import Lean
import Veil.Base
import Veil.Frontend.DSL.Module.Syntax
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Action.Elaborators
import Veil.Frontend.DSL.State.SubState
import Veil.Frontend.DSL.Module.VCGen
import Veil.Core.Tools.Verifier.Server
import Veil.Core.Tools.Verifier.Results
import Veil.Core.UI.Verifier.VerificationResults
import Veil.Core.UI.Trace.TraceDisplay
import Veil.Core.Tools.ModelChecker.Concrete.Checker
import Veil.Frontend.DSL.Action.Extract2
import Veil.Frontend.DSL.Module.Util.Enumeration
import Veil.Util.Multiprocessing
import Veil.Frontend.DSL.Module.AssertionInfo

open Lean Parser Elab Command

namespace Veil

private def overrideLeanDefaults : CommandElabM Unit := do
  -- FIXME: make this go through `elabVeilCommand` so it shows up in desugaring
  for (name, value) in veilDefaultOptions do
    modifyScope fun scope => { scope with opts := scope.opts.insert name value }

@[command_elab Veil.moduleDeclaration]
def elabModuleDeclaration : CommandElab := fun stx => do
  match stx with
  | `(veil module $modName:ident) => do
    overrideLeanDefaults
    let genv ← globalEnv.get
    let name := modName.getId
    let lenv ← localEnv.get
    if let some mod := lenv.currentModule then
      throwError s!"Module {mod.name} is already open, but you are now trying to open module {name}. Nested modules are not supported!"
    elabVeilCommand $ ← `(namespace $modName)
    if genv.containsModule name then
      logInfo "Module {name} has been previously defined. Importing it here."
      let mod := genv.modules[name]!
      localEnv.modifyModule (fun _ => mod)
    else
      let mod ← Module.freshWithName name
      localEnv.modifyModule (fun _ => mod)
  | _ => throwUnsupportedSyntax

@[command_elab Veil.typeDeclaration]
def elabTypeDeclaration : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare a type outside of a Veil module!")
  mod.throwIfStateAlreadyDefined
  match stx with
  | `(type $id:ident) => do
      let mod ← mod.declareUninterpretedSort id.getId stx
      localEnv.modifyModule (fun _ => mod)
  | _ => throwUnsupportedSyntax

@[command_elab Veil.stateComponentDeclaration]
def elabStateComponent : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare a state component outside of a Veil module!")
  mod.throwIfStateAlreadyDefined
  let new_mod : Module ← match stx with
  | `($mutab:stateMutability ? $kind:stateComponentKind $name:ident $br:bracketedBinder* : $dom:term) =>
    defineStateComponentFromSyntax mod mutab kind name br dom stx
  | `(command|$mutab:stateMutability ? relation $name:ident $br:bracketedBinder*) => do
    defineStateComponentFromSyntax mod mutab (← `(stateComponentKind|relation)) name br (← `(term|$(mkIdent ``Bool))) stx
  | _ => throwUnsupportedSyntax
  localEnv.modifyModule (fun _ => new_mod)
where
  defineStateComponentFromSyntax
  (mod : Module) (mutability : Option (TSyntax `stateMutability)) (kind : TSyntax `stateComponentKind)
  (name : Ident) (br : TSyntaxArray ``Term.bracketedBinder) (dom : Term) (userStx : Syntax) : CommandElabM Module := do
    let mutability := Mutability.fromStx mutability
    let kind := StateComponentKind.fromStx kind
    let sctype ← (
      if br.isEmpty then
        return StateComponentType.simple (← `(Command.structSimpleBinder|$name:ident : $dom))
      else
        return StateComponentType.complex br dom)
    let sc : StateComponent := { mutability := mutability, kind := kind, name := name.getId, «type» := sctype, userSyntax := userStx }
    Module.declareStateComponent mod sc

@[command_elab Veil.instanceDeclaration]
def elabInstantiate : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot instantiate a typeclass outside of a Veil module!")
  mod.throwIfStateAlreadyDefined
  let new_mod : Module ← match stx with
  | `(instantiate $inst:ident : $tp:term) => do
    let param : Parameter := { kind := .moduleTypeclass .userDefined, name := inst.getId, «type» := tp, userSyntax := stx }
    pure { mod with parameters := mod.parameters.push param }
  | _ => throwUnsupportedSyntax
  localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.enumDeclaration]
def elabEnumDeclaration : CommandElab := fun stx => do
  match stx with
  | `(enum $id:ident = { $[$elems:ident],* }) => do
    -- Declare the enum sort (using .enumSort instead of .uninterpretedSort)
    let mod ← getCurrentModule (errMsg := "You cannot declare an enum outside of a Veil module!")
    mod.throwIfStateAlreadyDefined
    let mod ← mod.declareUninterpretedSort id.getId stx .enumSort
    localEnv.modifyModule (fun _ => mod)
    -- Declare an axiomatisation class for the enum type
    let (class_name, class_decl) ← mkEnumAxiomatisation id elems
    elabVeilCommand class_decl
    -- Declare the concrete type and show it satisfies the axiomatisation
    for cmd in (← mkEnumConcreteType id elems) do
      elabVeilCommand cmd
    -- Add the enum to the Veil DSL environment
    let instanceV ← `(command|instantiate $(Ident.toEnumInst id) : @$class_name $id)
    trace[veil.debug] "Elaborated enum instance: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic instanceV}"
    elabVeilCommand instanceV
    elabVeilCommand $ ← `(open $class_name:ident)
  | _ => throwUnsupportedSyntax

 /-- Instruct the linter to not mark state variables as unused in our
  `after_init` and `action` definitions. -/
private def generateIgnoreFn (mod : Module) : CommandElabM Unit := do
  let cmd ← Command.runTermElabM fun _ => do
    let fnIdents ← mod.mutableComponents.mapM (fun sc => `($(quote sc.name)))
    let namesArrStx ← `(#[$[$fnIdents],*])
    let id := mkIdent `id
    let fnStx ← `(fun $id $(mkIdent `stack) _ => $(mkIdent ``Array.contains) ($namesArrStx) ($(mkIdent ``Lean.Syntax.getId) $id) /-&& isActionSyntax stack-/)
    let nm := mkIdent `ignoreStateFields
    let ignoreFnStx ← `(@[$(mkIdent `unused_variables_ignore_fn):ident] def $nm : $(mkIdent ``Lean.Linter.IgnoreFunction) := $fnStx)
    return ignoreFnStx
  elabVeilCommand cmd


@[command_elab Veil.inlineBuiltinDeclaration]
def elabInlineBuiltinDeclaration : CommandElab := fun stx => do
  match stx with
  | `(@[veil_decl] structure $name:ident $[$args]* where $[$fields]*) => do
    elabCommand (← `(structure $name:ident $[$args]* where $[$fields]*))
    tryDerivingInstances name stx
  | `(@[veil_decl] inductive $name:ident $[$args]* where $[$ctors]*) => do
    elabCommand (← `(inductive $name:ident $[$args]* where $[$ctors]*))
    tryDerivingInstances name stx
  | `(@[veil_decl] inductive $name:ident $[$args]* $[$ctors:ctor]*) => do
    elabCommand (← `(inductive $name:ident $[$args]* $[$ctors:ctor]*))
    tryDerivingInstances name stx
  | _ => throwUnsupportedSyntax
where
  /-- Try to derive instances, suppressing errors and showing warnings instead -/
  tryDerivingInstances (name : Ident) (_origStx : Syntax) : CommandElabM Unit := do
    for className in defaultDerivingClasses do
      let classIdent := Lean.mkIdent className
      try elabVeilCommand $ ← `(command| deriving instance $classIdent:ident for $name:ident)
      catch _ => logWarning m!"Could not automatically derive {className} for {name.getId}. You may need to provide a manual instance."
  defaultDerivingClasses : List Name := [
    ``Inhabited, ``DecidableEq, ``Lean.ToJson,
    ``Hashable, ``Ord, ``Repr,
    ``Std.TransOrd, ``Std.LawfulEqOrd,
    -- ``Veil.Enumeration
]

/-- Crystallizes the state of the module, i.e. it defines it as a Lean
`structure` definition, if that hasn't already happened. -/
private def Module.ensureStateIsDefined (mod : Module) : CommandElabM Module := do
  if mod.isStateDefined then
    return mod
  let (mod, stateStxs) ← do (if mod._useFieldRepTC then do
      let (mod, fieldStxs) ← mod.declareStateFieldLabelTypeAndDispatchers
      let (mod, stateStxs) ← mod.declareFieldsAbstractedStateStructure
      return (mod, fieldStxs ++ stateStxs)
    else mod.declareStateStructure)
  let (mod, theoryStxs) ← mod.declareTheoryStructure
  let instantiationStx ← mod.mkInstantiationStructure
  for stx in stateStxs ++ theoryStxs ++ #[instantiationStx] do
    elabVeilCommand stx
  generateIgnoreFn mod
  let mod := { mod with _stateDefined := true }
  if mod._useLocalRPropTC then
    let (localRPropTCStx, stx2) ← liftTermElabM mod.declareLocalRPropTC
    elabVeilCommand localRPropTCStx
    elabVeilCommand stx2
  pure mod

/-- Crystallizes the specification of the module, i.e. it finalizes the
set of `procedures` and `assertions`. -/
private def Module.ensureSpecIsFinalized (mod : Module) : CommandElabM Module := do
  if mod.isSpecFinalized then
    return mod
  let mod ← mod.ensureStateIsDefined
  let (assumptionCmd, mod) ← mod.assembleAssumptions
  elabVeilCommand assumptionCmd
  let (invariantCmd, mod) ← mod.assembleInvariants
  trace[veil.debug] s!"Elaborating invariants: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic invariantCmd}"
  elabVeilCommand invariantCmd
  let (safetyCmd, mod) ← mod.assembleSafeties
  trace[veil.debug] s!"Elaborating safeties: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic safetyCmd}"
  elabVeilCommand safetyCmd
  let (labelCmds, mod) ← mod.assembleLabel
  for cmd in labelCmds do
    elabVeilCommand cmd

  -- Generate ActionTag type for symbolic model checking
  -- NOTE: ActionTag is query-local (not a module sort), but we generate the
  -- axiomatisation class and concrete type here for convenience
  let actionNames := mod.actions.map (fun (a : ProcedureSpecification) => Lean.mkIdent a.name)
  if !actionNames.isEmpty then
    let (className, classDecl) ← mkEnumAxiomatisation actionTagType actionNames
    elabVeilCommand classDecl
    for cmd in (← mkEnumConcreteType actionTagType actionNames) do
      elabVeilCommand cmd
    elabVeilCommand $ ← `(open $className:ident)
    -- TODO: Generate equivalence lemma (ActionTag.label_equiv) here

  let (nextCmd, mod) ← mod.assembleNext
  elabVeilCommand nextCmd
  let (nextTrCmd, mod) ← mod.assembleNextTransition
  elabVeilCommand nextTrCmd
  let (initCmd, mod) ← mod.assembleInit
  elabVeilCommand initCmd
  Extract.genNextActCommands mod (if mod._useNewExtraction then Extract.genExtractCommand2 else Extract.genExtractCommand)
  elabVeilCommand (← Extract.Module.assembleEnumerableTransitionSystem mod)
  let (rtsCmd, mod) ← Module.assembleRelationalTransitionSystem mod
  elabVeilCommand rtsCmd
  Verifier.runManager
  mod.generateVCs
  return { mod with _specFinalized := true }

open Lean.Meta.Tactic.TryThis in
@[command_elab Veil.checkInvariants]
def elabCheckInvariants : CommandElab := fun stx => do
  -- Skip in compilation mode (no verification feedback needed)
  if ← isModelCheckCompileMode then return
  let mod ← getCurrentModule (errMsg := "You cannot #check_invariant outside of a Veil module!")
  let _ ← mod.ensureSpecIsFinalized
  Verifier.startAll
  -- Display suggestions if the command is `#check_invariants?`
  match stx with
  | `(command|#check_invariants?) => do
    Verifier.vcManager.atomically (fun ref => do
      let mgr ← ref.get
      let cmds ← liftCoreM <| constructCommands (← mgr.theorems)
      liftCoreM <| addSuggestion stx cmds)
  | `(command|#check_invariants!) => do
    Verifier.displayStreamingResults stx getResults
    Verifier.vcManager.atomicallyOnce frontendNotification
      (fun ref => do let mgr ← ref.get; return mgr.isDone)
      (fun ref => do
        let mgr ← ref.get
        let cmds ← liftCoreM <| constructCommands (← mgr.undischargedTheorems)
        liftCoreM <| addSuggestion stx cmds)
  | `(command|#check_invariants) => do
    Verifier.displayStreamingResults stx getResults
    -- Verifier.vcManager.atomicallyOnce frontendNotification
      -- (fun ref => do let mgr ← ref.get; return mgr.isDone)
      -- (fun ref => do let mgr ← ref.get; logInfo m!"{mgr}"; logInfo m!"{Lean.toJson (← mgr.toVerificationResults)}")
  | _ => logInfo "Unsupported syntax {stx}"; throwUnsupportedSyntax
  where
  getResults : CoreM (VerificationResults VCMetadata SmtResult × Verifier.StreamingStatus) := do
    Verifier.vcManager.atomically
      (fun ref => do
        let mgr ← ref.get
        let results ← mgr.toVerificationResults
        let isDone := mgr.isDone
        return (results, if isDone then .done else .running))


@[command_elab Veil.genState]
def elabGenState : CommandElab := fun _stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot #gen_state outside of a Veil module!")
  mod.throwIfStateAlreadyDefined ; mod.throwIfSpecAlreadyFinalized
  mod ← mod.ensureStateIsDefined
  localEnv.modifyModule (fun _ => mod)

@[command_elab Veil.initializerDefinition]
def elabInitializer : CommandElab := fun stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot elaborate an initializer outside of a Veil module!")
  mod ← mod.ensureStateIsDefined
  mod.throwIfSpecAlreadyFinalized
  let new_mod ← match stx with
  | `(command|after_init {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.initializer) .none .none l stx
  | _ => throwUnsupportedSyntax
  localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.procedureDefinition]
def elabProcedure : CommandElab := fun stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot elaborate an action outside of a Veil module!")
  mod ← mod.ensureStateIsDefined
  mod.throwIfSpecAlreadyFinalized
  let new_mod ← match stx with
  | `(command|action $nm:ident $br:explicitBinders ? {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.action nm.getId) br .none l stx
  | `(command|procedure $nm:ident $br:explicitBinders ? {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.procedure nm.getId) br .none l stx
  | _ => throwUnsupportedSyntax
  localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.transitionDefinition]
def elabTransition : CommandElab := fun stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot elaborate a transition outside of a Veil module!")
  mod ← mod.ensureStateIsDefined
  mod.throwIfSpecAlreadyFinalized
  let new_mod ← match stx with
  | `(command|transition $nm:ident $br:explicitBinders ? { $t:term }) =>
    -- check immutability of changed fields
    let changedFn (f : Name) := t.raw.find? (·.getId == f.appendAfter "'") |>.isSome
    let fields ← mod.getFieldsRecursively
    let (changedFields, unchangedFields) := fields.partition changedFn
    for f in changedFields do
      mod.throwIfImmutable f (isTransition := true)
    -- obtain the "real" transition term
    let trStx ← do
      let (th, st, st') := (mkIdent `th, mkIdent `st, mkIdent `st')
      let unchangedFields := unchangedFields.map Lean.mkIdent
      let tmp ← liftTermElabM <| mod.withTheoryAndStateTermTemplate [(.theory, th), (.state .none "conc", st), (.state "'" "conc'", st')]
        (fun _ _ => `([unchanged|"'"| $unchangedFields*] ∧ ($t)))
      `(term| (fun ($th : $environmentTheory) ($st $st' : $environmentState) => $tmp))
    mod.defineTransition (ProcedureInfo.action nm.getId (definedViaTransition := true)) br trStx stx
    -- FIXME: Is this required?
    -- -- warn if this is not first-order
    -- Command.liftTermElabM $ warnIfNotFirstOrder nm.getId
  | _ => throwUnsupportedSyntax
  localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.procedureDefinitionWithSpec]
def elabProcedureWithSpec : CommandElab := fun stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot elaborate an action outside of a Veil module!")
  mod ← mod.ensureStateIsDefined
  mod.throwIfSpecAlreadyFinalized
  let new_mod ← match stx with
  | `(command|action $nm:ident $br:explicitBinders ? $spec:doSeq {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.action nm.getId) br spec l stx
  | `(command|procedure $nm:ident $br:explicitBinders ? $spec:doSeq {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.procedure nm.getId) br spec l stx
  | _ => throwUnsupportedSyntax
  localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.ghostRelationDefinition]
def elabGhostRelationDefinition : CommandElab := fun stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot elaborate a ghost relation outside of a Veil module!")
  mod ← mod.ensureStateIsDefined
  mod.throwIfSpecAlreadyFinalized
  let (nm, stateGhost?, (cmd, new_mod)) ← match stx with
  | `(command|ghost relation $nm:ident $br:explicitBinders ? := $t:term) => pure (nm.getId, true, ← mod.defineGhostRelation nm.getId br t (justTheory := false))
  | `(command|theory ghost relation $nm:ident $br:explicitBinders ? := $t:term) => pure (nm.getId, false, ← mod.defineGhostRelation nm.getId br t (justTheory := true))
  | _ => throwUnsupportedSyntax
  elabVeilCommand cmd
  if mod._useLocalRPropTC && stateGhost? then liftTermElabM $ new_mod.proveLocalityForStatePredicate nm stx
  localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.assertionDeclaration]
def elabAssertion : CommandElab := fun stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  mod ← mod.ensureStateIsDefined
  mod.throwIfSpecAlreadyFinalized
  -- TODO: handle assertion sets correctly
  let assertion : StateAssertion ← match stx with
  | `(command|assumption $name:propertyName ? $prop:term) => mod.mkAssertion .assumption name prop stx
  | `(command|invariant $name:propertyName ? $prop:term) => mod.mkAssertion .invariant name prop stx
  | `(command|safety $name:propertyName ? $prop:term) => mod.mkAssertion .safety name prop stx
  | `(command|trusted invariant $name:propertyName ? $prop:term) => mod.mkAssertion .trustedInvariant name prop stx
  | `(command|termination $name:propertyName ? $prop:term) => mod.mkAssertion .termination name prop stx
  | _ => throwUnsupportedSyntax
  -- Elaborate the assertion in the Lean environment
  let (cmd, mod') ← mod.defineAssertion assertion
  elabVeilCommand cmd
--   dbg_trace s!"Elaborated assertion: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic stx}"
  if mod._useLocalRPropTC && (assertion.kind matches .invariant || assertion.kind matches .safety) then liftTermElabM $ mod'.proveLocalityForStatePredicate assertion.name stx
  localEnv.modifyModule (fun _ => mod')

@[command_elab Veil.genSpec]
def elabGenSpec : CommandElab := fun _stx => do
  let mod ← getCurrentModule (errMsg := "You cannot elaborate a specification outside of a Veil module!")
  let mod ← mod.ensureSpecIsFinalized
  localEnv.modifyModule (fun _ => mod)
  -- Run doesNotThrow VCs asynchronously and log errors at assertion locations when done
  Verifier.runFilteredAsync Verifier.isDoesNotThrow logDoesNotThrowErrors

open Lean Meta Elab Command Veil in
/-- Developer tool. Import all module parameters into section scope. -/
elab "veil_variables" : command => do
  let mod ← getCurrentModule
  let binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ← mod.parameters.mapM (·.binder)
  for binder in binders do
    match binder with
    | `(bracketedBinder| ($id:ident : $ty:term) )
    | `(bracketedBinder| [$id:ident : $ty:term] )
      =>
      let varId := id.getId
      trace[veil.debug] s!"{varId} :  {← liftTermElabM <| Lean.PrettyPrinter.formatTerm ty}"
    | _ => throwError "unsupported veil_variables binder syntax"
    let varUIds ← (← getBracketedBinderIds binder) |>.mapM (withFreshMacroScope ∘ MonadQuotation.addMacroScope)
    trace[veil.debug] s!"with unique IDs: {varUIds}"
    modifyScope fun scope => { scope with varDecls := scope.varDecls.push binder, varUIds := scope.varUIds ++ varUIds}

/-- Configuration options for the `#model_check` command. -/
structure ModelCheckerConfig where
  /-- Maximum depth (number of transitions) to explore. If it's 0, explores all
  reachable states. -/
  maxDepth : Nat := 0
  /-- If true, run the model checker sequentially (no parallelization). -/
  sequential : Bool := false
  /-- Parallel configuration. Only used if `sequential` is false. -/
  parallelCfg : Option ModelChecker.ParallelConfig := none
  deriving Repr

/-- Default threshold for parallelizing model checking subtasks. -/
def defaultThresholdToParallel : Nat := 20

declare_command_config_elab elabModelCheckerConfig ModelCheckerConfig

@[command_elab Veil.modelCheck]
def elabModelCheck : CommandElab := fun stx => do
  match stx with
  | `(#model_check%$tk $[after_compilation%$compile?]? $instTerm:term $[$theoryTermOpt]? $cfg:optConfig) =>
    let mod ← getCurrentModule (errMsg := "You cannot #model_check outside of a Veil module!")
    let mod ← mod.ensureSpecIsFinalized
    localEnv.modifyModule (fun _ => mod)

    let theoryTerm ← getTheoryTerm theoryTermOpt mod instTerm compile?.isSome

    warnAboutTransitions mod
    let config ← elabModelCheckerConfig cfg
    -- Resolve parallelCfg: sequential flag takes precedence, otherwise default to parallel
    let parallelCfg ← match config.sequential, config.parallelCfg with
      | true, _ => pure none
      | false, some cfg => pure (some cfg)
      | false, none => pure (some { numSubTasks := ← getNumCores, thresholdToParallel := defaultThresholdToParallel })
    let config := { config with parallelCfg := parallelCfg }
    let callExpr ← mkModelCheckerCall mod config instTerm theoryTerm

    -- Dispatch based on compilation mode (set via option) and after_compilation flag
    let isCompileMode ← isModelCheckCompileMode
    match isCompileMode, compile?.isSome with
    | true, _      => elabModelCheckInternalMode mod callExpr  -- In compiled binary
    | false, false => elabModelCheckInterpretedMode stx callExpr parallelCfg
    | false, true  => elabModelCheckCompiledMode tk stx parallelCfg
  | _ => throwUnsupportedSyntax
where
  /-- Get the theory term, defaulting to `{}` if not provided and there are no theory fields.
      Throws a helpful error if theory fields exist but no term was provided. -/
  getTheoryTerm (theoryTermOpt : Option Term) (mod : Module) (instTerm : Term)
      (isCompile : Bool) : CommandElabM Term := do
    match theoryTermOpt with
    | some t => pure t
    | none =>
      unless mod.immutableComponents.isEmpty do
        let fieldStrs := mod.immutableComponents.map (fun c => s!"{c.name} := ...")
        let theoryExample := "{ " ++ ", ".intercalate fieldStrs.toList ++ " }"
        let compileStr := if isCompile then "after_compilation " else ""
        throwError "This module has immutable fields, so you must specify the theory instantiation:\n\
          #model_check {compileStr}{instTerm} {theoryExample}"
      `({})

  /-- Generate the model source for compilation:
      1. Insert `set_option veil.__modelCheckCompileMode true` after imports
      2. Keep everything up to and including `#gen_spec`
      3. Append the current `#model_check` command
      This filters out `#check_invariants`, `sat trace`, etc. from the compiled model. -/
  generateModelSource (_tk stx : Syntax) : CommandElabM String := do
    let src := (← getFileMap).source
    let afterImportsPos := ModelChecker.Compilation.findPosAfterImports src
    let compileModePreamble := "\nset_option veil.__modelCheckCompileMode true\n"
    -- Find #gen_spec and take everything up to and including it
    let genSpecEnd := ModelChecker.Compilation.findGenSpecEnd src
    let beforeImports := String.Pos.Raw.extract src 0 afterImportsPos
    let afterImportsToGenSpec := String.Pos.Raw.extract src afterImportsPos genSpecEnd
    let some modelCheckStart := stx.getPos? | throwError "Unexpected error: #model_check has no position"
    let some modelCheckEnd := stx.getTailPos? | throwError "Unexpected error: #model_check has no end position"
    let modelCheckCmd := String.Pos.Raw.extract src modelCheckStart modelCheckEnd
    return beforeImports ++ compileModePreamble ++ afterImportsToGenSpec ++ "\n" ++ modelCheckCmd ++ "\n"

  /-- Prepend `name` with `mod.name`. Useful when expressions are printed out for debugging. -/
  mkIdentWithModName (mod : Module) (name : Name) : Ident :=
    Lean.mkIdent (mod.name ++ name)

  /-- Display a TraceDisplayViewer widget with the given result term. -/
  displayResultWidget (stx : Syntax) (resultTerm : Term) : CommandElabM Unit := do
    let widgetExpr ← `(open ProofWidgets.Jsx in
      <ProofWidgets.TraceDisplayViewer result={$resultTerm} layout={"vertical"} />)
    let html ← ← liftTermElabM <| ProofWidgets.HtmlCommand.evalCommandMHtml <| ← ``(ProofWidgets.HtmlEval.eval $widgetExpr)
    liftCoreM <| Widget.savePanelWidgetInfo
      (hash ProofWidgets.HtmlDisplayPanel.javascript)
      (return json% { html: $(← Server.rpcEncode html) }) stx

  mkSearchParameters (mod : Module) (config : ModelCheckerConfig) : CommandElabM Term := do
    -- Build SafetyProperty.mk syntax for a StateAssertion
    let mkProp (sa : StateAssertion) : CommandElabM Term :=
      `($(mkIdent ``Veil.ModelChecker.SafetyProperty.mk)
          ($(mkIdent `name) := $(quote sa.name))
          ($(mkIdent `property) := fun $(mkIdent `th) $(mkIdent `st) => $(mkIdentWithModName mod sa.name) $(mkIdent `th) $(mkIdent `st)))
    let safetyList ← `([$((← mod.invariants.mapM mkProp)),*])
    let terminatingProp ← match mod.terminations[0]? with
      | some t => mkProp t
      | none => `($(mkIdent `default))
    let earlyTermConds ← do
      let base ← `([$(mkIdent ``Veil.ModelChecker.EarlyTerminationCondition.foundViolatingState)])
      if config.maxDepth > 0 then `($base ++ [$(mkIdent ``Veil.ModelChecker.EarlyTerminationCondition.reachedDepthBound) $(quote config.maxDepth)])
      else pure base
    `({ $(mkIdent `invariants) := $safetyList, $(mkIdent `terminating) := $terminatingProp,
        $(mkIdent `earlyTerminationConditions) := $earlyTermConds })

  /-- Build the core model checker call syntax (without parallel config). -/
  mkModelCheckerCall (mod : Module) (config : ModelCheckerConfig)
      (instTerm theoryTerm : Term) : CommandElabM Term := do
    let inst := mkVeilImplementationDetailIdent `inst
    let th := mkVeilImplementationDetailIdent `th
    let instSortArgs ← (← mod.sortIdents).mapM fun sortIdent => `($inst.$(sortIdent))
    let sp ← mkSearchParameters mod config
    -- Model checker call with type annotation to help inference
    -- Note: findReachable takes parallelCfg and progressInstanceId as the last two args
    `((let $inst : $instantiationType := $instTerm
       let $th : $theoryIdent $instSortArgs* := $theoryTerm
       $(mkIdent ``Veil.ModelChecker.Concrete.findReachable)
         ($(mkIdentWithModName mod `enumerableTransitionSystem) $instSortArgs* $th)
         $sp : _ → _ → IO _))

  /-- Warn if the module contains transitions (which are slow to model check). -/
  warnAboutTransitions (mod : Module) : CommandElabM Unit := do
    let transitions := mod.procedures.filter (·.info.isTransition)
    if transitions.isEmpty then return
    let names := ", ".intercalate (transitions.map (·.info.name.toString) |>.toList)
    logWarning m!"Explicit state model checking of transitions is SLOW!\n\n\
      The current implementation enumerates all possible states and filters those satisfying \
      the transition relation. Your specification has {transitions.size} \
      transition{if transitions.size > 1 then "s" else ""}: {names}\n\n\
      Consider encoding transitions as imperative actions where possible."

  /-- Read stderr lines from a subprocess and update progress refs until EOF. -/
  readStderrProgress (stderr : IO.FS.Handle) (instanceId : Nat) : IO Unit := do
    repeat do
      let line ← stderr.getLine
      if line.isEmpty then break
      if let .ok json := Json.parse line then
        if let .ok (p : ModelChecker.Concrete.Progress) := FromJson.fromJson? json then
          if let some refs ← ModelChecker.Concrete.getProgressRefs instanceId then
            refs.progressRef.set p

  /-- Handle internal mode: define and export the model checker result. -/
  elabModelCheckInternalMode (mod : Module) (callExpr : Term) : CommandElabM Unit := do
    elabVeilCommand (← `(def $(mkIdent `modelCheckerResult) (pcfg : Option Veil.ModelChecker.ParallelConfig) (progressInstanceId : Nat) := $callExpr pcfg progressInstanceId))
    elabVeilCommand (← `(end $(mkIdent mod.name)))
    elabVeilCommand (← `(export $(mkIdent mod.name) ($(mkIdent `modelCheckerResult))))

  /-- Run lake build and check if compilation was interrupted.
      Returns `true` if compilation succeeded and wasn't interrupted. -/
  runCompilationStep (sourceFile : String) (buildFolder : System.FilePath) (instanceId : Nat) : IO Bool := do
    let result ← ModelChecker.Compilation.runProcessWithStatus sourceFile
      { cmd := "lake", args := #["build", "ModelCheckerMain"], cwd := buildFolder }
      instanceId "Compiling"
    -- Check if compilation was interrupted
    if result.interrupted then
      return false
    -- Check if compilation failed
    if result.exitCode != 0 then
      let errorMsg := s!"Compilation failed (exit code {result.exitCode}):\n" ++
        (if result.stderr.isEmpty then "" else s!"[stderr]\n{result.stderr}") ++
        (if result.stdout.isEmpty then "" else s!"[stdout]\n{result.stdout}\n")
      ModelChecker.Concrete.finishProgress instanceId (Json.mkObj [
        ("error", Json.str errorMsg)])
      return false
    -- Mark compilation as finished
    ModelChecker.Compilation.stillCurrentCont sourceFile instanceId fun ref => do
      ref.modify fun registry => registry.insert sourceFile (.finished buildFolder)

  /-- Check if the compiled binary exists.
      Returns `some binPath` if it exists, `none` otherwise (after reporting error). -/
  verifyBinaryExists (buildFolder : System.FilePath) (instanceId : Nat) : IO (Option System.FilePath) := do
    let binPath := buildFolder / ".lake" / "build" / "bin"
    if ← (binPath / "ModelCheckerMain").pathExists then
      return some binPath
    else
      ModelChecker.Concrete.finishProgress instanceId (Json.mkObj [
        ("error", Json.str s!"ModelCheckerMain binary not found at {binPath}. Compilation may have failed.")])
      return none

  /-- Run the model checker binary and return its stdout output. -/
  runModelCheckerBinary (binPath : System.FilePath)
      (parallelCfg : Option ModelChecker.ParallelConfig) (instanceId : Nat) : IO String := do
    ModelChecker.Concrete.updateStatus instanceId "Running..."
    let args := parallelCfg.map (fun p => #[toString p.numSubTasks, toString p.thresholdToParallel]) |>.getD #[]
    let child ← IO.Process.spawn {
      cmd := toString (binPath / "ModelCheckerMain"), args,
      stdin := .piped, stdout := .piped, stderr := .piped }
    readStderrProgress child.stderr instanceId
    let stdout ← IO.FS.Handle.readToEnd child.stdout
    let _ ← child.wait
    return stdout

  /-- Handle compiled mode: build, run, and display results with streaming progress. -/
  elabModelCheckCompiledMode (tk stx : Syntax) (parallelCfg : Option ModelChecker.ParallelConfig) : CommandElabM Unit := do
    let instanceId ← ModelChecker.Concrete.allocProgressInstance
    let assertionSources := extractAssertionSources (← globalEnv.get).assertions (← getFileMap)
    let sourceFile ← getFileName
    let buildFolder ← do
      let modelSource ← generateModelSource tk stx
      ModelChecker.Compilation.createBuildFolder sourceFile modelSource
    ModelChecker.Compilation.compilationRegistry.atomically fun ref => do
      ref.modify fun registry => registry.insert sourceFile (.inProgress instanceId buildFolder)
    let _ ← IO.asTask (prio := .dedicated) do
      unless (← runCompilationStep sourceFile buildFolder instanceId) do return
      let some binPath ← verifyBinaryExists buildFolder instanceId | return
      let stdout ← runModelCheckerBinary binPath parallelCfg instanceId
      let json := Json.parse stdout |>.toOption.getD .null
      let enrichedJson := enrichJsonWithAssertions json assertionSources
      ModelChecker.Concrete.finishProgress instanceId enrichedJson
    ModelChecker.displayStreamingProgress stx instanceId

  /-- Handle interpreted mode: evaluate and display results directly. -/
  elabModelCheckInterpretedMode (stx : Syntax) (callExpr : Term)
      (parallelCfg : Option ModelChecker.ParallelConfig) : CommandElabM Unit := do
    -- Allocate a unique progress instance ID before starting the task
    let instanceId ← ModelChecker.Concrete.allocProgressInstance
    -- Extract assertion sources before starting the task (needs elaboration context)
    let assertionSources := extractAssertionSources (← globalEnv.get).assertions (← getFileMap)
    let resultExpr ← `(Lean.toJson <$> $callExpr ($(quote parallelCfg)) ($(quote instanceId)))
    trace[veil.desugar] "{resultExpr}"
    -- Elaborate and get the IO computation (must be done synchronously)
    let ioComputation ← liftTermElabM do
      let expr ← Term.elabTerm resultExpr none
      Term.synthesizeSyntheticMVarsNoPostponing
      let expr ← instantiateMVars expr
      unsafe Meta.evalExpr (IO Lean.Json) (mkApp (mkConst ``IO) (mkConst ``Lean.Json)) expr
    -- Start the IO computation in a background task
    let _ ← IO.asTask (prio := .dedicated) do
      let json ← IO.ofExcept (← ioComputation.toIO')
      -- Enrich JSON with assertion source info for any assertion failures
      let enrichedJson := enrichJsonWithAssertions json assertionSources
      IO.eprintln s!"{enrichedJson}"
      -- Mark progress as complete and store result JSON
      ModelChecker.Concrete.finishProgress instanceId enrichedJson
    -- Display streaming progress widget with the same instance ID
    ModelChecker.displayStreamingProgress stx instanceId

end Veil
