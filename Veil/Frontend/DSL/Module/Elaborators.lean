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

/-- Extract the name identifier from a Veil procedure/transition/ghost syntax.
    Returns `unknown if the syntax doesn't match any known pattern. -/
def extractDefinitionName (stx : Syntax) : Name :=
  match stx with
  -- procedureDefinition (without spec)
  | `(command|action $nm:ident $_br:explicitBinders ? {$_l:doSeq}) => nm.getId
  | `(command|procedure $nm:ident $_br:explicitBinders ? {$_l:doSeq}) => nm.getId
  -- procedureDefinitionWithSpec
  | `(command|action $nm:ident $_br:explicitBinders ? $_spec:doSeq {$_l:doSeq}) => nm.getId
  | `(command|procedure $nm:ident $_br:explicitBinders ? $_spec:doSeq {$_l:doSeq}) => nm.getId
  -- transitionDefinition
  | `(command|transition $nm:ident $_br:explicitBinders ? { $_t:term }) => nm.getId
  -- ghostRelationDefinition
  | `(command|ghost relation $nm:ident $_br:explicitBinders ? := $_t:term) => nm.getId
  | `(command|theory ghost relation $nm:ident $_br:explicitBinders ? := $_t:term) => nm.getId
  | _ => `unknown

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

/-- Check if the syntax stack contains a Veil procedure context.
    Returns true if we're inside an `after_init`, `action`, `procedure`, or `transition` block. -/
def isVeilProcedureContext (stack : Syntax.Stack) : Bool :=
  stack.any fun (s, _) =>
    s.isOfKind `Veil.initializerDefinition ||
    s.isOfKind `Veil.procedureDefinition ||
    s.isOfKind `Veil.procedureDefinitionWithSpec ||
    s.isOfKind `Veil.transitionDefinition

/-- Instruct the linter to not mark state variables as unused in our
  `after_init` and `action` definitions. Also ignores capitalized identifiers
  (universally quantified variables) in Veil procedure contexts. -/
private def generateIgnoreFn (mod : Module) : CommandElabM Unit := do
  let cmd ← Command.runTermElabM fun _ => do
    let fnIdents ← mod.mutableComponents.mapM (fun sc => `($(quote sc.name)))
    let namesArrStx ← `(#[$[$fnIdents],*])
    let id := mkIdent `id
    let stack := mkIdent `stack
    -- Ignore if:
    -- 1. The identifier is a state component name (existing behavior), OR
    -- 2. The identifier is capitalized (universally quantified) AND we're in a Veil procedure context
    let fnStx ← `(fun $id $stack _ =>
      $(mkIdent ``Array.contains) ($namesArrStx) ($(mkIdent ``Lean.Syntax.getId) $id) ||
      ($(mkIdent ``Veil.isCapital) ($(mkIdent ``Lean.Syntax.getId) $id) && $(mkIdent ``Veil.isVeilProcedureContext) $stack))
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

private def warnIfNoInvariantsDefined (mod : Module) : CommandElabM Unit := do
  if mod.invariants.isEmpty then
    logWarning "you have not defined any invariants for this specification; did you forget?"

private def warnIfNoActionsDefined (mod : Module) : CommandElabM Unit := do
  if mod.actions.isEmpty then
    logWarning "you have not defined any actions for this specification; did you forget?"

/-- Crystallizes the specification of the module, i.e. it finalizes the set of
`procedures` and `assertions`. The `stx` parameter is the syntax of the command
that triggered the finalization; it is stored for use by `#model_check` when
generating compiled model source. -/
def Module.ensureSpecIsFinalized (mod : Module) (stx : Syntax) : CommandElabM Module := do
  if mod.isSpecFinalized then
    return mod
  let mod ← mod.ensureStateIsDefined
  warnIfNoInvariantsDefined mod
  warnIfNoActionsDefined mod
  let mod ← withTraceNode `veil.perf.elaborator.decl.Assumptions (fun _ => return "Assumptions") do
    let (assumptionCmd, mod) ← mod.assembleAssumptions
    elabVeilCommand assumptionCmd
    return mod
  let mod ← withTraceNode `veil.perf.elaborator.decl.Invariants (fun _ => return "Invariants") do
    let (invariantCmd, mod) ← mod.assembleInvariants
    trace[veil.debug] s!"Elaborating invariants: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic invariantCmd}"
    elabVeilCommand invariantCmd
    return mod
  let mod ← withTraceNode `veil.perf.elaborator.decl.Safeties (fun _ => return "Safeties") do
    let (safetyCmd, mod) ← mod.assembleSafeties
    trace[veil.debug] s!"Elaborating safeties: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic safetyCmd}"
    elabVeilCommand safetyCmd
    return mod
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
  mod.generateDoesNotThrowVCs
  -- Run doesNotThrow VCs asynchronously and log errors at assertion locations when done
  Verifier.runFilteredAsync Verifier.isDoesNotThrow logDoesNotThrowErrors
  mod.generateInvariantVCs
  -- The invariant VCs are started only when `#check_invariants` is run
  return { mod with _specFinalizedAt := some stx }

/-- Log verification results asynchronously after all VCs complete. -/
def logVerificationResults (stx : Syntax) (results : VerificationResults VCMetadata SmtResult) : CommandElabM Unit := do
  let msg ← Verifier.formatVerificationResults results
  let violationIsError := veil.violationIsError.get (← getOptions)
  if Verifier.hasFailedVCs results && violationIsError then
    veilLogErrorAt stx msg
  else
    unless ← isModelCheckCompileMode do
      logInfoAt stx msg

@[command_elab Veil.checkInvariants]
def elabCheckInvariants : CommandElab := fun stx => do
  -- Use dynamic trace class name for detailed profiling
  withTraceNode `veil.perf.elaborator.checkInvariants (fun _ => return "#check_invariants") do
    -- Skip in compilation mode (no verification feedback needed)
    if ← isModelCheckCompileMode then return
    let mod ← getCurrentModule (errMsg := "You cannot #check_invariant outside of a Veil module!")
    mod.throwIfSpecNotFinalized
    Verifier.runFilteredAsync VCMetadata.isInduction (logVerificationResults stx)
    Verifier.displayStreamingResults stx getResults
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
  -- Use dynamic trace class name for detailed profiling
  withTraceNode `veil.perf.elaborator.genState (fun _ => return "#gen_state") do
    let mut mod ← getCurrentModule (errMsg := "You cannot #gen_state outside of a Veil module!")
    mod.throwIfStateAlreadyDefined ; mod.throwIfSpecAlreadyFinalized
    mod ← mod.ensureStateIsDefined
    localEnv.modifyModule (fun _ => mod)

@[command_elab Veil.initializerDefinition]
def elabInitializer : CommandElab := fun stx => do
  -- Use dynamic trace class name for detailed profiling
  withTraceNode `veil.perf.elaborator.afterInit (fun _ => return "after_init") do
    let mut mod ← getCurrentModule (errMsg := "You cannot elaborate an initializer outside of a Veil module!")
    mod ← mod.ensureStateIsDefined
    mod.throwIfSpecAlreadyFinalized
    let new_mod ← match stx with
    | `(command|after_init {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.initializer) .none .none l stx
    | _ => throwUnsupportedSyntax
    localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.procedureDefinition]
def elabProcedure : CommandElab := fun stx => do
  let nm := extractDefinitionName stx
  -- Use dynamic trace class name that includes the action name
  withTraceNode (`veil.perf.elaborator.action ++ nm) (fun _ => return s!"action {nm}") do
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
  let nm := extractDefinitionName stx
  -- Use dynamic trace class name that includes the transition name
  withTraceNode (`veil.perf.elaborator.transition ++ nm) (fun _ => return s!"transition {nm}") do
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
  let nm := extractDefinitionName stx
  -- Use dynamic trace class name that includes the action name
  withTraceNode (`veil.perf.elaborator.actionWithSpec ++ nm) (fun _ => return s!"action+spec {nm}") do
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
  let nm := extractDefinitionName stx
  -- Use dynamic trace class name that includes the ghost relation name
  withTraceNode (`veil.perf.elaborator.ghostRelation ++ nm) (fun _ => return s!"ghost {nm}") do
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
  -- Use dynamic trace class name that includes the assertion name and kind
  let kindStr := match assertion.kind with
    | .assumption => "assumption"
    | .invariant => "invariant"
    | .safety => "safety"
    | .trustedInvariant => "trusted_invariant"
    | .termination => "termination"
  withTraceNode (`veil.perf.elaborator.assertion ++ assertion.name) (fun _ => return s!"{kindStr} {assertion.name}") do
    -- Elaborate the assertion in the Lean environment
    let (cmd, mod') ← mod.defineAssertion assertion
    elabVeilCommand cmd
  --   dbg_trace s!"Elaborated assertion: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic stx}"
    if mod._useLocalRPropTC && (assertion.kind matches .invariant || assertion.kind matches .safety) then liftTermElabM $ mod'.proveLocalityForStatePredicate assertion.name stx
    localEnv.modifyModule (fun _ => mod')

@[command_elab Veil.genSpec]
def elabGenSpec : CommandElab := fun stx => do
  -- Use dynamic trace class name for detailed profiling
  withTraceNode `veil.perf.elaborator.genSpec (fun _ => return "#gen_spec") do
    let mod ← getCurrentModule (errMsg := "You cannot elaborate a specification outside of a Veil module!")
    let mod ← mod.ensureSpecIsFinalized stx
    localEnv.modifyModule (fun _ => mod)

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

/-- Model checking mode: interpreted only, compiled only, or default (both with handoff). -/
inductive ModelCheckingMode where
  | interpreted
  | compiled
  | default
  deriving Repr, DecidableEq

/-- Context for model checking operations. Bundles common parameters to reduce duplication. -/
structure ModelCheckContext where
  mod : Module
  stx : Syntax
  instanceId : Nat
  cancelToken : IO.CancelToken
  assertionSources : Std.HashMap AssertionId AssertionSourceInfo
  parallelCfg : Option ModelChecker.ParallelConfig

/-- Extract the model checking mode from the optional mode syntax. -/
def getModelCheckingMode (modeStx : Syntax) : ModelCheckingMode :=
  if modeStx.isNone then .default
  else match modeStx[0] with
    | `(modelCheckMode| interpreted) => .interpreted
    | `(modelCheckMode| compiled) => .compiled
    | _ => .default

@[command_elab Veil.modelCheck]
def elabModelCheck : CommandElab := fun stx => do
  -- Use dynamic trace class name for detailed profiling
  withTraceNode `veil.perf.elaborator.modelCheck (fun _ => return "#model_check") do
    -- stx[1] is the optional mode, stx[2] is instTerm, stx[3] is optional theory, stx[4] is config
    let mode := getModelCheckingMode stx[1]
    let instTerm : Term := ⟨stx[2]⟩
    let theoryTermOpt : Option Term := if stx[3].isNone then none else some ⟨stx[3][0]⟩
    let cfg := stx[4]
    elabModelCheckCore stx mode instTerm theoryTermOpt cfg
where
  /-- Get the theory term, defaulting to `{}` if not provided and there are no theory fields.
      Throws a helpful error if theory fields exist but no term was provided. -/
  getTheoryTerm (theoryTermOpt : Option Term) (mod : Module) (instTerm : Term) : CommandElabM Term := do
    match theoryTermOpt with
    | some t => pure t
    | none =>
      unless mod.immutableComponents.isEmpty do
        let fieldStrs := mod.immutableComponents.map (fun c => s!"{c.name} := ...")
        let theoryExample := "{ " ++ ", ".intercalate fieldStrs.toList ++ " }"
        throwError "This module has immutable fields, so you must specify the theory instantiation:\n\
          #model_check {instTerm} {theoryExample}"
      `({})

  /-- Generate the model source for compilation:
      1. Insert `set_option veil.__modelCheckCompileMode true` after imports
      2. Keep everything up to the point where the spec was finalized
      3. Append the current `#model_check` command
      This filters out `#check_invariants`, `sat trace`, etc. from the compiled model. -/
  generateModelSource (mod : Module) (stx : Syntax) : CommandElabM String := do
    let src := (← getFileMap).source
    let afterImportsPos := ModelChecker.Compilation.findPosAfterImports src
    let compileModePreamble := "\nset_option veil.__modelCheckCompileMode true\n"
    -- Use the stored syntax where spec was finalized
    let some specFinalizedAtStx := mod.specFinalizedAtStx
      | throwError "Internal error: spec should be finalized before generating model source"
    let some modelCheckStart := stx.getPos? | throwError "Unexpected error: #model_check has no position"
    let some modelCheckEnd := stx.getTailPos? | throwError "Unexpected error: #model_check has no end position"
    -- If #model_check itself triggered finalization, use its start position to avoid duplication.
    -- Otherwise, use the tail position of the finalizing command (e.g., #gen_spec, #check_invariants).
    let modelCheckTriggeredFinalization := specFinalizedAtStx.getPos? == stx.getPos?
    let specFinalizedAtPos := if modelCheckTriggeredFinalization
      then modelCheckStart
      else specFinalizedAtStx.getTailPos?.getD modelCheckStart
    let beforeImports := String.Pos.Raw.extract src 0 afterImportsPos
    let afterImportsToSpecFinalized := String.Pos.Raw.extract src afterImportsPos specFinalizedAtPos
    let modelCheckCmd := String.Pos.Raw.extract src modelCheckStart modelCheckEnd
    return beforeImports ++ compileModePreamble ++ afterImportsToSpecFinalized ++ "\n" ++ modelCheckCmd ++ "\n"

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
      let base ← `([$(mkIdent ``Veil.ModelChecker.EarlyTerminationCondition.foundViolatingState),
                    $(mkIdent ``Veil.ModelChecker.EarlyTerminationCondition.assertionFailed),
                    $(mkIdent ``Veil.ModelChecker.EarlyTerminationCondition.deadlockOccurred)])
      if config.maxDepth > 0 then `($base ++ [$(mkIdent ``Veil.ModelChecker.EarlyTerminationCondition.reachedDepthBound) $(quote config.maxDepth)])
      else pure base
    `({ $(mkIdent `invariants):ident := $safetyList, $(mkIdent `terminating):ident := $terminatingProp,
        $(mkIdent `earlyTerminationConditions):ident := $earlyTermConds })

  /-- Build the core model checker call syntax (without parallel config). -/
  mkModelCheckerCall (mod : Module) (config : ModelCheckerConfig)
      (instTerm theoryTerm : Term) : CommandElabM Term := do
    let inst := mkVeilImplementationDetailIdent `inst
    let th := mkVeilImplementationDetailIdent `th
    let instSortArgs ← (← mod.sortIdents).mapM fun sortIdent => `($inst.$(sortIdent))
    let sp ← mkSearchParameters mod config
    -- Model checker call with type annotation to help inference
    -- Note: findReachable takes parallelCfg, progressInstanceId, and cancelToken as the last three args
    `((let $inst : $instantiationType := $instTerm
       let $th : $theoryIdent $instSortArgs* := $theoryTerm
       $(mkIdent ``Veil.ModelChecker.Concrete.findReachable)
         ($(mkIdentWithModName mod `enumerableTransitionSystem) $instSortArgs* $th)
         $sp : _ → _ → _ → IO _))

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

  /-- Create an error JSON object. -/
  errorJson (msg : String) : Json := Json.mkObj [("error", msg)]

  /-- Check if cancelled (ignoring handoff-triggered cancellations). -/
  checkCancelled (cancelToken : IO.CancelToken) (instanceId : Nat) : IO Bool := do
    if ← cancelToken.isSet then
      unless ← ModelChecker.Concrete.checkHandoffRequested instanceId do
        ModelChecker.Concrete.cancelProgress instanceId
        return true
    return false

  /-- Handle internal mode: define and export the model checker result. -/
  elabModelCheckInternalMode (mod : Module) (callExpr : Term) : CommandElabM Unit := do
    elabVeilCommand (← `(def $(mkIdent `modelCheckerResult) (pcfg : Option Veil.ModelChecker.ParallelConfig) (progressInstanceId : Nat) (cancelToken : IO.CancelToken) := $callExpr pcfg progressInstanceId cancelToken))
    elabVeilCommand (← `(end $(mkIdent mod.name)))
    elabVeilCommand (← `(export $(mkIdent mod.name) ($(mkIdent `modelCheckerResult))))

  /-- Build compilation error message from process result. -/
  mkCompilationErrorMsg (result : ModelChecker.Compilation.ProcessResult) : String :=
    s!"Compilation failed (exit code {result.exitCode}):\n" ++
      (if result.stderr.isEmpty then "" else s!"[stderr]\n{result.stderr}") ++
      (if result.stdout.isEmpty then "" else s!"[stdout]\n{result.stdout}\n")

  /-- Check if the compiled binary exists. Returns `some binPath` if found. -/
  verifyBinaryExists (buildFolder : System.FilePath) (instanceId : Nat) : IO (Option System.FilePath) := do
    let binPath := buildFolder / ".lake" / "build" / "bin"
    if ← (binPath / "ModelCheckerMain").pathExists then return some binPath
    ModelChecker.Concrete.finishProgress instanceId (errorJson s!"Binary not found at {binPath}")
    return none

  /-- Run the model checker binary and finish with result. Returns true if completed. -/
  runBinaryAndFinish (binPath : System.FilePath) (parallelCfg : Option ModelChecker.ParallelConfig)
      (instanceId : Nat) (cancelToken : IO.CancelToken)
      (assertionSources : Std.HashMap AssertionId AssertionSourceInfo) : IO Bool := do
    ModelChecker.Concrete.updateStatus instanceId "Running compiled binary..."
    let args := parallelCfg.map (fun p => #[s!"{p.numSubTasks}", s!"{p.thresholdToParallel}"]) |>.getD #[]
    let child ← IO.Process.spawn {
      cmd := toString (binPath / "ModelCheckerMain"), args,
      stdin := .piped, stdout := .piped, stderr := .piped }
    -- Read stderr for progress updates
    let stderrAccum ← IO.mkRef ""
    let _ ← IO.asTask (prio := .dedicated) do
      while true do
        let line ← child.stderr.getLine
        if line.isEmpty then break
        match Json.parse line >>= FromJson.fromJson? (α := ModelChecker.Concrete.Progress) with
        | .ok p => if let some refs ← ModelChecker.Concrete.getProgressRefs instanceId then
            refs.progressRef.modify fun old => { p with allActionLabels := old.allActionLabels }
        | .error _ => stderrAccum.modify (· ++ line)
    let stdoutTask ← IO.asTask (prio := .dedicated) child.stdout.readToEnd
    let waitTask ← IO.asTask (prio := .dedicated) child.wait
    -- Monitor for cancellation
    while !(← IO.hasFinished waitTask) do
      if ← checkCancelled cancelToken instanceId then child.kill; return false
      IO.sleep 100
    let stdout ← IO.ofExcept (← IO.wait stdoutTask)
    let exitCode ← IO.ofExcept (← IO.wait waitTask)
    let stderr ← stderrAccum.get
    if exitCode != 0 then
      ModelChecker.Concrete.finishProgress instanceId (errorJson s!"Binary exited with code {exitCode}{if stderr.isEmpty then "" else s!"\n{stderr}"}")
      return true
    let json := Json.parse stdout |>.toOption.getD (errorJson s!"Failed to parse output: {stdout.take 500}")
    ModelChecker.Concrete.finishProgress instanceId (enrichJsonWithAssertions json assertionSources)
    return true

  /-- Elaborate the interpreted mode computation. Must be called synchronously. -/
  elaborateInterpretedComputation (instanceId : Nat) (callExpr : Term)
      (parallelCfg : Option ModelChecker.ParallelConfig) : CommandElabM (IO Lean.Json) := do
    let resultExpr ← `(do
      let some refs ← Veil.ModelChecker.Concrete.getProgressRefs $(quote instanceId) | pure Lean.Json.null
      Lean.toJson <$> $callExpr ($(quote parallelCfg)) ($(quote instanceId)) refs.cancelToken)
    trace[veil.desugar] "{resultExpr}"
    liftTermElabM do
      let expr ← Term.elabTerm resultExpr none
      Term.synthesizeSyntheticMVarsNoPostponing
      unsafe Meta.evalExpr (IO Lean.Json) (mkApp (mkConst ``IO) (mkConst ``Lean.Json)) (← instantiateMVars expr)

  /-- Get all action label names for never-enabled action warnings. -/
  getActionLabelNames (mod : Module) : CommandElabM (List String) := do
    let labelTypeName ← resolveGlobalConstNoOverload labelType
    return mod.actions.map (fun a => s!"{labelTypeName}.{a.name}") |>.toList

  /-- Log model checking result. -/
  logModelCheckResult (stx : Syntax) (resultJson : Json) : CommandElabM Unit := do
    let msg := TraceDisplay.formatModelCheckingResult resultJson
    let isViolation := resultJson.getObjValD "result" == Json.str "found_violation" ||
                       resultJson.getObjValD "error" != .null
    let violationIsError := veil.violationIsError.get (← getOptions)
    if isViolation && violationIsError then logErrorAt stx msg else logInfoAt stx msg

  /-- Allocate a model check context with progress tracking. -/
  allocModelCheckContext (mod : Module) (stx : Syntax)
      (parallelCfg : Option ModelChecker.ParallelConfig) : CommandElabM ModelCheckContext := do
    let (instanceId, cancelToken) ← ModelChecker.Concrete.allocProgressInstance (← getActionLabelNames mod)
    let assertionSources := extractAssertionSources (← globalEnv.get).assertions (← getFileMap)
    return { mod, stx, instanceId, cancelToken, assertionSources, parallelCfg }

  /-- Handle errors in model checking computations. -/
  handleModelCheckError (ctx : ModelCheckContext) (e : Exception) : CommandElabM Unit := do
    let json := errorJson s!"{← e.toMessageData.toString}"
    logModelCheckResult ctx.stx json
    ModelChecker.Concrete.finishProgress ctx.instanceId json

  /-- Finish model checking with a successful result. -/
  finishWithResult (ctx : ModelCheckContext) (json : Json) : CommandElabM Unit := do
    let json := enrichJsonWithAssertions json ctx.assertionSources
    logModelCheckResult ctx.stx json
    ModelChecker.Concrete.finishProgress ctx.instanceId json

  /-- Run the compiled binary and log the result. -/
  runBinaryAndLogResult (ctx : ModelCheckContext) (buildFolder : System.FilePath)
      (sourceFile : String) : CommandElabM Unit := do
    let some binPath ← verifyBinaryExists buildFolder ctx.instanceId | return
    let _ ← runBinaryAndFinish binPath ctx.parallelCfg ctx.instanceId ctx.cancelToken ctx.assertionSources
    ModelChecker.Compilation.markRegistryFinished sourceFile buildFolder
    let some resultJson ← ModelChecker.Concrete.getResultJson ctx.instanceId | return
    logModelCheckResult ctx.stx resultJson

  /-- Compile the model. Returns the build folder path if compilation succeeded, none otherwise. -/
  compileModel (mod : Module) (sourceFile : String) (modelSource : String)
      (instanceId : Nat) : IO (Option System.FilePath) := do
    let buildFolder ← ModelChecker.Compilation.createBuildFolder sourceFile modelSource mod.name.toString
    ModelChecker.Compilation.markRegistryInProgress sourceFile instanceId buildFolder
    let result ← ModelChecker.Compilation.runProcessWithStatusCallback
      { cmd := "lake", args := #["build", "ModelCheckerMain"], cwd := buildFolder }
      (fun elapsedMs => ModelChecker.Concrete.updateCompilationElapsed instanceId elapsedMs)
      (fun line isError elapsedMs => ModelChecker.Concrete.updateCompilationLog instanceId elapsedMs line isError)
    if result.exitCode != 0 then
      ModelChecker.Concrete.updateCompilationStatus instanceId (.failed (mkCompilationErrorMsg result))
      return none
    ModelChecker.Concrete.updateCompilationStatus instanceId .succeeded
    return some buildFolder

  /-- Core elaboration logic shared by all model checking modes. -/
  elabModelCheckCore (stx : Syntax) (mode : ModelCheckingMode) (instTerm : Term)
      (theoryTermOpt : Option Term) (cfg : Syntax) : CommandElabM Unit := do
    let mod ← getCurrentModule (errMsg := "You cannot #model_check outside of a Veil module!")
    mod.throwIfSpecNotFinalized

    let theoryTerm ← getTheoryTerm theoryTermOpt mod instTerm

    warnAboutTransitions mod
    let config ← elabModelCheckerConfig cfg
    -- Resolve parallelCfg: sequential flag takes precedence, otherwise default to parallel
    let parallelCfg ← match config.sequential, config.parallelCfg with
      | true, _ => pure none
      | false, some cfg => pure (some cfg)
      | false, none => pure (some { numSubTasks := ← getNumCores, thresholdToParallel := defaultThresholdToParallel })
    let config := { config with parallelCfg := parallelCfg }
    let callExpr ← mkModelCheckerCall mod config instTerm theoryTerm

    -- Dispatch based on compilation mode (set via option) and mode keyword
    let isCompileMode ← isModelCheckCompileMode
    match isCompileMode, mode with
    | true, _            => elabModelCheckInternalMode mod callExpr  -- In compiled binary
    | false, .interpreted => elabModelCheckInterpretedMode mod stx callExpr parallelCfg
    | false, .compiled    => elabModelCheckCompiledMode mod stx parallelCfg
    | false, .default     => elabModelCheckWithHandoff mod stx callExpr parallelCfg

  /-- Handle interpreted mode: evaluate and display results directly. -/
  elabModelCheckInterpretedMode (mod : Module) (stx : Syntax) (callExpr : Term)
      (parallelCfg : Option ModelChecker.ParallelConfig) : CommandElabM Unit := do
    -- dbg_trace "elabModelCheckInterpretedMode"
    let ctx ← allocModelCheckContext mod stx parallelCfg
    let ioComputation ← elaborateInterpretedComputation ctx.instanceId callExpr parallelCfg
    let computation ← Command.wrapAsyncAsSnapshot (fun () => do
      try
        if ← checkCancelled ctx.cancelToken ctx.instanceId then return
        let json ← IO.ofExcept (← ioComputation.toIO')
        finishWithResult ctx json
      catch e : Exception =>
        handleModelCheckError ctx e
    ) ctx.cancelToken
    let mkTask ← BaseIO.asTask (computation ()) (prio := .dedicated)
    Command.logSnapshotTask { stx? := none, cancelTk? := ctx.cancelToken, task := mkTask }
    ModelChecker.displayStreamingProgress stx ctx.instanceId

  /-- Handle compiled-only mode: compile and run binary without interpreted fallback. -/
  elabModelCheckCompiledMode (mod : Module) (stx : Syntax)
      (parallelCfg : Option ModelChecker.ParallelConfig) : CommandElabM Unit := do
    -- dbg_trace "elabModelCheckCompiledMode"
    let ctx ← allocModelCheckContext mod stx parallelCfg
    let sourceFile ← getFileName
    let modelSource ← generateModelSource mod stx

    let compilationComputation ← Command.wrapAsyncAsSnapshot (fun () => do
      try
        let some buildFolder ← compileModel mod sourceFile modelSource ctx.instanceId | return
        if ← checkCancelled ctx.cancelToken ctx.instanceId then return
        runBinaryAndLogResult ctx buildFolder sourceFile
      catch e : Exception =>
        handleModelCheckError ctx e
    ) ctx.cancelToken

    let compilationTask ← BaseIO.asTask (compilationComputation ()) (prio := .dedicated)
    Command.logSnapshotTask { stx? := none, cancelTk? := ctx.cancelToken, task := compilationTask }
    ModelChecker.displayStreamingProgress stx ctx.instanceId

  /-- Handle default mode: run interpreted + background compile with handoff. -/
  elabModelCheckWithHandoff (mod : Module) (stx : Syntax) (callExpr : Term)
      (parallelCfg : Option ModelChecker.ParallelConfig) : CommandElabM Unit := do
    -- dbg_trace "elabModelCheckWithHandoff"
    let ctx ← allocModelCheckContext mod stx parallelCfg
    let sourceFile ← getFileName
    let modelSource ← generateModelSource mod stx
    let ioComputation ← elaborateInterpretedComputation ctx.instanceId callExpr parallelCfg

    -- Interpreted mode task (wrapped for async logging)
    let interpretedComputation ← Command.wrapAsyncAsSnapshot (fun () => do
      try
        let json ← IO.ofExcept (← ioComputation.toIO')
        match (← ctx.cancelToken.isSet, ← ModelChecker.Concrete.checkHandoffRequested ctx.instanceId) with
        | (true, false) => ModelChecker.Concrete.cancelProgress ctx.instanceId  -- User clicked Stop
        | (false, _) => finishWithResult ctx json
        | (true, true) => pure ()  -- Handoff requested, let compiled binary take over
      catch e : Exception =>
        handleModelCheckError ctx e
    ) ctx.cancelToken
    let interpretedTask ← BaseIO.asTask (interpretedComputation ()) (prio := .dedicated)
    Command.logSnapshotTask { stx? := none, cancelTk? := ctx.cancelToken, task := interpretedTask }

    -- Background compilation with handoff
    let compilationCancelTk ← IO.CancelToken.new
    let compilationComputation ← Command.wrapAsyncAsSnapshot (fun () => do
      try
        let some buildFolder ← compileModel mod sourceFile modelSource ctx.instanceId | return
        -- Skip handoff if violation found or interpreted finished
        if (← ModelChecker.Concrete.isViolationFound ctx.instanceId) || (← IO.hasFinished interpretedTask) then
          ModelChecker.Compilation.markRegistryFinished sourceFile buildFolder
          return
        -- Handoff to compiled binary
        ModelChecker.Concrete.requestHandoff ctx.instanceId
        ctx.cancelToken.set
        let _ ← IO.wait interpretedTask
        let some newCancelToken ← ModelChecker.Concrete.resetProgressForHandoff ctx.instanceId | return
        let ctxWithNewToken := { ctx with cancelToken := newCancelToken }
        runBinaryAndLogResult ctxWithNewToken buildFolder sourceFile
      catch e : Exception =>
        ModelChecker.Concrete.updateCompilationStatus ctx.instanceId (.failed s!"{← e.toMessageData.toString}")
    ) compilationCancelTk
    let compilationTask ← BaseIO.asTask (compilationComputation ()) (prio := .dedicated)
    Command.logSnapshotTask { stx? := none, cancelTk? := compilationCancelTk, task := compilationTask }

    ModelChecker.displayStreamingProgress stx ctx.instanceId

end Veil
