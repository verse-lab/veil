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
import Veil.Core.UI.Widget.ProgressViewer
import Veil.Frontend.DSL.Action.Extract2

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
where
  isEqualToOneOf {m} [Monad m] [MonadQuotation m] (x : TSyntax `term) (xs : Array (TSyntax `term)) : m (TSyntax `term) := do
    let equalities ← xs.mapM (fun elem => `($x = $(elem)))
    repeatedOr equalities
  mkEnumAxiomatisation {m} [Monad m] [MonadQuotation m] (id : Ident) (elems : Array Ident) : m (Ident × TSyntax `command) := do
    let variants ← elems.mapM (fun elem => `(Command.structSimpleBinder|$elem:ident : $id))
    let (class_name, ax_distinct, ax_complete) := (Ident.toEnumClass id, enumDistinct, enumComplete)
    let ax_distinct ← `(Command.structSimpleBinder|$ax_distinct:ident : distinct $[$elems]*)
    let x := mkVeilImplementationDetailIdent `x
    let ax_complete ← `(Command.structSimpleBinder|$ax_complete:ident : ∀ ($x : $id), $(← isEqualToOneOf x elems))
    let class_decl ← `(
      class $class_name ($id : $(mkIdent ``outParam) Type) where
        $[$variants]*
        $ax_distinct
        $ax_complete)
    return (class_name, class_decl)
  mkEnumConcreteType {m} [Monad m] [MonadQuotation m] (id : Ident) (elems : Array Ident) : m (Array (TSyntax `command)) := do
    let name := Ident.toEnumConcreteType id
    let ctors ← elems.mapM fun el => `(Lean.Parser.Command.ctor| | $el:ident )
    let indType ← do
      if !ctors.isEmpty then
        `(inductive $name where $[$ctors]* deriving $(mkIdent ``DecidableEq):ident, $(mkIdent ``Repr):ident, $(mkIdent ``Inhabited):ident, $(mkIdent ``Nonempty):ident)
      else
        `(inductive $name where deriving $(mkIdent ``DecidableEq):ident, $(mkIdent ``Repr):ident)
    -- show that the concrete type satisfies the axiomatisation
    let concElems : Array Ident := elems.map fun el => mkIdent (name.getId ++ el.getId)
    let instFields ← (elems.zip concElems).mapM fun (el, concEl) => `(Lean.Parser.Term.structInstField| $el:ident := $concEl:ident)
    let distinctField ← `(Lean.Parser.Term.structInstField| $enumDistinct:ident :=  (by (try decide); (try grind)))
    let completeField ← do
      let x := mkVeilImplementationDetailIdent `x
      `(Lean.Parser.Term.structInstField| $enumComplete:ident := (by intro $x:ident <;> cases $x:ident <;> (first | decide | grind)))
    let fields := instFields ++ #[distinctField, completeField]
    let instanceAx ← `(command|instance : $(Ident.toEnumClass id) $name where $[$fields]*)
    -- show that the concrete type is a `Veil.Enumeration`
    let constructors ← `(term| [ $concElems,* ] )
    let complete : Ident := mkIdent $ Name.toEnumClass id.getId ++ enumCompleteName
    let instanceEnumeration ←
      `(instance : $(mkIdent ``Enumeration) $name := $(mkIdent ``Enumeration.mk) $constructors (by simp ; exact $complete))
    -- derive instances for the concrete type
    let derivedInsts ← `(command| deriving instance $(mkIdent ``Ord):ident, $(mkIdent ``Hashable):ident for $name)
    -- we derive instances for `Std.OrientedCmp`, `Std.TransCmp`, and `Std.LawfulEqCmp` manually
    let ord ← `($(mkIdent ``Ord.compare) ($(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $name)))
    let instMk := fun ty => `(command| instance : $(mkIdent ty) $ord := by apply$(mkIdent $ ty ++ `mk) ; decide)
    let ordInsts ← #[``Std.OrientedCmp, ``Std.TransCmp, ``Std.LawfulEqCmp].mapM instMk
    return #[indType, instanceAx, instanceEnumeration, derivedInsts] ++ ordInsts

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

/-- Log errors at assertion locations for disproven `doesNotThrow` VCs. -/
private def logDoesNotThrowErrors (results : VerificationResults VCMetadata SmtResult) : CommandElabM Unit := do
  let actx := (← globalEnv.get).assertions
  for vc in results.vcs do
    if vc.metadata.property != `doesNotThrow then continue
    for d in vc.timing.dischargers do
      let .some (.disproven (.some (.sat ces)) _) := d.result | continue
      for ce in ces.filterMap id do
        let .ok extraVals := ce.structuredJson.getObjVal? "extraVals" | continue
        let .ok exVal := extraVals.getObjVal? "__veil_ex" | continue
        let .ok exId := exVal.getInt? | continue
        let .some a := actx.find[exId]?
          | throwError s!"Assertion {exId} not found (from {vc.metadata.action})"; continue
        logErrorAt a.ctx.stx s!"This assertion might fail when called from {vc.metadata.action}"

open Lean.Meta.Tactic.TryThis in
@[command_elab Veil.checkInvariants]
def elabCheckInvariants : CommandElab := fun stx => do
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
    --   (fun ref => do let mgr ← ref.get; return mgr.isDone)
    --   (fun ref => do let mgr ← ref.get; logInfo m!"{mgr}"; logInfo m!"{Lean.toJson (← mgr.toVerificationResults)}")
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
  parallelCfg : Option ModelChecker.ParallelConfig := none
  deriving Repr

declare_command_config_elab elabModelCheckerConfig ModelCheckerConfig

@[command_elab Veil.modelCheck]
def elabModelCheck : CommandElab := fun stx => do
  match stx with
  | `(#model_check%$tk $[internal_mode%$internal?]? $[after_compilation%$compile?]? $instTerm:term $theoryTerm:term $cfg) =>
    -- Write modified source for compilation (if in compilation mode)
    if internal?.isNone && compile?.isSome then
      writeSourceForCompilation tk stx

    let mod ← getCurrentModule (errMsg := "You cannot #model_check outside of a Veil module!")
    let mod ← mod.ensureSpecIsFinalized
    localEnv.modifyModule (fun _ => mod)

    warnAboutTransitions mod
    let config ← elabModelCheckerConfig cfg
    let callExpr ← mkModelCheckerCall mod config instTerm theoryTerm

    -- Dispatch to appropriate mode handler
    match internal?.isSome, compile?.isSome with
    | true, false  => throwError "The 'internal_mode' keyword is inserted by Veil when compiling the specification. You should never add it manually."
    | true, true   => elabModelCheckInternalMode mod callExpr
    | false, false => elabModelCheckInterpretedMode stx callExpr config.parallelCfg
    | false, true  => elabModelCheckCompiledMode stx config.parallelCfg
  | _ => throwUnsupportedSyntax
where
  /-- Display a TraceDisplayViewer widget with the given result term. -/
  displayResultWidget (stx : Syntax) (resultTerm : Term) : CommandElabM Unit := do
    let widgetExpr ← `(open ProofWidgets.Jsx in
      <ProofWidgets.TraceDisplayViewer result={$resultTerm} layout={"vertical"} />)
    let html ← ← liftTermElabM <| ProofWidgets.HtmlCommand.evalCommandMHtml <| ← ``(ProofWidgets.HtmlEval.eval $widgetExpr)
    liftCoreM <| Widget.savePanelWidgetInfo
      (hash ProofWidgets.HtmlDisplayPanel.javascript)
      (return json% { html: $(← Server.rpcEncode html) }) stx

  /-- Build the core model checker call syntax (without parallel config). -/
  mkModelCheckerCall (mod : Module) (config : ModelCheckerConfig)
      (instTerm theoryTerm : Term) : CommandElabM Term := do
    let inst := mkVeilImplementationDetailIdent `inst
    let th := mkVeilImplementationDetailIdent `th
    let instSortArgs ← (← mod.sortIdents).mapM fun sortIdent => `($inst.$(sortIdent))
    -- Build SafetyProperty.mk syntax for a StateAssertion
    let mkProp (sa : StateAssertion) : CommandElabM Term :=
      `(Veil.ModelChecker.SafetyProperty.mk (name := $(quote sa.name))
          (property := fun th st => $(Lean.mkIdent sa.name) th st))
    let safetyList ← `([$((← mod.invariants.mapM mkProp)),*])
    let terminatingProp ← match mod.terminations[0]? with
      | some t => mkProp t
      | none => `(default)
    let earlyTermConds ← do
      let base ← `([Veil.ModelChecker.EarlyTerminationCondition.foundViolatingState])
      if config.maxDepth > 0 then `($base ++ [Veil.ModelChecker.EarlyTerminationCondition.reachedDepthBound $(quote config.maxDepth)])
      else pure base
    -- Model checker call with type annotation to help inference
    -- Note: findReachable takes parallelCfg and progressInstanceId as the last two args
    `((let $inst : $instantiationType := $instTerm
       let $th : $theoryIdent $instSortArgs* := $theoryTerm
       $(mkIdent ``Veil.ModelChecker.Concrete.findReachable)
         ($(mkIdent `enumerableTransitionSystem) $instSortArgs* $th)
         { invariants := $safetyList, terminating := $terminatingProp,
           earlyTerminationConditions := $earlyTermConds } : _ → _ → IO _))

  /-- Write modified source file for compilation mode. -/
  writeSourceForCompilation (tk stx : Syntax) : CommandElabM Unit := do
    -- Copy the current file into a dedicated file
    --
    -- NOTE: This command *should not* be copied verbatim into the new file,
    -- otherwise this process will go into a loop. NOTE: Since some definitions
    -- required for compilation are not available *before this command*, we need
    -- to somehow make them available. The approach taken here is to change the
    -- behavior of the command in the new file by doing minimal source-to-source
    -- transformation: we insert the `internal_mode` keyword after `#model_check`,
    -- which makes the command skip the compilation step.
    let some posTk := tk.getTailPos? | throwError "Unexpected error"
    let some posStx := stx.getTailPos? | throwError "Unexpected error"
    let src := (← getFileMap).source
    let newSource := String.Pos.Raw.extract src 0 posTk ++ " internal_mode " ++ String.Pos.Raw.extract src posTk posStx
    IO.FS.writeFile ((← IO.currentDir) / "ToBeImportedByModelCheckerMain.lean") newSource

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

  /-- Handle internal mode: define and export the model checker result. -/
  elabModelCheckInternalMode (mod : Module) (callExpr : Term) : CommandElabM Unit := do
    elabVeilCommand (← `(def $(mkIdent `modelCheckerResult) (pcfg : Option Veil.ModelChecker.ParallelConfig) (progressInstanceId : Nat) := $callExpr pcfg progressInstanceId))
    elabVeilCommand (← `(end $(mkIdent mod.name)))
    elabVeilCommand (← `(export $(mkIdent mod.name) ($(mkIdent `modelCheckerResult))))

  /-- Run a process, updating status with elapsed time until it completes. -/
  runProcessWithStatus (cfg : IO.Process.SpawnArgs) (instanceId : Nat) (statusPrefix : String) : IO Unit := do
    let proc ← IO.Process.spawn { cfg with stdin := .piped, stdout := .piped, stderr := .piped }
    let waitTask ← IO.asTask (prio := .dedicated) proc.wait
    while !(← IO.hasFinished waitTask) do
      IO.sleep 100
      if let some refs ← ModelChecker.Concrete.getProgressRefs instanceId then
        let elapsed := ModelChecker.formatElapsedTime (← refs.progressRef.get).elapsedMs
        ModelChecker.Concrete.updateStatus instanceId s!"{statusPrefix} ({elapsed})"
    let _ ← IO.wait waitTask

  /-- Read stderr lines from a subprocess and update progress refs until EOF. -/
  readStderrProgress (stderr : IO.FS.Handle) (instanceId : Nat) : IO Unit := do
    repeat do
      let line ← stderr.getLine
      if line.isEmpty then break
      if let .ok json := Json.parse line then
        if let .ok (p : ModelChecker.Concrete.Progress) := FromJson.fromJson? json then
          if let some refs ← ModelChecker.Concrete.getProgressRefs instanceId then
            refs.progressRef.set p

  /-- Handle compiled mode: build, run, and display results with streaming progress. -/
  elabModelCheckCompiledMode (stx : Syntax) (parallelCfg : Option ModelChecker.ParallelConfig) : CommandElabM Unit := do
    let instanceId ← ModelChecker.Concrete.allocProgressInstance
    let cwd ← IO.currentDir
    let _ ← IO.asTask (prio := .dedicated) do
      -- Compile
      runProcessWithStatus { cmd := "lake", args := #["build", "ModelCheckerMain"], cwd } instanceId "Compiling"
      -- Run model checker
      ModelChecker.Concrete.updateStatus instanceId "Running..."
      let args := parallelCfg.map (fun p => #[toString p.numSubTasks, toString p.thresholdToParallel]) |>.getD #[]
      let child ← IO.Process.spawn {
        cmd := "ModelCheckerMain", args, cwd := cwd / ".lake" / "build" / "bin",
        stdin := .piped, stdout := .piped, stderr := .piped }
      readStderrProgress child.stderr instanceId
      let stdout ← IO.FS.Handle.readToEnd child.stdout
      let _ ← child.wait
      ModelChecker.Concrete.finishProgress instanceId (Json.parse stdout |>.toOption.getD .null)
    ModelChecker.displayStreamingProgress stx instanceId

  /-- Handle interpreted mode: evaluate and display results directly. -/
  elabModelCheckInterpretedMode (stx : Syntax) (callExpr : Term)
      (parallelCfg : Option ModelChecker.ParallelConfig) : CommandElabM Unit := do
    -- Allocate a unique progress instance ID before starting the task
    let instanceId ← ModelChecker.Concrete.allocProgressInstance
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
      -- Mark progress as complete and store result JSON
      ModelChecker.Concrete.finishProgress instanceId json
    -- Display streaming progress widget with the same instance ID
    ModelChecker.displayStreamingProgress stx instanceId

end Veil
