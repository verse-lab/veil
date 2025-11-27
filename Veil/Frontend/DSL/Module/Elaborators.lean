import Lean
import Veil.Frontend.DSL.Module.Syntax
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Action.Elaborators
import Veil.Frontend.DSL.State.SubState
import Veil.Frontend.DSL.Module.VCGen
import Veil.Core.Tools.Verifier.Server

open Lean Parser Elab Command

namespace Veil

@[command_elab Veil.moduleDeclaration]
def elabModuleDeclaration : CommandElab := fun stx => do
  match stx with
  | `(veil module $modName:ident) => do
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
    -- Declare the uninterpreted sort
    elabCommand $ ← `(type $id)
    -- Declare a class for the enum type
    let variants ← elems.mapM (fun elem => `(Command.structSimpleBinder|$elem:ident : $id))
    let (class_name, ax_distinct, ax_complete) := (mkIdent (Name.mkSimple s!"{id.getId}_Enum"), mkIdent $ Name.mkSimple s!"{id.getId}_distinct", mkIdent $ Name.mkSimple s!"{id.getId}_complete")
    let ax_distinct ← `(Command.structSimpleBinder|$ax_distinct:ident : distinct $[$elems]*)
    let x := mkIdent $ Name.mkSimple s!"{id.getId}_x"
    let ax_complete ← `(Command.structSimpleBinder|$ax_complete:ident : ∀ ($x : $id), $(← isEqualToOneOf x elems))
    let class_decl ← `(
      class $class_name ($id : outParam Type) where
        $[$variants]*
        $ax_distinct
        $ax_complete
    )
    elabCommand class_decl
    let instanceName := mkIdent $ Name.mkSimple s!"{id.getId}_isEnum"
    let instanceV ← `(command|instantiate $instanceName : @$class_name $id)
    trace[veil.debug] "Elaborated enum instance: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic instanceV}"
    elabCommand instanceV
    elabCommand $ ← `(open $class_name:ident)
  | _ => throwUnsupportedSyntax
where
isEqualToOneOf {m} [Monad m] [MonadQuotation m] (x : TSyntax `term) (xs : Array (TSyntax `term)) : m (TSyntax `term) := do
  let equalities ← xs.mapM (fun elem => `($x = $(elem)))
  repeatedOr equalities

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

/-- Crystallizes the state of the module, i.e. it defines it as a Lean
`structure` definition, if that hasn't already happened. -/
private def Module.ensureStateIsDefined (mod : Module) : CommandElabM Module := do
  if mod.isStateDefined then
    return mod
  let mod ← if mod._useFieldRepTC
  then
    let (mod, stxs) ← mod.declareStateFieldLabelTypeAndDispatchers
    let (mod, stateStx) ← mod.declareFieldsAbstractedStateStructure
    let (mod, theoryStx) ← mod.declareTheoryStructure
    for stx in stxs do
      elabVeilCommand stx
    elabVeilCommand stateStx
    elabVeilCommand theoryStx
    generateIgnoreFn mod
    pure { mod with _stateDefined := true }
  else
    let (mod, stateStx) ← mod.declareStateStructure
    let (mod, theoryStx) ← mod.declareTheoryStructure
    elabVeilCommand stateStx
    elabVeilCommand theoryStx
    generateIgnoreFn mod
    pure { mod with _stateDefined := true }
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
  Verifier.runManager
  mod.generateVCs
  return { mod with _specFinalized := true }

@[command_elab Veil.checkInvariants]
def elabCheckInvariants : CommandElab := fun _stx => do
  let mod ← getCurrentModule (errMsg := "You cannot #check_invariant outside of a Veil module!")
  let _ ← mod.ensureSpecIsFinalized
  Verifier.startAll
  vcManager.atomicallyOnce frontendNotification
    (fun ref => do let mgr ← ref.get; return mgr._doneWith.size == mgr.nodes.size)
    (fun ref => do let mgr ← ref.get; logInfo m!"{mgr}"; logInfo m!"{Lean.toJson mgr}")

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
    mod.defineTransition (ProcedureInfo.action nm.getId) br trStx stx
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

end Veil
