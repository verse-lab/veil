module

public meta import Lean
public meta import Veil.Frontend.DSL.Module.Representation
public meta import Veil.Frontend.DSL.Module.Util
public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Frontend.DSL.Infra.Metadata
public meta import Veil.Util.Meta
public meta import Veil.Core.Tools.Verifier.Server
public meta import Veil.Frontend.DSL.Tactic
-- FIXME: it really doesn't make sense to import this here
public meta import Veil.Core.UI.Verifier.Model
public meta import Veil.Core.UI.Verifier.InductionCounterexample
public meta import Veil.Frontend.DSL.Module.VCGen.Replay

public meta section

/-!
# Induction VC Generation

This module provides VC generation for inductive invariant verification.
It handles the standard invariant preservation VCs for actions and initializers.
-/

open Lean Elab Term Command

namespace Veil

/-! ## Induction-Specific Result Processing -/

/-- Refute the original induction obligation at the reconstructed action, theory and states. -/
def checkInductionWitness (mod : Module) (vc : VCStatement) (md : InductionVCMetadata)
    (w : VeilCTI) : TermElabM WitnessCheck := checkWitness do
  let mut args := #[]
  let some proc := mod.procedures.find? (·.name == md.action) | throwError "unknown action"
  if proc.info != .initializer then
    let some label := w.labelExpr | throwError "missing action label"
    let label ← Meta.whnf label
    let labelType := mkAppN (mkConst (mod.name ++ labelTypeName)) w.theoryType.getAppArgs
    unless ← Meta.isDefEq (← Meta.inferType label) labelType do throwError "wrong label type"
    let some ctor ← Meta.isConstructorApp? label | throwError "unresolved action label"
    unless ctor.name == mod.name ++ labelTypeName ++ md.action do return mkConst ``False
    args := label.getAppArgs.extract ctor.numParams label.getAppNumArgs
  else if w.labelExpr.isSome then return mkConst ``False
  unless args.size == proc.params.size do throwError "missing action arguments"
  if veil.solver.get (← getOptions) matches .custom then
    if (md.baseParams ++ md.extraParams).any (·.kind == .moduleTypeclass .userDefined) then
      throwError "custom solver does not identify instance binders"
  let values ← witnessAssignments w.ctx w.extraVals
  let body ← specializeWitnessModule (← vc.type) (md.baseParams ++ md.extraParams)
    w.theoryType w.stateType w.enumAdapts values
  let mut triple ← specializeWitness body args
  if md.style == .tr then
    let some after := w.postStateExpr | throwError "missing post-state"
    unless triple.isAppOf ``Transition.meetsSpecificationIfSuccessfulAssuming do
      throwError "expected a TR preservation obligation"
    return mkNot (← specializeWitness triple #[w.theoryExpr, w.preStateExpr, after])
  if md.property == `doesNotThrow then
    let some ex := values[modelValueName `exception]? | throwError "missing exception ID"
    triple ← specializeWitness triple #[ex]
    unless triple.isAppOf ``VeilM.doesNotThrowAssuming_ex do throwError "expected an exception obligation"
    if w.postStateExpr.isSome then throwError "exception model includes a post-state"
  else
    unless triple.isAppOf ``VeilM.meetsSpecificationIfSuccessfulAssuming do
      throwError "expected a WP preservation obligation"
    if let some after := w.postStateExpr then
      -- A violation of this postcondition must reach the reported state on the same run.
      checkWitnessArg after w.stateType
      let post := triple.appArg!
      let post ← Meta.withLocalDeclD `th w.theoryType fun th =>
        Meta.withLocalDeclD `st w.stateType fun st => do
          Meta.mkLambdaFVars #[th, st] (mkOr (mkApp2 post th st) (mkNot (← Meta.mkEq st after)))
      triple := mkApp triple.appFn! post
  let original ← specializeWitness triple #[w.theoryExpr, w.preStateExpr]
  let choices := values.filter fun name _ => !isModelParameterName name && (modelBinderKey? name).isNone
  checkWPChoices original (mod.name ++ toExtName md.action) choices w.enumAdapts

/-- Process SMT outputs and build counterexamples for inductive VCs. -/
private def overallSmtResult (actName : Name) (outputs : Array SmtOutput)
    (replay : VeilCTI → TermElabM WitnessCheck) : TermElabM (Option SmtResult) := do
  let mod ← getCurrentModule
  let customSolver := veil.solver.get (← getOptions) matches .custom
  buildSmtResult outputs (fun sat => do
    -- Custom tactics still see the original binder names. A solver model from
    -- such a tactic does not identify its module parameters for reconstruction.
    if customSolver && mod.parameters.any (·.kind matches .userParameter) then
      return sat.map (fun _ => none)
    sat.filterMapM (fun ce => return ← ce.mapM (fun ce => do
      try
        let veilModel ← buildCounterexampleExprs ce mod actName
        let structuredJson : Json ← unsafe veilModel.toJson
        let result ← replay veilModel
        let structuredJson := structuredJson.setObjVal! "witnessCheck" (toJson result)
        return .some { raw := ce, rawHtml := ← renderSmtModel ce, structuredJson := structuredJson }
      catch ex =>
        dbg_trace "Failed to build counterexample; exception: {← ex.toMessageData.toString}"
        return none)))

/-- Create a DischargerResult from SMT outputs for inductive VCs. -/
private def mkDischargerResult (replay : VeilCTI → TermElabM WitnessCheck)
    (expectedName : Name) (actName : Name)
    (ch : Std.CloseableChannel ((Name × Nat) × Smt.AsyncOutput))
    (data : Witness ⊕ Exception) (time : Nat) : TermElabM (DischargerResult SmtResult) := do
  let outputs ← collectSmtOutputs ch expectedName
  let result ← overallSmtResult actName outputs replay
  match result with
  | .some result => match result with
    | .error exs => return .error exs time
    | .sat _ => return .disproven result time
    | .unknown _ => return .unknown result time
    | .unsat _ => do
      match data with
      | .inl witness => return .proven (some witness) result time
      | _ =>
        let s := "mkDischargerResult: overallSmtResult is unsat, but no witness provided"
        dbg_trace s; throwError s
  | .none =>
    match data with
    | .inl witness => return .proven (some witness) .none time
    | .inr ex =>
      match ← unknownReasonFromException? ex with
      | some reason => return .unknown (.some (.unknown #[reason])) time
      | none => return .error #[(ex, s!"{← ex.toMessageData.toString}")] time

/-! ## VC Discharger -/

/-- Create a discharger for inductive verification conditions. -/
def VCDischarger.fromTerm (term : Term) (metadata : VCMetadata) (vcStatement : VCStatement)
    (dischargerId : DischargerIdentifier) (ch : Std.Channel (ManagerNotification VCMetadata SmtResult))
    (_cancelTk? : Option IO.CancelToken := none) : CommandElabM (Discharger SmtResult) := do
  let .induction md := metadata | throwError "expected induction metadata"
  let suffix := if md.style == .wp then "_WP" else "_TR"
  let dischargerId := { dischargerId with name := .mkSimple (dischargerId.name.getString! ++ suffix) }
  -- Proof inlining only needs declarations, not mutable runtime handles.
  let env0 := Veil.Verifier.clearVerifierRuntime (← getEnv)
  let mod ← getCurrentModule
  let modelNames := if veil.solver.get (← getOptions) matches .custom then #[] else Id.run do
    let names := moduleModelNames (md.baseParams ++ md.extraParams)
    let args := (mod.procedures.find? (·.name == md.action)).map (·.params) |>.getD #[]
    let ex := if md.property == `doesNotThrow then #[some (modelValueName `exception)] else #[]
    return names ++ args.mapIdx (fun i _ => some (modelValueName (.num `arg i))) ++ ex
  Discharger.fromTermWith term vcStatement dischargerId ch (modelNames := modelNames) fun smtCh data time => do
    let data : Witness ⊕ Exception ← match data with
      | .inl witness => do
        let witness ← inlineFreshProofs env0 witness
        -- A throw here is caught by `Discharger.fromTermWith`, which re-invokes
        -- us with the exception (`.inr`); `mkDischargerResult` then throws its
        -- "unsat, but no witness provided" when the solver succeeded but the
        -- tactic still failed, and the fallback error result is published.
        if witness.hasMVar || witness.hasFVar || witness.hasSyntheticSorry then
          throwError "unsolved goals"
        pure (.inl witness)
      | .inr ex => pure (.inr ex)
    mkDischargerResult (checkInductionWitness mod vcStatement md) dischargerId.name md.action smtCh data time

/-! ## VC Statement Building -/

private def DeclarationKind.assumesInvariantsForInductionVC : DeclarationKind → Bool
  | .procedure .initializer => false
  | _ => true

private def mkInductionPrecondition [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [AddErrorMessageContext m]
    (mod : Module) (dependsOn : Std.HashSet Name) (assumesInvariants : Bool) : m Term := do
  if assumesInvariants then
    let (_, invArgs) ← mod.declarationAllBindersArgs assembledInvariantsName
      (.derivedDefinition .invariantLike dependsOn)
    `(term| (@$assembledInvariants $invArgs*))
  else
    `(term| (fun _ _ => $(mkIdent ``True)))

private def mkVCForSpecTheorem [Monad m] [MonadMacroAdapter m] [MonadExceptOf Exception m] [AddErrorMessageContext m] [MonadEnv m]
    [MonadRecDepth m] [MonadResolveName m] [MonadTrace m] [MonadOptions m]
    [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (propertyName : Name) (actKind : DeclarationKind)
    (specName : Name) (vcName : Name) (vcKind : InductionVCKind)
    (style : VCStyle := .wp) (extraDeps : Std.HashSet Name := {})
    (extraBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[])
    (extraTerms : Array Term := #[]) : m (VCData VCMetadata) := do
  -- FIXME: make all the name-related/parameter functions work with `ext` names
  let assumesInvariants := actKind.assumesInvariantsForInductionVC
  let baseDeps :=
    if assumesInvariants then
      #[actName, assembledAssumptionsName, assembledInvariantsName]
    else
      #[actName, assembledAssumptionsName]
  let dependsOn := extraDeps.insertMany baseDeps
  let (thmBaseParams, thmExtraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·)
    (.derivedDefinition .theoremLike dependsOn)
  -- NOTE: the VCs are stated in terms of `act.ext` (for WP) or `act.ext.tr` (for TR)
  let actionIdent := match style with
    | .wp => toExtName actName
    | .tr => toTransitionName (toExtName actName)
  let ((_, allModArgs), (actBinders, actArgs)) ← mod.declarationSplitBindersArgs actName actKind
  let (_, assArgs) ← mod.declarationAllBindersArgs assembledAssumptionsName
    (.derivedDefinition .assumptionLike dependsOn)
  let preTerm ← mkInductionPrecondition mod dependsOn assumesInvariants
  return {
    name := vcName,
    params := ← (thmBaseParams ++ thmExtraParams).mapM (·.binder),
    statement := ← expandTermMacro $ ← `(term|
      forall? $actBinders* $extraBinders*,
        $(mkIdent specName)
          (@$(mkIdent actionIdent) $allModArgs* $actArgs*)
          (@$assembledAssumptions $assArgs*)
          $preTerm
          $extraTerms:term*
    ),
    metadata := .induction {
      kind := vcKind,
      style := style,
      «action» := actName,
      property := propertyName,
      baseParams := thmBaseParams,
      extraParams := thmExtraParams,
      stmtDerivedFrom := dependsOn
    }
  }

private def mkDoesNotThrowVC [Monad m] [MonadMacroAdapter m] [MonadExceptOf Exception m] [AddErrorMessageContext m] [MonadEnv m]
    [MonadRecDepth m] [MonadResolveName m] [MonadTrace m] [MonadOptions m]
    [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : InductionVCKind)
    : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `doesNotThrow)
    ``VeilM.doesNotThrowAssuming_ex (Name.mkSimple s!"{actName}_doesNotThrow") vcKind
    (extraBinders := #[← `(bracketedBinder| ($exception:ident : ExId))])
    (extraTerms := #[← `(term| $exception:ident)])

private def mkMeetsSpecificationIfSuccessfulClauseVC [Monad m] [MonadMacroAdapter m] [MonadExceptOf Exception m] [AddErrorMessageContext m] [MonadEnv m] [MonadRecDepth m] [MonadResolveName m]
    [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (invariantClause : Name)
    (vcKind : InductionVCKind) : m (VCData VCMetadata) := do
  let extraDeps : Std.HashSet Name := {invariantClause}
  let extraTerms := #[← `(term|
    (@$(mkIdent invariantClause)
      $(← mod.declarationAllArgs invariantClause (.stateAssertion .invariant))*) )]
  mkVCForSpecTheorem mod actName (propertyName := invariantClause) actKind
    ``VeilM.meetsSpecificationIfSuccessfulAssuming
    (Name.mkSimple s!"{actName}_{invariantClause}") vcKind
    (extraDeps := extraDeps)
    (extraTerms := extraTerms)

private def mkPreservesInvariantsIfSuccessfulVC [Monad m] [MonadMacroAdapter m] [MonadExceptOf Exception m] [AddErrorMessageContext m]
    [MonadEnv m] [MonadRecDepth m] [MonadResolveName m] [MonadTrace m]
    [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : InductionVCKind)
    : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `preservesInvariants)
    ``VeilM.preservesInvariantsIfSuccessfulAssuming
    (Name.mkSimple s!"{actName}_preservesInvariants") vcKind

private def mkSucceedsAndInvariantsIfSuccessfulVC [Monad m] [MonadMacroAdapter m] [MonadExceptOf Exception m] [AddErrorMessageContext m]
    [MonadEnv m] [MonadRecDepth m] [MonadResolveName m] [MonadTrace m]
    [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : InductionVCKind)
    : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `succeedsAndPreservesInvariants)
    ``VeilM.succeedsAndPreservesInvariantsAssuming
    (Name.mkSimple s!"{actName}_succeedsAndPreservesInvariants") vcKind

/-- Generate a TR-style (transition-based) VC for checking if an action preserves
an invariant clause. For ordinary actions this is the fallback VC; for actions
defined with `transition`, this is the primary VC. -/
private def mkMeetsSpecificationIfSuccessfulClauseTrVC [Monad m] [MonadMacroAdapter m] [MonadExceptOf Exception m] [AddErrorMessageContext m] [MonadEnv m] [MonadRecDepth m] [MonadResolveName m]
    [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (invariantClause : Name)
    (vcKind : InductionVCKind) : m (VCData VCMetadata) := do
  let extraDeps : Std.HashSet Name := {invariantClause}
  let extraTerms := #[← `(term|
    (@$(mkIdent invariantClause)
      $(← mod.declarationAllArgs invariantClause (.stateAssertion .invariant))*) )]
  mkVCForSpecTheorem mod actName (propertyName := invariantClause) actKind
    ``Transition.meetsSpecificationIfSuccessfulAssuming
    (Name.mkSimple s!"{actName}_{invariantClause}_tr") vcKind
    (style := .tr) (extraDeps := extraDeps)
    (extraTerms := extraTerms)

/-! ## Module VC Generation -/

/-- Get the list of actions/initializers that need VC generation. -/
private def Module.actsToCheck (mod : Module) : Array ProcedureSpecification :=
  mod.procedures.filter (fun s => match s.info with
    | .action _ _ | .initializer => true
    | .procedure _ => false)

-- NOTE: This function could be the private helper of `elabProveVeilInvariantGoal`,
-- but it's here to use the `private` definitions in this module.
/-- Rebuild an interactive goal from the specification in the current environment,
using the same builders as automatic verification, rather than the mutable manager. -/
def Module.mkInvariantGoalVC (mod : Module) (actionId propertyId : Ident)
    (style : VCStyle) : CommandElabM (VCData VCMetadata) := do
  let some act := mod.actsToCheck.find? (·.name == actionId.getId)
    | throwErrorAt actionId "unknown action or initializer `{actionId.getId}`"
  if propertyId.getId == `doesNotThrow then
    unless style == .wp do
      throwErrorAt propertyId "`doesNotThrow` only supports `using wp`"
    return ← mkDoesNotThrowVC mod act.name act.declarationKind .primary
  unless mod.checkableInvariants.any (·.name == propertyId.getId) do
    throwErrorAt propertyId "unknown invariant `{propertyId.getId}`"
  match style with
  | .wp => mkMeetsSpecificationIfSuccessfulClauseVC mod act.name act.declarationKind propertyId.getId .primary
  | .tr => mkMeetsSpecificationIfSuccessfulClauseTrVC mod act.name act.declarationKind propertyId.getId .primary

/-- Generate doesNotThrow VCs for all actions.
    These VCs check that actions don't throw exceptions assuming the invariants hold. -/
def Module.generateDoesNotThrowVCs (mod : Module) : CommandElabM Unit := do
  let actsToCheck := mod.actsToCheck
  let wpTactic ← `(by veil_solve_wp_doesnotthrow)
  -- Prepare VC data outside the lock
  let vcData ← actsToCheck.mapM fun act =>
    mkDoesNotThrowVC mod act.name act.declarationKind InductionVCKind.primary
  -- Add all VCs atomically
  Verifier.withVCManager fun ref => do
    for vc in vcData do
      let mgr ← ref.get
      let (mgr, vcId) := mgr.addVC vc {} #[]
      let mgr ← mgr.mkAddDischarger vcId (VCDischarger.fromTerm wpTactic vc.metadata)
      ref.set mgr

/-- Generate invariant preservation VCs for all actions × invariant clauses.
    These VCs check that each action preserves each invariant clause. -/
def Module.generateInvariantVCs (mod : Module) : CommandElabM Unit := do
  let actsToCheck := mod.actsToCheck
  let wpTactic ← if mod._useLocalRPropTC then `(by veil_solve_wp) else `(by veil_solve_wp)
  let trTactic ← `(by veil_solve_tr)
  -- Prepare all VC data outside the lock
  let vcData ← actsToCheck.foldlM (init := #[]) fun acc act => do
    let clauseVCs ← mod.checkableInvariants.foldlM (init := #[]) fun acc' invClause => do
      let trPrimary := act.info.isTransition
      let wpVC ← mkMeetsSpecificationIfSuccessfulClauseVC mod act.name
        act.declarationKind invClause.name
        (if trPrimary then InductionVCKind.alternative else InductionVCKind.primary)
      let trVC ← mkMeetsSpecificationIfSuccessfulClauseTrVC mod act.name
        act.declarationKind invClause.name
        (if trPrimary then InductionVCKind.primary else InductionVCKind.alternative)
      return acc'.push (wpVC, trVC, trPrimary)
    return acc ++ clauseVCs
  -- Add all VCs atomically
  Verifier.withVCManager fun ref => do
    for (wpVC, trVC, trPrimary) in vcData do
      let mgr ← ref.get
      let mgr ←
        if trPrimary then do
          -- Actions written in `transition` syntax should be proved in their
          -- native two-state form first.  The WP VC still exists as the
          -- fallback, but it no longer drives the normal path for these actions.
          let (mgr, trVCId) := mgr.addVC trVC {} #[]
          let mgr ← mgr.mkAddDischarger trVCId (VCDischarger.fromTerm trTactic trVC.metadata)
          let (mgr, wpVCId) := mgr.addAlternativeVC wpVC trVCId #[]
          mgr.mkAddDischarger wpVCId (VCDischarger.fromTerm wpTactic wpVC.metadata)
        else do
          -- Ordinary actions keep the existing WP-first behavior.  TR remains a
          -- fallback counterexample/proof route if the WP VC fails.
          let (mgr, wpVCId) := mgr.addVC wpVC {} #[]
          let mgr ← mgr.mkAddDischarger wpVCId (VCDischarger.fromTerm wpTactic wpVC.metadata)
          let (mgr, trVCId) := mgr.addAlternativeVC trVC wpVCId #[]
          mgr.mkAddDischarger trVCId (VCDischarger.fromTerm trTactic trVC.metadata)
      ref.set mgr

/-- Generate all VCs (both doesNotThrow and invariant preservation). -/
def Module.generateVCs (mod : Module) : CommandElabM Unit := do
  mod.generateDoesNotThrowVCs
  mod.generateInvariantVCs

end Veil
