module

public meta import Lean
public meta import Veil.Frontend.DSL.Module.Representation
public meta import Veil.Frontend.DSL.Module.Util
public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Frontend.DSL.Infra.Metadata
public meta import Veil.Util.Meta
public meta import Veil.Core.Tools.Verifier.Server
public import Veil.Frontend.DSL.Action.Semantics.Theorems
public meta import Veil.Frontend.DSL.Tactic
-- FIXME: it really doesn't make sense to import this here
public meta import Veil.Core.UI.Verifier.Model
public meta import Veil.Core.UI.Verifier.InductionCounterexample
public meta import Veil.Frontend.DSL.Module.VCGen.Common
public meta import Veil.Backend.Tactic.Frame

public meta section

/-!
# Induction VC Generation

This module provides VC generation for inductive invariant verification.
It handles the standard invariant preservation VCs for actions and initializers.
-/

open Lean Elab Term Command

namespace Veil

/-! ## Induction-Specific Result Processing -/

/-- Process SMT outputs and build counterexamples for inductive VCs. -/
private def overallSmtResult [Monad m] [MonadEnv m] [MonadError m] [MonadLiftT BaseIO m]
    [MonadLiftT MetaM m] (actName : Name) (outputs : Array SmtOutput) : m (Option SmtResult) := do
  let mod ← getCurrentModule
  buildSmtResult outputs (fun sat => do
    sat.filterMapM (fun ce => return ← ce.mapM (fun ce => do
      try
        let veilModel ← buildCounterexampleExprs ce mod actName
        let structuredJson : Json ← unsafe veilModel.toJson
        return .some { raw := ce, rawHtml := ← renderSmtModel ce, structuredJson := structuredJson }
      catch ex =>
        dbg_trace "Failed to build counterexample; exception: {← ex.toMessageData.toString}"
        return none)))

/-- Create a DischargerResult from SMT outputs for inductive VCs. -/
private def mkDischargerResult [Monad m] [MonadEnv m] [MonadError m] [MonadLiftT BaseIO m]
    [MonadLiftT (EIO Std.CloseableChannel.Error) m] [MonadLiftT MetaM m]
    (expectedName : Name) (actName : Name)
    (ch : Std.CloseableChannel ((Name × Nat) × Smt.AsyncOutput))
    (data : Witness ⊕ Exception) (time : Nat) : m (DischargerResult SmtResult) := do
  let outputs ← collectSmtOutputs ch expectedName
  let result ← overallSmtResult actName outputs
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
def VCDischarger.fromTerm (term : Term) (actName : Name) (vcStatement : VCStatement)
    (dischargerId : DischargerIdentifier)
    (nameSuffix : String := "")
    (ch : Std.Channel (ManagerNotification VCMetadata SmtResult))
    (_cancelTk? : Option IO.CancelToken := none) : CommandElabM (Discharger SmtResult) := do
  let dischargerId :=
    if nameSuffix.isEmpty then dischargerId
    else { dischargerId with name := Name.mkSimple s!"{dischargerId.name.getString!}{nameSuffix}" }
  -- Proof inlining only needs declarations, not mutable runtime handles.
  let env0 := Veil.Verifier.clearVerifierRuntime (← getEnv)
  Discharger.fromTermWith term vcStatement dischargerId ch fun smtCh data time => do
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
    mkDischargerResult dischargerId.name actName smtCh data time

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
    (style : VCStyle := .wp) (isAssertionCheck := false) (extraDeps : Std.HashSet Name := {})
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
      isAssertionCheck := isAssertionCheck,
      baseParams := thmBaseParams,
      extraParams := thmExtraParams,
      stmtDerivedFrom := dependsOn
    }
  }

/-- Actions and initializers for which the verifier builds obligations. -/
private def Module.actsToCheck (mod : Module) : Array ProcedureSpecification :=
  mod.procedures.filter (fun s => match s.info with
    | .action _ _ | .initializer => true
    | .procedure _ => false)

private def assertionTheoremName (actName : Name) : Name :=
  Name.mkSimple s!"{actName}_doesNotThrow"

private abbrev InvariantTheoremNames := Std.HashMap (Name × Name × VCStyle) Name

/-- Keep the familiar theorem names wherever they are unique. Assertion checks take
priority, followed by WP proofs and then their TR companions. Reserve every preferred
name before assigning numeric suffixes so a collision cannot displace an unrelated VC. -/
private def Module.invariantTheoremNames (mod : Module) : InvariantTheoremNames := Id.run do
  let actions := mod.actsToCheck.map (·.name)
  let clauses := mod.checkableInvariants.map (·.name)
  let mut used : Std.HashSet Name := .ofList (actions.toList.map assertionTheoremName)
  let mut reserved := used
  let mut goals := #[]
  for style in [VCStyle.wp, .tr] do
    for actName in actions do
      for clause in clauses do
        let name := Name.mkSimple s!"{actName}_{clause}{if style == .tr then "_tr" else ""}"
        reserved := reserved.insert name
        goals := goals.push ((actName, clause, style), name)
  let mut names := {}
  for (key, preferred) in goals do
    let mut name := preferred
    if used.contains name then
      let mut i := 1
      repeat
        name := preferred.appendAfter s!"_{i}"
        if !reserved.contains name && !used.contains name then break
        i := i + 1
    used := used.insert name
    names := names.insert key name
  return names

private def mkDoesNotThrowVC [Monad m] [MonadMacroAdapter m] [MonadExceptOf Exception m] [AddErrorMessageContext m] [MonadEnv m]
    [MonadRecDepth m] [MonadResolveName m] [MonadTrace m] [MonadOptions m]
    [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : InductionVCKind)
    : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `doesNotThrow)
    ``VeilM.doesNotThrowAssuming_ex (assertionTheoremName actName) vcKind
    (isAssertionCheck := true)
    (extraBinders := #[← `(bracketedBinder| ($exception:ident : Int))])
    (extraTerms := #[← `(term| $exception:ident)])

private def mkInvariantClauseVC (mod : Module) (names : InvariantTheoremNames) (actName : Name)
    (actKind : DeclarationKind) (invariantClause : Name) (style : VCStyle)
    (vcKind : InductionVCKind) : CommandElabM (VCData VCMetadata) := do
  let extraDeps : Std.HashSet Name := {invariantClause}
  let extraTerms := #[← `(term|
    (@$(mkIdent invariantClause)
      $(← mod.declarationAllArgs invariantClause (.stateAssertion .invariant))*) )]
  let specName := match style with
    | .wp => ``VeilM.meetsSpecificationIfSuccessfulAssuming
    | .tr => ``Transition.meetsSpecificationIfSuccessfulAssuming
  mkVCForSpecTheorem mod actName (propertyName := invariantClause) actKind
    specName names[(actName, invariantClause, style)]! vcKind style
    (extraDeps := extraDeps) (extraTerms := extraTerms)

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

/-! ## Module VC Generation -/

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
  mkInvariantClauseVC mod mod.invariantTheoremNames act.name act.declarationKind propertyId.getId style .primary

/-- Generate doesNotThrow VCs for all actions.
    These VCs check that actions don't throw exceptions assuming the invariants hold. -/
def Module.generateDoesNotThrowVCs (mod : Module) : CommandElabM Unit := do
  let actsToCheck := mod.actsToCheck
  let wpTactic ← `(by veil_solve_wp_doesnotthrow)
  -- Prepare VC data outside the lock
  let vcData ← actsToCheck.mapM fun act =>
    return (act, ← mkDoesNotThrowVC mod act.name act.declarationKind InductionVCKind.primary)
  -- Add all VCs atomically
  Verifier.withVCManager fun ref => do
    for (act, vc) in vcData do
      let mgr ← ref.get
      let (mgr, vcId) := mgr.addVC vc {} #[]
      let mgr ← mgr.mkAddDischarger vcId (VCDischarger.fromTerm wpTactic act.name (nameSuffix := "_WP"))
      ref.set mgr

/-- WP clauses try framing first. TR clauses go directly to the TR solver. -/
private def addInvariantDischargers (mgr : VCManager VCMetadata SmtResult) (id : VCId)
    (vc : VCData VCMetadata) (frame : FrameDischarger) : CommandElabM (VCManager VCMetadata SmtResult) := do
  let .induction info := vc.metadata | throwError "expected an induction VC"
  match info.style with
  | .wp =>
    let mgr ← if veil.frame.get (← getOptions) then
      mgr.addProofDischarger id (← `(by veil_frame)) "FRAME" (some (frame.proveInvariant vc))
    else pure mgr
    mgr.mkAddDischarger id (VCDischarger.fromTerm (← `(by veil_solve_wp)) info.action (nameSuffix := "_WP"))
  | .tr =>
    mgr.mkAddDischarger id (VCDischarger.fromTerm (← `(by veil_solve_tr)) info.action (nameSuffix := "_TR"))

/-- Transport the proof under exactly the module and action parameters shared
by the two VC statements. Locality proofs are required only when converting a
WP proof to a TR proof for an action declared with `transition`. -/
private def convertInvariantProof (externalAction : Name) (nativeTransition : Bool)
    (sourceStyle : VCStyle) (source statement : Expr) : TermElabM Expr :=
  Meta.forallTelescope statement fun xs goal => do
    let h := mkAppN source xs
    let trGoal ← if sourceStyle == .wp then pure goal else Meta.inferType h
    let proof ← match_expr trGoal with
      | Transition.meetsSpecificationIfSuccessfulAssuming _ _ tr assu pre post => do
        let trName := toTransitionName externalAction
        if nativeTransition then
          let trTerm ← exprToSyntax tr
          let sourceProof ← exprToSyntax h
          let term ← match sourceStyle with
            | .tr => `(term| Transition.wp_of_invariant $trTerm $sourceProof)
            | .wp => `(term| Transition.invariant_of_wp $trTerm $sourceProof
                (by intros; simp only [$(mkIdent trName):ident, decide_eq_true_eq, substateSimp])
                (by intros; simp only [invSimp, substateSimp]))
          withoutErrToSorry <| elabTermAndSynthesize term goal
        else
          let derived := mkAppN (mkConst (toDerivedEqName externalAction)) tr.getAppArgs
          let iff ← Meta.mkAppM ``VeilM.invariant_iff_transition #[derived, assu, pre, post]
          Meta.mkAppM (if sourceStyle == .wp then ``Iff.mp else ``Iff.mpr) #[iff, h]
      | _ => throwError "expected a transition invariant for `{externalAction}`, got{indentExpr trGoal}"
    Meta.mkLambdaFVars xs (← instantiateMVars proof)

/-- Generate invariant preservation VCs for all actions × invariant clauses.
    These VCs check that each action preserves each invariant clause. -/
def Module.generateInvariantVCs (mod : Module) : CommandElabM Unit := do
  let actsToCheck := mod.actsToCheck
  let names := mod.invariantTheoremNames
  -- Build the statements outside the manager lock.
  let vcData ← actsToCheck.foldlM (init := #[]) fun acc act => do
    let frame ← FrameDischarger.forAction act.info
    let trPrimary := act.info.isTransition
    let mut result := acc
    for invClause in mod.checkableInvariants do
      let wpVC ← mkInvariantClauseVC mod names act.name act.declarationKind invClause.name .wp
        (if trPrimary then InductionVCKind.alternative else InductionVCKind.primary)
      let trVC ← mkInvariantClauseVC mod names act.name act.declarationKind invClause.name .tr
        (if trPrimary then InductionVCKind.primary else InductionVCKind.alternative)
      let convert := convertInvariantProof (mod.name ++ toExtName act.name) trPrimary
      let wpVariant := { trVC.toVCStatement with ofProof := convert .wp : VCTheoremVariant }
      let trVariant := { wpVC.toVCStatement with ofProof := convert .tr : VCTheoremVariant }
      let wpVC := { wpVC with variant? := some wpVariant }
      let trVC := { trVC with variant? := some trVariant }
      -- Relational actions try TR first; ordinary actions and initializers try WP first.
      let (primary, alternative) := if trPrimary then (trVC, wpVC) else (wpVC, trVC)
      result := result.push (primary, alternative, frame)
    return result
  Verifier.withVCManager fun ref => do
    for (primary, alternative, frame) in vcData do
      let (mgr, id) := (← ref.get).addVC primary {} #[]
      let mgr ← addInvariantDischargers mgr id primary frame
      let (mgr, altId) := mgr.addAlternativeVC alternative id #[]
      ref.set (← addInvariantDischargers mgr altId alternative frame)

/-- Generate all VCs (both doesNotThrow and invariant preservation). -/
def Module.generateVCs (mod : Module) : CommandElabM Unit := do
  mod.generateDoesNotThrowVCs
  mod.generateInvariantVCs

end Veil
