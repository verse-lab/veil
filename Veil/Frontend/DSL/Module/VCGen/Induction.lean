module

public meta import Lean
public meta import Veil.Frontend.DSL.Module.Representation
public meta import Veil.Frontend.DSL.Module.Util
public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Frontend.DSL.Infra.Metadata
public meta import Veil.Util.Meta
public meta import Veil.Core.Tools.Verifier.Server
public meta import Veil.Frontend.DSL.Tactic
public meta import Veil.Frontend.DSL.Tactic.InvSet
-- FIXME: it really doesn't make sense to import this here
public meta import Veil.Core.UI.Verifier.Model
public meta import Veil.Core.UI.Verifier.InductionCounterexample
public meta import Veil.Frontend.DSL.Module.VCGen.Common

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
        -- Internal procedures have no external dispatch label. Preserve the
        -- raw solver model for a contract failure rather than attempting to
        -- manufacture a nonexistent `Label.procedure` constructor.
        if actName != initializerName && !mod.actions.any (·.name == actName) then
          return some {
            raw := ce, rawHtml := ← renderSmtModel ce,
            structuredJson := Json.mkObj [("kind", toJson "contract"),
              ("procedure", toJson actName)] }
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
  let env0 ← getEnv
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
    (style : VCStyle := .wp) (extraDeps : Std.HashSet Name := {})
    (extraBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[])
    (extraTerms : Array Term := #[])
    (contractOwner : Option Name := none)
    (contractAssumesInvariants : Bool := false) : m (VCData VCMetadata) := do
  -- FIXME: make all the name-related/parameter functions work with `ext` names
  let assumesInvariants := if contractOwner.isSome then contractAssumesInvariants
    else actKind.assumesInvariantsForInductionVC
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
      «action» := contractOwner.getD actName,
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

/-- Generate doesNotThrow VCs for all actions.
    These VCs check that actions don't throw exceptions assuming the invariants hold. -/
def Module.generateDoesNotThrowVCs (mod : Module) : CommandElabM Unit := do
  let actsToCheck := mod.actsToCheck
  -- Prepare VC data outside the lock
  let vcData ← actsToCheck.mapM fun act => do
    let support? ← mod.invSetSupportForAction act.name
    let wpTactic ← match support? with
      | none => `(by veil_solve_wp_doesnotthrow)
      | some support => do
          let ids := support.map mkIdent
          if act.info.isTransition then
            -- Native transitions enumerate concrete represented states;
            -- they do not have the imperative local-WP equality bridge.
            `(by
              veil_restrict_invset_pre [$[$ids:ident],*]
              veil_intros
              __veil_solve_wp_conservative)
          else
            `(by
              veil_restrict_invset_pre [$[$ids:ident],*]
              veil_apply_local_wp
              __veil_solve_wplo)
    return (act, ← mkDoesNotThrowVC mod act.name act.declarationKind InductionVCKind.primary, wpTactic)
  -- Add all VCs atomically
  Verifier.withVCManager fun ref => do
    for (act, vc, wpTactic) in vcData do
      let mgr ← ref.get
      let (mgr, vcId) := mgr.addVC vc {} #[]
      let mgr ← mgr.mkAddDischarger vcId (VCDischarger.fromTerm wpTactic act.name (nameSuffix := "_WP"))
      ref.set mgr

/-- Procedure contracts quantify over arbitrary states satisfying their
explicit leading requirements and immutable assumptions. External-action
certificates may additionally require the boundary invariant conjunction;
that premise remains explicit in their theorem type. -/
private def Module.generateCompanionVCs (mod : Module) (suffix : Name) : CommandElabM Unit := do
  -- The verification-only Unit view calls the real implementation internally;
  -- its local WP bridge supports the same field abstraction as action VCs.
  let mut vcs := #[]
  for proc in mod.procedures do
    let contractName := proc.name ++ suffix
    let some contract := mod.procedures.find? (·.name == contractName) | continue
    let support? ← match proc.info with
      | .action _ _ => mod.invSetSupportForAction proc.name
      | _ => pure none
    let tactic ← match support? with
      | none => `(by veil_solve_wp_doesnotthrow)
      | some support => do
          let ids := support.map mkIdent
          if proc.info.isTransition then
            -- Keep the native method's concrete-state semantics, including
            -- frame assertions, under exactly the selected precondition.
            `(by
              veil_restrict_invset_pre [$[$ids:ident],*]
              veil_intros
              __veil_solve_wp_conservative)
          else
            `(by
              veil_restrict_invset_pre [$[$ids:ident],*]
              veil_apply_local_wp
              __veil_solve_wplo)
    let vc ← mkVCForSpecTheorem mod contract.name
      (propertyName := suffix) contract.declarationKind
      ``VeilM.doesNotThrowAssuming_ex (Name.mkSimple s!"{proc.name}_{suffix}")
      InductionVCKind.primary
      (extraBinders := #[← `(bracketedBinder| ($exception:ident : ExId))])
      (extraTerms := #[← `(term| $exception:ident)])
      (contractOwner := some proc.name)
      (contractAssumesInvariants := match proc.info with | .action _ _ => true | _ => false)
    vcs := vcs.push (proc.name, vc, tactic)
  Verifier.withVCManager fun ref => do
    for (proc, vc, tactic) in vcs do
      let mgr ← ref.get
      let (mgr, vcId) := mgr.addVC vc {} #[]
      let mgr ← mgr.mkAddDischarger vcId (VCDischarger.fromTerm tactic proc (nameSuffix := s!"_{suffix}_WP"))
      ref.set mgr

def Module.generateContractVCs (mod : Module) : CommandElabM Unit :=
  mod.generateCompanionVCs `contract

/-- Every instantiated method must prove that its complete implementation,
including opaque helper effects, leaves foreign owned fields unchanged. -/
def Module.generateFrameVCs (mod : Module) : CommandElabM Unit :=
  mod.generateCompanionVCs `frame

/-- Generate invariant preservation VCs for all actions × invariant clauses.
    These VCs check that each action preserves each invariant clause. -/
def Module.generateInvariantVCs (mod : Module) : CommandElabM Unit := do
  let actsToCheck := mod.actsToCheck
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
      let support? ← if act.info == .initializer then pure none
        else mod.invSetSupportFor invClause.name
      let (wpTactic, trTactic) ← match support? with
        | none => pure (← `(by veil_solve_wp), ← `(by veil_solve_tr))
        | some support => do
          let ids := support.map mkIdent
          let wpTactic ← `(by
            veil_restrict_invset_pre [$[$ids:ident],*]
            veil_apply_local_wp
            __veil_solve_wplo)
          let trTactic ← `(by
            veil_restrict_invset_pre [$[$ids:ident],*]
            veil_apply_local_tr
            __veil_solve_trlo)
          pure (wpTactic, trTactic)
      return acc'.push (act, wpVC, trVC, trPrimary, wpTactic, trTactic)
    return acc ++ clauseVCs
  -- Add all VCs atomically
  Verifier.withVCManager fun ref => do
    for (act, wpVC, trVC, trPrimary, wpTactic, trTactic) in vcData do
      let mgr ← ref.get
      let mgr ←
        if trPrimary then do
          -- Actions written in `transition` syntax should be proved in their
          -- native two-state form first.  The WP VC still exists as the
          -- fallback, but it no longer drives the normal path for these actions.
          let (mgr, trVCId) := mgr.addVC trVC {} #[]
          let mgr ← mgr.mkAddDischarger trVCId (VCDischarger.fromTerm trTactic act.name (nameSuffix := "_TR"))
          let (mgr, wpVCId) := mgr.addAlternativeVC wpVC trVCId #[]
          mgr.mkAddDischarger wpVCId (VCDischarger.fromTerm wpTactic act.name (nameSuffix := "_WP"))
        else do
          -- Ordinary actions keep the existing WP-first behavior.  TR remains a
          -- fallback counterexample/proof route if the WP VC fails.
          let (mgr, wpVCId) := mgr.addVC wpVC {} #[]
          let mgr ← mgr.mkAddDischarger wpVCId (VCDischarger.fromTerm wpTactic act.name (nameSuffix := "_WP"))
          let (mgr, trVCId) := mgr.addAlternativeVC trVC wpVCId #[]
          mgr.mkAddDischarger trVCId (VCDischarger.fromTerm trTactic act.name (nameSuffix := "_TR"))
      ref.set mgr

/-- Generate all VCs (both doesNotThrow and invariant preservation). -/
def Module.generateVCs (mod : Module) : CommandElabM Unit := do
  mod.generateDoesNotThrowVCs
  mod.generateContractVCs
  mod.generateFrameVCs
  mod.generateInvariantVCs

end Veil
