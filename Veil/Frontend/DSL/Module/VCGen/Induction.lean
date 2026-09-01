import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Infra.Metadata
import Veil.Util.Meta
import Veil.Core.Tools.Verifier.Server
import Veil.Frontend.DSL.Tactic
-- FIXME: it really doesn't make sense to import this here
import Veil.Core.UI.Verifier.Model
import Veil.Core.UI.Verifier.InductionCounterexample
import Veil.Frontend.DSL.Module.VCGen.Common

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

/-- Create a discharger for inductive verification conditions.

`attempt > 0` marks a retry discharger (see `veil.smt.retries`): the manager
only schedules it after an earlier attempt of the same VC timed out
(`VerificationCondition.nextDischarger?`). The perturbed solver configuration
is expected to be baked into `term` itself (via `set_option ... in`), so
witness regeneration replays it unchanged. -/
def VCDischarger.fromTerm (term : Term) (actName : Name) (vcStatement : VCStatement)
    (dischargerId : DischargerIdentifier)
    (nameSuffix : String := "")
    (attempt : Nat := 0)
    (ch : Std.Channel (ManagerNotification VCMetadata SmtResult))
    (_cancelTk? : Option IO.CancelToken := none) : CommandElabM (Discharger SmtResult) := do
  let dischargerId :=
    if nameSuffix.isEmpty then dischargerId
    else { dischargerId with name := Name.mkSimple s!"{dischargerId.name.getString!}{nameSuffix}" }
  let env0 ← getEnv
  let discharger ← Discharger.fromTermWith term vcStatement dischargerId ch fun smtCh data time => do
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
  return { discharger with attempt := attempt }

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

/-- Retry variants of a discharge tactic, per `veil.smt.retries`: attempt `k`
re-runs `tac` with the solver seed set to `k` and the short
`veil.smt.retryTimeout` budget. The perturbed options are baked into the
returned `by` term via `set_option ... in`, so lazy witness regeneration
(`#gen_theorems`) replays exactly the configuration that succeeded. -/
private def mkRetryTerms [Monad m] [MonadQuotation m] [MonadOptions m]
    (tac : TSyntax `tactic) : m (Array (Nat × Term)) := do
  let opts ← getOptions
  let retryTimeout := Syntax.mkNatLit (veil.smt.retryTimeout.get opts)
  (Array.range (veil.smt.retries.get opts)).mapM fun i => do
    let k := i + 1
    let seed := Syntax.mkNatLit k
    let term ← `(term| by
      set_option veil.smt.seed $seed:num in
      set_option veil.smt.timeout $retryTimeout:num in
      $tac:tactic)
    return (k, term)

/-- Add `retryTerms` (from `mkRetryTerms`) as retry dischargers of `vcId`. -/
private def VCManager.addRetryDischargers
    (mgr : VCManager VCMetadata SmtResult) (vcId : VCId) (actName : Name)
    (nameSuffix : String) (retryTerms : Array (Nat × Term))
    : CommandElabM (VCManager VCMetadata SmtResult) :=
  retryTerms.foldlM (init := mgr) fun mgr (k, term) =>
    mgr.mkAddDischarger vcId (VCDischarger.fromTerm term actName
      (nameSuffix := s!"{nameSuffix}_retry{k}") (attempt := k))

/-- Generate doesNotThrow VCs for all actions.
    These VCs check that actions don't throw exceptions assuming the invariants hold. -/
def Module.generateDoesNotThrowVCs (mod : Module) : CommandElabM Unit := do
  let actsToCheck := mod.actsToCheck
  let wpSolve ← `(tactic| veil_solve_wp_doesnotthrow)
  let wpTactic ← `(by $wpSolve:tactic)
  let wpRetries ← mkRetryTerms wpSolve
  -- Prepare VC data outside the lock
  let vcData ← actsToCheck.mapM fun act =>
    return (act, ← mkDoesNotThrowVC mod act.name act.declarationKind InductionVCKind.primary)
  -- Add all VCs atomically
  Verifier.withVCManager fun ref => do
    for (act, vc) in vcData do
      let mgr ← ref.get
      let (mgr, vcId) := mgr.addVC vc {} #[]
      let mgr ← mgr.mkAddDischarger vcId (VCDischarger.fromTerm wpTactic act.name (nameSuffix := "_WP"))
      let mgr ← mgr.addRetryDischargers vcId act.name "_WP" wpRetries
      ref.set mgr

/-- Generate invariant preservation VCs for all actions × invariant clauses.
    These VCs check that each action preserves each invariant clause. -/
def Module.generateInvariantVCs (mod : Module) : CommandElabM Unit := do
  let actsToCheck := mod.actsToCheck
  let wpSolve ← `(tactic| veil_solve_wp)
  let trSolve ← `(tactic| veil_solve_tr)
  let wpTactic ← `(by $wpSolve:tactic)
  let trTactic ← `(by $trSolve:tactic)
  let wpRetries ← mkRetryTerms wpSolve
  let trRetries ← mkRetryTerms trSolve
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
      return acc'.push (act, wpVC, trVC, trPrimary)
    return acc ++ clauseVCs
  -- Add all VCs atomically
  Verifier.withVCManager fun ref => do
    for (act, wpVC, trVC, trPrimary) in vcData do
      let mgr ← ref.get
      let mgr ←
        if trPrimary then do
          -- Actions written in `transition` syntax should be proved in their
          -- native two-state form first.  The WP VC still exists as the
          -- fallback, but it no longer drives the normal path for these actions.
          let (mgr, trVCId) := mgr.addVC trVC {} #[]
          let mgr ← mgr.mkAddDischarger trVCId (VCDischarger.fromTerm trTactic act.name (nameSuffix := "_TR"))
          let mgr ← mgr.addRetryDischargers trVCId act.name "_TR" trRetries
          let (mgr, wpVCId) := mgr.addAlternativeVC wpVC trVCId #[]
          let mgr ← mgr.mkAddDischarger wpVCId (VCDischarger.fromTerm wpTactic act.name (nameSuffix := "_WP"))
          mgr.addRetryDischargers wpVCId act.name "_WP" wpRetries
        else do
          -- Ordinary actions keep the existing WP-first behavior.  TR remains a
          -- fallback counterexample/proof route if the WP VC fails.
          let (mgr, wpVCId) := mgr.addVC wpVC {} #[]
          let mgr ← mgr.mkAddDischarger wpVCId (VCDischarger.fromTerm wpTactic act.name (nameSuffix := "_WP"))
          let mgr ← mgr.addRetryDischargers wpVCId act.name "_WP" wpRetries
          let (mgr, trVCId) := mgr.addAlternativeVC trVC wpVCId #[]
          let mgr ← mgr.mkAddDischarger trVCId (VCDischarger.fromTerm trTactic act.name (nameSuffix := "_TR"))
          mgr.addRetryDischargers trVCId act.name "_TR" trRetries
      ref.set mgr

/-- Generate all VCs (both doesNotThrow and invariant preservation). -/
def Module.generateVCs (mod : Module) : CommandElabM Unit := do
  mod.generateDoesNotThrowVCs
  mod.generateInvariantVCs

end Veil
