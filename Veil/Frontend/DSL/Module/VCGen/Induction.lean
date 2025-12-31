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
    | .inr ex => return .error #[(ex, s!"{← ex.toMessageData.toString}")] time

/-! ## VC Discharger -/

/-- Create a discharger for inductive verification conditions. -/
def VCDischarger.fromTerm (term : Term) (actName : Name) (vcStatement : VCStatement)
    (dischargerId : DischargerIdentifier)
    (ch : Std.Channel (ManagerNotification VCMetadata SmtResult))
    (cancelTk? : Option IO.CancelToken := none) : CommandElabM (Discharger SmtResult) := do
  let cancelTk := cancelTk?.getD $ (Context.cancelTk? (← read)).getD (← IO.CancelToken.new)
  let smtCh ← Std.CloseableChannel.new
  let mk ← Command.wrapAsync (fun vcStatement : VCStatement => do
    let res ← (do
      let startTime ← IO.monoMsNow
      try
        liftTermElabM $ do
          let _ ← Smt.initAsyncState dischargerId.name (.some smtCh)
          let witness ← instantiateMVars $ ← withSynthesize (postpone := .no) $
            withoutErrToSorry $ elabTermEnsuringType term (← vcStatement.type)
          let endTime ← IO.monoMsNow
          if witness.hasMVar || witness.hasFVar || witness.hasSyntheticSorry then
            throwError "unsolved goals"
          let dischargerResult ← mkDischargerResult dischargerId.name actName smtCh
            (.inl witness) (endTime - startTime)
          return dischargerResult
      catch ex =>
        let endTime ← IO.monoMsNow
        let dischargerResult ← liftTermElabM $ mkDischargerResult dischargerId.name actName smtCh
          (.inr ex) (endTime - startTime)
        return dischargerResult
      finally
        if ← cancelTk.isSet then
          pure ()
    )
    let _ ← ch.send (.dischargerResult dischargerId res)
    return res
  ) cancelTk
  let mkTask := EIO.asTask (mk vcStatement)
  return {
    id := dischargerId,
    term := term,
    cancelTk := cancelTk,
    task := Option.none,
    mkTask := mkTask
  }

/-! ## VC Statement Building -/

private def mkVCForSpecTheorem [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m]
    [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m]
    [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (propertyName : Name) (actKind : DeclarationKind)
    (specName : Name) (vcName : Name) (vcKind : InductionVCKind)
    (style : VCStyle := .wp) (extraDeps : Std.HashSet Name := {})
    (extraBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[])
    (extraTerms : Array Term := #[]) : m (VCData VCMetadata) := do
  -- FIXME: make all the name-related/parameter functions work with `ext` names
  let dependsOn := extraDeps.insertMany #[actName, assembledAssumptionsName, assembledInvariantsName]
  let (thmBaseParams, thmExtraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·)
    (.derivedDefinition .theoremLike dependsOn)
  -- NOTE: the VCs are stated in terms of `act.ext` (for WP) or `act.ext.tr` (for TR)
  let actionIdent := match style with
    | .wp => toExtName actName
    | .tr => toTransitionName (toExtName actName)
  let ((_, allModArgs), (actBinders, actArgs)) ← mod.declarationSplitBindersArgs actName actKind
  let (_, assArgs) ← mod.declarationAllBindersArgs assembledAssumptionsName
    (.derivedDefinition .assumptionLike dependsOn)
  let (_, invArgs) ← mod.declarationAllBindersArgs assembledInvariantsName
    (.derivedDefinition .invariantLike dependsOn)
  return {
    name := vcName,
    params := ← (thmBaseParams ++ thmExtraParams).mapM (·.binder),
    statement := ← expandTermMacro $ ← `(term|
      forall? $actBinders* $extraBinders*,
        $(mkIdent specName)
          (@$(mkIdent actionIdent) $allModArgs* $actArgs*)
          (@$assembledAssumptions $assArgs*)
          (@$assembledInvariants $invArgs*)
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

private def mkDoesNotThrowVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m]
    [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m]
    [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : InductionVCKind)
    : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `doesNotThrow)
    ``VeilM.doesNotThrowAssuming_ex (Name.mkSimple s!"{actName}_doesNotThrow") vcKind
    (extraBinders := #[← `(bracketedBinder| ($exception:ident : ExId))])
    (extraTerms := #[← `(term| $exception:ident)])

private def mkMeetsSpecificationIfSuccessfulClauseVC [Monad m] [MonadQuotation m]
    [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m]
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
    (extraDeps := extraDeps) (extraTerms := extraTerms)

private def mkPreservesInvariantsIfSuccessfulVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m]
    [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m]
    [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : InductionVCKind)
    : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `preservesInvariants)
    ``VeilM.preservesInvariantsIfSuccessfulAssuming
    (Name.mkSimple s!"{actName}_preservesInvariants") vcKind

private def mkSucceedsAndInvariantsIfSuccessfulVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m]
    [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m]
    [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : InductionVCKind)
    : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `succeedsAndPreservesInvariants)
    ``VeilM.succeedsAndPreservesInvariantsAssuming
    (Name.mkSimple s!"{actName}_succeedsAndPreservesInvariants") vcKind

/-- Generate a TR-style (transition-based) VC for checking if an action preserves
an invariant clause. This is an alternative to the WP-style VC and only runs
when the WP-style VC fails. -/
private def mkMeetsSpecificationIfSuccessfulClauseTrVC [Monad m] [MonadQuotation m]
    [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m]
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
    (style := .tr) (extraDeps := extraDeps) (extraTerms := extraTerms)

/-! ## Module VC Generation -/

def Module.generateVCs (mod : Module) : CommandElabM Unit := do
  -- We need to build the VCs "bottom-up", i.e. from the "smallest"
  -- statements to the "largest".
  let actsToCheck := mod.procedures.filter (fun s => match s.info with
    | .action _ _ | .initializer => true
    | .procedure _ => false)
  let wpTactic ← if mod._useLocalRPropTC then `(by veil_solve_wp !) else `(by veil_solve_wp)
  let trTactic ← `(by veil_solve_tr)
  let mut doesNotThrowVCs : Std.HashSet VCId := {}
  let mut clausesVCsByInv : Std.HashMap Name (Std.HashSet VCId) := {}
  -- let mut preservesInvariantsVCs : Std.HashSet VCId := {}
  -- let mut succeedsAndPreservesInvariantsVCs : Std.HashSet VCId := {}
  -- Per-action checks
  for act in actsToCheck do
    -- The action does not throw any exceptions, assuming the `Invariants`
    let mut doesNotThrowVC := default
    doesNotThrowVC ← Verifier.addVC ( ← mkDoesNotThrowVC mod act.name act.declarationKind InductionVCKind.primary) {}
    Verifier.mkAddDischarger doesNotThrowVC (VCDischarger.fromTerm wpTactic act.name)
    doesNotThrowVCs := doesNotThrowVCs.insert doesNotThrowVC

    -- Assuming the `Invariants`, this action preserves every invariant clause
    let mut clauseVCsForAct : Std.HashSet VCId := {}
    for invariantClause in mod.checkableInvariants do
      -- WP-style VC (primary)
      let mut clauseVC := default
      clauseVC ← Verifier.addVC ( ← mkMeetsSpecificationIfSuccessfulClauseVC mod act.name
        act.declarationKind invariantClause.name InductionVCKind.primary) {}
      Verifier.mkAddDischarger clauseVC (VCDischarger.fromTerm wpTactic act.name)
      clausesVCsByInv := clausesVCsByInv.insert invariantClause.name
        ((clausesVCsByInv.getD invariantClause.name {}).insert clauseVC)
      clauseVCsForAct := clauseVCsForAct.insert clauseVC

      -- TR-style VC (alternative) - only runs when WP-style VC fails
      let trVCData ← mkMeetsSpecificationIfSuccessfulClauseTrVC mod act.name
        act.declarationKind invariantClause.name InductionVCKind.alternative
      let trVC ← Verifier.addAlternativeVC trVCData clauseVC
      Verifier.mkAddDischarger trVC (VCDischarger.fromTerm trTactic act.name)

  --   -- Per-action overall invariant preservation VC
  --   let mut preservesInvariantsVC := default
  --   preservesInvariantsVC ← Verifier.addVC ( ← mkPreservesInvariantsIfSuccessfulVC mod act.name act.declarationKind .derived) clauseVCsForAct
  --   preservesInvariantsVCs := preservesInvariantsVCs.insert preservesInvariantsVC

  --   let mut succeedsAndPreservesInvariantsVC := default
  --   succeedsAndPreservesInvariantsVC ← Verifier.addVC ( ← mkSucceedsAndInvariantsIfSuccessfulVC mod act.name act.declarationKind .derived) {doesNotThrowVC, preservesInvariantsVC}
  --   succeedsAndPreservesInvariantsVCs := succeedsAndPreservesInvariantsVCs.insert succeedsAndPreservesInvariantsVC

  -- -- `NextAct` theorems
  -- let .some dd := mod._derivedDefinitions[assembledNextActName]?
  --   | throwError s!"[Module.generateVCs] derived definition {assembledNextActName} not found"
  -- let _ ← Verifier.addVC ( ← mkDoesNotThrowVC mod assembledNextActName dd.declarationKind  .derived) doesNotThrowVCs

  -- for invariantClause in mod.checkableInvariants do
  --   let _ ← Verifier.addVC ( ← mkMeetsSpecificationIfSuccessfulClauseVC mod assembledNextActName dd.declarationKind invariantClause.name .derived) (clausesVCsByInv[invariantClause.name]!)
  -- let _ ← Verifier.addVC ( ← mkPreservesInvariantsIfSuccessfulVC mod assembledNextActName dd.declarationKind .derived) preservesInvariantsVCs
  -- let _ ← Verifier.addVC ( ← mkSucceedsAndInvariantsIfSuccessfulVC mod assembledNextActName dd.declarationKind .derived) succeedsAndPreservesInvariantsVCs

end Veil
