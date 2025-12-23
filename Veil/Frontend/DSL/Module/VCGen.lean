import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Util.Meta
import Veil.Core.Tools.Verifier.Server
import Veil.Frontend.DSL.Tactic
-- FIXME: it really doesn't make sense to import this here
import Veil.Core.UI.Verifier.Model

open Lean Elab Term Command

namespace Veil

private def collectSmtOutputs [Monad m] [MonadError m] [MonadLiftT BaseIO m] [MonadLiftT (EIO Std.CloseableChannel.Error) m] (ch : Std.CloseableChannel ((Name × ℕ) × Smt.AsyncOutput)) (expectedName : Name) : m (Array SmtOutput) := do
  -- Calling `close` will throw an exception if the channel is already closed.
  -- We ignore it here because we want to continue with our logic.
  try let _ ← ch.close catch _ => pure ()
  let mut outputs := #[]
  while true do
    let Option.some ((name, index), output) := (← ch.recv).get | break
    if name != expectedName then
      let s := s!"Expected {expectedName}, got {name} from channel"
      dbg_trace s; throwError s
    outputs := outputs.push ((name, index), output)
  return outputs

private def overallSmtResult [Monad m] [MonadLiftT BaseIO m] [MonadLiftT MetaM m] (_name : Name) (outputs : Array SmtOutput) : m (Option SmtResult) := do
  let mut (errors, sat, unknown, unsat) := (#[], #[], #[], #[])
  for output in outputs do
    match output with
    | (_, .exception ex) => errors := errors.push ex
    | (_, .result (.sat ce)) => sat := sat.push ce
    | (_, .result (.unknown reason)) => unknown := unknown.push reason
    | (_, .result (.unsat _ core)) => unsat := unsat.push core
    | _ => pure ()
  let res ← (do
    if errors.size > 0 then
      return .some $ .error (← errors.mapM (fun ex => do return (ex, toJson (← ex.toMessageData.toString))))
    if sat.size > 0 then
      return .some $ .sat (← sat.mapM (fun ce => return ← ce.mapM (fun ce => return (ce, ← renderSmtModel ce))))
    if unknown.size > 0 then
      return .some $ .unknown unknown
    if errors.size == 0 && sat.size == 0 && unknown.size == 0 && unsat.size > 0 then
      return .some $ .unsat unsat
    -- the SMT solver wasn't involved in proving this goal
    return .none)
  -- dbg_trace "{_name}: {errors.size} errors, {sat.size} sat, {unknown.size} unknown, {unsat.size} unsat -> {← (toMessageData res).toString}"
  return res

private def mkDischargerResult [Monad m] [MonadError m] [MonadLiftT BaseIO m] [MonadLiftT (EIO Std.CloseableChannel.Error) m] [MonadLiftT MetaM m] (expectedName : Name) (ch : Std.CloseableChannel ((Name × ℕ) × Smt.AsyncOutput)) (data : Witness ⊕ Exception) (time : Nat) : m (DischargerResult SmtResult) := do
  let outputs ← collectSmtOutputs ch expectedName
  let result ← overallSmtResult expectedName outputs
  match result with
  | .some result => match result with
    | .error exs => return .error exs time
    | .sat _ => return .disproven result time
    | .unknown _ => return .unknown result time
    | .unsat _ => do
      match data with
      | .inl witness => return .proven witness result time
      | _ =>
        let s := "mkDischargerResult: overallSmtResult is unsat, but no witness provided"
        dbg_trace s; throwError s
  | .none =>
    match data with
    | .inl witness => return .proven witness .none time
    | .inr ex => return .error #[(ex, s!"{← ex.toMessageData.toString}")] time

def VCDischarger.fromTerm (term : Term) (vcStatement : VCStatement) (dischargerId : DischargerIdentifier) (ch : Std.Channel (ManagerNotification SmtResult)) (cancelTk? : Option IO.CancelToken := none) : CommandElabM (Discharger SmtResult) := do
  let cancelTk := cancelTk?.getD $ (Context.cancelTk? (← read)).getD (← IO.CancelToken.new)
  let smtCh ← Std.CloseableChannel.new
  let mk ← Command.wrapAsync (fun vcStatement : VCStatement => do
    -- NOTE: `trace` here will never be displayed and `dbg_trace` will show up
    -- as errors in the LSP output
    -- dbg_trace "Starting discharger task for {vcStatement.name}"
    let res ← (do
      /- We wrap in `try`/`catch` because we want to reify exceptions ourselves
      into `DischargerResult` -/
      let startTime ← IO.monoMsNow
      try
      liftTermElabM $ do
        -- dbg_trace "{← IO.monoMsNow} @ thread {← IO.getTID} [Discharger] Elaborating term for {vcStatement.name}"
        let _ ← Smt.initAsyncState dischargerId.name (.some smtCh)
        -- FIXME: how to properly check that this elaborated correctly?
        let witness ← instantiateMVars $ ← withSynthesize (postpone := .no) $
          withoutErrToSorry $ elabTermEnsuringType term (← vcStatement.type)
        let endTime ← IO.monoMsNow
        if witness.hasMVar || witness.hasFVar || witness.hasSyntheticSorry then
          -- dbg_trace "{dischargerId.name}: provided term does not solve the VC (has mvars: {witness.hasMVar} | has fvars: {witness.hasFVar} | has synthetic sorry: {witness.hasSyntheticSorry})"
          throwError "unsolved goals"
        let dischargerResult ← mkDischargerResult dischargerId.name smtCh (.inl witness) (endTime - startTime)
        -- dbg_trace "{endTime} @ thread {← IO.getTID} [Discharger] Successfully finished task for {vcStatement.name} in {endTime - startTime}ms"
        return dischargerResult
      catch ex =>
        let endTime ← IO.monoMsNow
        -- dbg_trace "{endTime} @ thread {← IO.getTID} [Discharger] Failed task for {vcStatement.name} in {endTime - startTime}ms; exception: {← ex.toMessageData.toString}"
        let dischargerResult ← liftTermElabM $ mkDischargerResult dischargerId.name smtCh (.inr ex) (endTime - startTime)
        return dischargerResult
      finally
        if ← cancelTk.isSet then
          pure ()
          -- dbg_trace "{← IO.monoMsNow} @ thread {← IO.getTID} [Discharger] Task {dischargerId} was cancelled"
    )
    -- Send the result to the VCManager
    -- dbg_trace "Sending result for {vcStatement.name}: {← (toMessageData res).toString}"
    let _ ← ch.send (.dischargerResult dischargerId res)
    -- And also record it in the task for good measure
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

private def mkVCForSpecTheorem [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (propertyName : Name) (actKind : DeclarationKind) (specName : Name) (vcName : Name) (vcKind : VCKind)
  (extraDeps : Std.HashSet Name := {}) (extraTerms : Array Term := #[]) : m (VCData VCMetadata) := do
  -- FIXME: make all the name-related/parameter functions work with `ext` names
  let dependsOn := extraDeps.insertMany #[actName, assembledAssumptionsName, assembledInvariantsName]
  let (thmBaseParams, thmExtraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .theoremLike dependsOn)
  -- NOTE: the VCs are stated in terms of `act.ext`, not `act`
  let extName := toExtName actName
  let ((_, allModArgs), (actBinders, actArgs)) ← mod.declarationSplitBindersArgs actName actKind
  let (_, assArgs) ← mod.declarationAllBindersArgs assembledAssumptionsName (.derivedDefinition .assumptionLike dependsOn)
  let (_, invArgs) ← mod.declarationAllBindersArgs assembledInvariantsName (.derivedDefinition .invariantLike dependsOn)
  return {
    name := vcName,
    params := ← (thmBaseParams ++ thmExtraParams).mapM (·.binder),
    statement := ← expandTermMacro $ ← `(term|
      forall? $actBinders*,
        $(mkIdent specName)
          (@$(mkIdent extName) $allModArgs* $actArgs*)
          (@$assembledAssumptions $assArgs*)
          (@$assembledInvariants $invArgs*)
          $extraTerms:term*
    ),
    metadata := {
      kind := vcKind,
      style := .wp,
      «action» := actName,
      property := propertyName,
      baseParams := thmBaseParams,
      extraParams := thmExtraParams,
      stmtDerivedFrom := dependsOn
    }
  }

private def mkDoesNotThrowVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : VCKind) : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `doesNotThrow) ``VeilM.doesNotThrowAssuming (Name.mkSimple s!"{actName}_doesNotThrow") vcKind

private def mkMeetsSpecificationIfSuccessfulClauseVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (invariantClause : Name) (vcKind : VCKind) : m (VCData VCMetadata) := do
  let extraDeps := {invariantClause}
  let extraTerms := #[← `(term| (@$(mkIdent invariantClause) $(← mod.declarationAllArgs invariantClause (.stateAssertion .invariant))*) )]
  mkVCForSpecTheorem mod actName actKind (propertyName := invariantClause) ``VeilM.meetsSpecificationIfSuccessfulAssuming (Name.mkSimple s!"{actName}_{invariantClause}") vcKind extraDeps extraTerms

private def mkPreservesInvariantsIfSuccessfulVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : VCKind) : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `preservesInvariants) ``VeilM.preservesInvariantsIfSuccessfulAssuming (Name.mkSimple s!"{actName}_preservesInvariants") vcKind

private def mkSucceedsAndInvariantsIfSuccessfulVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : VCKind) : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `succeedsAndPreservesInvariants) ``VeilM.succeedsAndPreservesInvariantsAssuming (Name.mkSimple s!"{actName}_succeedsAndPreservesInvariants") vcKind

/-- Generate a TR-style (transition-based) VC for a specification theorem.
This is similar to `mkVCForSpecTheorem` but uses the transition (`act.ext.tr`)
instead of the VeilM action (`act.ext`). -/
private def mkVCForSpecTheoremTr [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (propertyName : Name) (actKind : DeclarationKind) (specName : Name) (vcName : Name) (vcKind : VCKind)
  (extraDeps : Std.HashSet Name := {}) (extraTerms : Array Term := #[]) : m (VCData VCMetadata) := do
  let dependsOn := extraDeps.insertMany #[actName, assembledAssumptionsName, assembledInvariantsName]
  let (thmBaseParams, thmExtraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .theoremLike dependsOn)
  -- For TR-style VCs, we use the transition name: act.ext.tr
  let trName := toTransitionName (toExtName actName)
  let ((_, allModArgs), (actBinders, actArgs)) ← mod.declarationSplitBindersArgs actName actKind
  let (_, assArgs) ← mod.declarationAllBindersArgs assembledAssumptionsName (.derivedDefinition .assumptionLike dependsOn)
  let (_, invArgs) ← mod.declarationAllBindersArgs assembledInvariantsName (.derivedDefinition .invariantLike dependsOn)
  return {
    name := vcName,
    params := ← (thmBaseParams ++ thmExtraParams).mapM (·.binder),
    statement := ← expandTermMacro $ ← `(term|
      forall? $actBinders*,
        $(mkIdent specName)
          (@$(mkIdent trName) $allModArgs* $actArgs*)
          (@$assembledAssumptions $assArgs*)
          (@$assembledInvariants $invArgs*)
          $extraTerms:term*
    ),
    metadata := {
      kind := vcKind,
      style := .tr,
      «action» := actName,
      property := propertyName,
      baseParams := thmBaseParams,
      extraParams := thmExtraParams,
      stmtDerivedFrom := dependsOn
    }
  }

/-- Generate a TR-style (transition-based) VC for checking if an action preserves
an invariant clause. This is an alternative to the WP-style VC and only runs
when the WP-style VC fails. -/
private def mkMeetsSpecificationIfSuccessfulClauseTrVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (invariantClause : Name) (vcKind : VCKind) : m (VCData VCMetadata) := do
  let extraDeps := {invariantClause}
  let extraTerms := #[← `(term| (@$(mkIdent invariantClause) $(← mod.declarationAllArgs invariantClause (.stateAssertion .invariant))*) )]
  mkVCForSpecTheoremTr mod actName (propertyName := invariantClause) actKind ``Transition.meetsSpecificationIfSuccessfulAssuming (Name.mkSimple s!"{actName}_{invariantClause}_tr") vcKind extraDeps extraTerms

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
    doesNotThrowVC ← Verifier.addVC ( ← mkDoesNotThrowVC mod act.name act.declarationKind .primary) {}
    Verifier.mkAddDischarger doesNotThrowVC (VCDischarger.fromTerm wpTactic)
    doesNotThrowVCs := doesNotThrowVCs.insert doesNotThrowVC

    -- Assuming the `Invariants`, this action preserves every invariant clause
    let mut clauseVCsForAct : Std.HashSet VCId := {}
    for invariantClause in mod.checkableInvariants do
      -- WP-style VC (primary)
      let mut clauseVC := default
      clauseVC ← Verifier.addVC ( ← mkMeetsSpecificationIfSuccessfulClauseVC mod act.name act.declarationKind invariantClause.name .primary) {}
      Verifier.mkAddDischarger clauseVC (VCDischarger.fromTerm wpTactic)
      clausesVCsByInv := clausesVCsByInv.insert invariantClause.name ((clausesVCsByInv.getD invariantClause.name {}).insert clauseVC)
      clauseVCsForAct := clauseVCsForAct.insert clauseVC

      -- TR-style VC (alternative) - only runs when WP-style VC fails
      let trVCData ← mkMeetsSpecificationIfSuccessfulClauseTrVC mod act.name act.declarationKind invariantClause.name .alternative
      let trVC ← Verifier.addAlternativeVC trVCData clauseVC
      Verifier.mkAddDischarger trVC (VCDischarger.fromTerm trTactic)

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
