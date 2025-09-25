import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Util.Meta
import Veil.Core.Tools.Verifier.Server
import Veil.Frontend.DSL.Tactic

open Lean Elab Term Command

namespace Veil

private def collectSmtOutputs (ch : Std.CloseableChannel ((Name × ℕ) × Smt.AsyncOutput)) (expectedName : Name) : CoreM (Array SmtOutput) := do
  let _ ← ch.close
  let mut outputs := #[]
  while true do
    let Option.some ((name, index), output) := (← ch.recv).get | break
    if name != expectedName then
      throwError s!"Expected {expectedName}, got {name} from channel"
    outputs := outputs.push ((name, index), output)
  return outputs

private def overallSmtResult (name : Name) (outputs : Array SmtOutput) : CoreM (Option SmtResult) := do
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
      return .some $ .error errors
    if sat.size > 0 then
      return .some $ .sat sat
    if unknown.size > 0 then
      return .some $ .unknown unknown
    if errors.size == 0 && sat.size == 0 && unknown.size == 0 then
      return .some $ .unsat unsat
    return .none)
  -- dbg_trace "{name}: {errors.size} errors, {sat.size} sat, {unknown.size} unknown, {unsat.size} unsat -> {← (toMessageData res).toString}"
  return res

private def mkDischargerResult (expectedName : Name) (ch : Std.CloseableChannel ((Name × ℕ) × Smt.AsyncOutput)) (data : Witness ⊕ Exception) (time : Nat) : CoreM (DischargerResult SmtResult) := do
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
      | _ => throwError "mkDischargerResult: overallSmtResult is unsat, but no witness provided"
  | .none =>
    match data with
    | .inl witness => return .proven witness .none time
    | .inr ex => return .error #[ex] time

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
        -- dbg_trace "{← IO.monoMsNow} @ thread {← IO.getTID} [Discharger] Starting task for {vcStatement.name}"
        liftTermElabMWithBinders vcStatement.params fun vs => do
          /- We want to throw an error if anything fails or is missing during
          elaboration. -/
          withoutErrToSorry $ do
            -- dbg_trace "{← IO.monoMsNow} @ thread {← IO.getTID} [Discharger] Elaborating term for {vcStatement.name}"
            let statementType ← elabTermEnsuringType vcStatement.statement (Expr.sort levelZero)
            let _ ← Smt.initAsyncState dischargerId.name (.some smtCh)
            let body ← withSynthesize $ elabTermEnsuringType term statementType
            let witness ← Meta.mkLambdaFVars vs body
            let endTime ← IO.monoMsNow
            let dischargerResult ← mkDischargerResult dischargerId.name smtCh (.inl witness) (endTime - startTime)
            -- dbg_trace "{endTime} @ thread {← IO.getTID} [Discharger] Successfully finished task for {vcStatement.name} in {endTime - startTime}ms"
            return dischargerResult
      catch ex =>
        let endTime ← IO.monoMsNow
        let dischargerResult ← liftCoreM $  mkDischargerResult dischargerId.name smtCh (.inr ex) (endTime - startTime)
        -- dbg_trace "{endTime} @ thread {← IO.getTID} [Discharger] Failed task for {vcStatement.name} in {endTime - startTime}ms; exception: {← ex.toMessageData.toString}"
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
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (specName : Name) (vcName : Name) (vcKind : VCKind)
  (extraDeps : Std.HashSet Name := {}) (extraTerms : Array Term := #[]): m (VCData VCMetadata) := do
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
      baseParams := thmBaseParams,
      extraParams := thmExtraParams,
      stmtDerivedFrom := dependsOn
    }
  }

private def mkDoesNotThrowVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : VCKind) : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind ``VeilM.doesNotThrowAssuming (Name.mkSimple s!"{actName}_doesNotThrow") vcKind

private def mkMeetsSpecificationIfSuccessfulClauseVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (invariantClause : Name) (vcKind : VCKind) : m (VCData VCMetadata) := do
  let extraDeps := {invariantClause}
  let extraTerms := #[← `(term| (@$(mkIdent invariantClause) $(← mod.declarationAllArgs invariantClause (.stateAssertion .invariant))*) )]
  mkVCForSpecTheorem mod actName actKind ``VeilM.meetsSpecificationIfSuccessfulAssuming (Name.mkSimple s!"{actName}_{invariantClause}") vcKind extraDeps extraTerms

private def mkPreservesInvariantsIfSuccessfulVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : VCKind) : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind ``VeilM.preservesInvariantsIfSuccessfulAssuming (Name.mkSimple s!"{actName}_preservesInvariants") vcKind

private def mkSucceedsAndInvariantsIfSuccessfulVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : VCKind) : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind ``VeilM.succeedsAndPreservesInvariantsAssuming (Name.mkSimple s!"{actName}_succeedsAndPreservesInvariants") vcKind

def Module.generateVCs (mod : Module) : CommandElabM Unit := do
  -- We need to build the VCs "bottom-up", i.e. from the "smallest"
  -- statements to the "largest".
  let actsToCheck := mod.procedures.filter (fun s => match s.info with
    | .action _ | .initializer => true
    | .procedure _ => false)
  let mut doesNotThrowVCs : Std.HashSet VCId := {}
  let mut clausesVCsByInv : Std.HashMap Name (Std.HashSet VCId) := {}
  let mut preservesInvariantsVCs : Std.HashSet VCId := {}
  let mut succeedsAndPreservesInvariantsVCs : Std.HashSet VCId := {}
  -- Per-action checks
  for act in actsToCheck do
    -- The action does not throw any exceptions, assuming the `Invariants`
    let mut doesNotThrowVC := default
    doesNotThrowVC ← Verifier.addVC ( ← mkDoesNotThrowVC mod act.name act.declarationKind .primary) {}
    Verifier.mkAddDischarger doesNotThrowVC (VCDischarger.fromTerm $ ← `(by veil_solve))
    doesNotThrowVCs := doesNotThrowVCs.insert doesNotThrowVC

    -- Assuming the `Invariants`, this action preserves every invariant clause
    let mut clauseVCsForAct : Std.HashSet VCId := {}
    for invariantClause in mod.checkableInvariants do
      let mut clauseVC := default
      clauseVC ← Verifier.addVC ( ← mkMeetsSpecificationIfSuccessfulClauseVC mod act.name act.declarationKind invariantClause.name .primary) {}
      Verifier.mkAddDischarger clauseVC (VCDischarger.fromTerm $ ← `(by veil_solve))
      clausesVCsByInv := clausesVCsByInv.insert invariantClause.name ((clausesVCsByInv.getD invariantClause.name {}).insert clauseVC)
      clauseVCsForAct := clauseVCsForAct.insert clauseVC

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
