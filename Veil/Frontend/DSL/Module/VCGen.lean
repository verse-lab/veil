import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Util.Meta
import Veil.Core.Tools.Verifier.Server
import Veil.Frontend.DSL.Tactic

open Lean Elab Term Command

namespace Veil

def VCDischarger.fromTerm (term : Term) (vcStatement : VCStatement) (dischargerId : DischargerIdentifier) (ch : Std.Channel (ManagerNotification VeilResult)) (cancelTk? : Option IO.CancelToken := none) : CommandElabM (Discharger VeilResult) := do
  let cancelTk := cancelTk?.getD $ (Context.cancelTk? (← read)).getD (← IO.CancelToken.new)
  let mk ← Command.wrapAsync (fun vcStatement : VCStatement => do
    -- NOTE: `trace` here will never be displayed and `dbg_trace` will show up
    -- as errors in the LSP output
    -- dbg_trace "Starting discharger task for {vcStatement.name}"
    let res ← ( do
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
            let body ← withSynthesize $ elabTermEnsuringType term statementType
            let witness ← Meta.mkLambdaFVars vs body
            let endTime ← IO.monoMsNow
            -- dbg_trace "{endTime} @ thread {← IO.getTID} [Discharger] Successfully finished task for {vcStatement.name} in {endTime - startTime}ms"
            return .success witness Option.none (endTime - startTime)
      catch ex =>
        let endTime ← IO.monoMsNow
        -- dbg_trace "{endTime} @ thread {← IO.getTID} [Discharger] Failed task for {vcStatement.name} in {endTime - startTime}ms; exception: {← ex.toMessageData.toString}"
        -- TODO: identify SMT failure and get counter-example from the solver
        return .error ex (endTime - startTime))
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
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (actBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder) (specName : Name) (vcName : Name) (vcKind : VCKind)
  (extraDeps : Std.HashSet Name := {}) (extraTerms : Array Term := #[]): m (VCData VCMetadata) := do
  -- FIXME: make all the name-related/parameter functions work with `ext` names
  let dependsOn := extraDeps.insertMany #[actName, assembledAssumptionsName, assembledInvariantsName]
  let (thmBaseParams, thmExtraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .theoremLike dependsOn)
  -- NOTE: the VCs are stated in terms of `act.ext`, not `act`
  let extName := toExtName actName
  return {
    name := vcName,
    params := ← (thmBaseParams ++ thmExtraParams).mapM (·.binder),
    statement := ← expandTermMacro $ ← `(term|
      forall? $actBinders*,
        $(mkIdent specName)
          (@$(mkIdent extName) $(← mod.declarationAllParamsMapFn (·.arg) actName actKind)* $(← bracketedBindersToTerms actBinders)*)
          (@$assembledAssumptions $(← mod.declarationAllParamsMapFn (·.arg) assembledAssumptionsName (.derivedDefinition .assumptionLike dependsOn))*)
          (@$assembledInvariants $(← mod.declarationAllParamsMapFn (·.arg) assembledInvariantsName (.derivedDefinition .invariantLike dependsOn))*)
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
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (actBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder) (vcKind : VCKind) : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind actBinders ``VeilM.doesNotThrowAssuming (Name.mkSimple s!"{actName}_doesNotThrow") vcKind

private def mkMeetsSpecificationIfSuccessfulClauseVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (actBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder) (invariantClause : Name) (vcKind : VCKind) : m (VCData VCMetadata) := do
  let extraDeps := {invariantClause}
  let extraTerms := #[← `(term| (@$(mkIdent invariantClause) $(← mod.declarationAllParamsMapFn (·.arg) invariantClause (.stateAssertion .invariant))*) )]
  mkVCForSpecTheorem mod actName actKind actBinders ``VeilM.meetsSpecificationIfSuccessfulAssuming (Name.mkSimple s!"{actName}_{invariantClause}") vcKind extraDeps extraTerms

private def mkPreservesInvariantsIfSuccessfulVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (actBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder) (vcKind : VCKind) : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind actBinders ``VeilM.preservesInvariantsIfSuccessfulAssuming (Name.mkSimple s!"{actName}_preservesInvariants") vcKind

private def mkSucceedsAndInvariantsIfSuccessfulVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (actBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder) (vcKind : VCKind) : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind actBinders ``VeilM.succeedsAndPreservesInvariantsAssuming (Name.mkSimple s!"{actName}_succeedsAndPreservesInvariants") vcKind

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
    doesNotThrowVC ← Verifier.addVC ( ← mkDoesNotThrowVC mod act.name act.declarationKind (← act.binders) .primary) {}
    Verifier.mkAddDischarger doesNotThrowVC (VCDischarger.fromTerm $ ← `(by sorry))
    doesNotThrowVCs := doesNotThrowVCs.insert doesNotThrowVC

    -- Assuming the `Invariants`, this action preserves every invariant clause
    let mut clauseVCsForAct : Std.HashSet VCId := {}
    for invariantClause in mod.checkableInvariants do
      let mut clauseVC := default
      clauseVC ← Verifier.addVC ( ← mkMeetsSpecificationIfSuccessfulClauseVC mod act.name act.declarationKind (← act.binders) invariantClause.name .primary) {}
      Verifier.mkAddDischarger clauseVC (VCDischarger.fromTerm $ ← `(by veil_solve))
      clausesVCsByInv := clausesVCsByInv.insert invariantClause.name ((clausesVCsByInv.getD invariantClause.name {}).insert clauseVC)
      clauseVCsForAct := clauseVCsForAct.insert clauseVC

  --   -- Per-action overall invariant preservation VC
  --   let mut preservesInvariantsVC := default
  --   preservesInvariantsVC ← Verifier.addVC ( ← mkPreservesInvariantsIfSuccessfulVC mod act.name act.declarationKind (← act.binders) .derived) clauseVCsForAct
  --   preservesInvariantsVCs := preservesInvariantsVCs.insert preservesInvariantsVC

  --   let mut succeedsAndPreservesInvariantsVC := default
  --   succeedsAndPreservesInvariantsVC ← Verifier.addVC ( ← mkSucceedsAndInvariantsIfSuccessfulVC mod act.name act.declarationKind (← act.binders) .derived) {doesNotThrowVC, preservesInvariantsVC}
  --   succeedsAndPreservesInvariantsVCs := succeedsAndPreservesInvariantsVCs.insert succeedsAndPreservesInvariantsVC

  -- -- `NextAct` theorems
  -- let .some dd := mod._derivedDefinitions[assembledNextActName]?
  --   | throwError s!"[Module.generateVCs] derived definition {assembledNextActName} not found"
  -- let _ ← Verifier.addVC ( ← mkDoesNotThrowVC mod assembledNextActName dd.declarationKind (← dd.binders) .derived) doesNotThrowVCs

  -- for invariantClause in mod.checkableInvariants do
  --   let _ ← Verifier.addVC ( ← mkMeetsSpecificationIfSuccessfulClauseVC mod assembledNextActName dd.declarationKind (← dd.binders) invariantClause.name .derived) (clausesVCsByInv[invariantClause.name]!)
  -- let _ ← Verifier.addVC ( ← mkPreservesInvariantsIfSuccessfulVC mod assembledNextActName dd.declarationKind (← dd.binders) .derived) preservesInvariantsVCs
  -- let _ ← Verifier.addVC ( ← mkSucceedsAndInvariantsIfSuccessfulVC mod assembledNextActName dd.declarationKind (← dd.binders) .derived) succeedsAndPreservesInvariantsVCs

end Veil
