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

/-- Canonical generated theorem/VC name for a WP-style induction obligation. -/
def inductionTheoremName (actName propertyName : Name) : Name :=
  Name.mkSimple s!"{actName}_{propertyName}"

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
  -- let cancelTk := cancelTk?.getD $ (Context.cancelTk? (← read)).getD (← IO.CancelToken.new)
  let cancelTk ← IO.CancelToken.new
  let smtCh ← Std.CloseableChannel.new
  -- Create promises to track start time and result
  let startTimePromise ← IO.Promise.new
  let resultPromise ← IO.Promise.new
  let env0 ← getEnv
  -- Use wrapAsyncAsSnapshot for proper snapshot tree integration with the language server
  let mk ← Command.wrapAsyncAsSnapshot (fun vcStatement : VCStatement => do
    -- Wrap in profiler trace for discharger timing
    withTraceNode (`veil.perf.discharger ++ dischargerId.name)
        (fun _ => return s!"discharger {dischargerId.name}") do
      let res ← (do
        -- Resolve the start time promise when the discharger actually begins
        let startTime ← IO.monoMsNow
        startTimePromise.resolve startTime
        try
          liftTermElabM $ do
            let _ ← Smt.initAsyncState dischargerId.name (.some smtCh)
            let witness ← instantiateMVars $ ← withSynthesize (postpone := .no) $
              withoutErrToSorry $ elabTermEnsuringType term (← vcStatement.type)
            let witness ← inlineFreshProofs env0 witness
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
      -- Resolve the result promise so Discharger.status can read it
      resultPromise.resolve res
      -- Send notification to manager
      let _ ← ch.send (.dischargerResult dischargerId res)
      -- Note: wrapAsyncAsSnapshot expects Unit, so no return value
  ) cancelTk
  let mkTask := (mk vcStatement).asTask
  return {
    id := dischargerId,
    term := term,
    cancelTk := cancelTk,
    task := Option.none,
    startTimePromise := startTimePromise,
    resultPromise := resultPromise,
    mkTask := mkTask
  }

/-! ## VC Statement Building -/

private def DeclarationKind.assumesInvariantsForInductionVC : DeclarationKind → Bool
  | .procedure .initializer => false
  | _ => true

private def mkInductionPrecondition [Monad m] [MonadQuotation m] [MonadError m]
    (mod : Module) (dependsOn : Std.HashSet Name) (assumesInvariants : Bool) : m Term := do
  if assumesInvariants then
    let (_, invArgs) ← mod.declarationAllBindersArgs assembledInvariantsName
      (.derivedDefinition .invariantLike dependsOn)
    `(term| (@$assembledInvariants $invArgs*))
  else
    `(term| (fun _ _ => $(mkIdent ``True)))

private def mkVCForSpecTheorem [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m]
    [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m]
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

private def mkDoesNotThrowVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m]
    [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m]
    [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : InductionVCKind)
    : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `doesNotThrow)
    ``VeilM.doesNotThrowAssuming_ex (inductionTheoremName actName `doesNotThrow) vcKind
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
    (inductionTheoremName actName invariantClause) vcKind
    (extraDeps := extraDeps)
    (extraTerms := extraTerms)

private def mkPreservesInvariantsIfSuccessfulVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m]
    [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m]
    [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : InductionVCKind)
    : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `preservesInvariants)
    ``VeilM.preservesInvariantsIfSuccessfulAssuming
    (inductionTheoremName actName `preservesInvariants) vcKind

private def mkSucceedsAndInvariantsIfSuccessfulVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m]
    [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m]
    [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : InductionVCKind)
    : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `succeedsAndPreservesInvariants)
    ``VeilM.succeedsAndPreservesInvariantsAssuming
    (inductionTheoremName actName `succeedsAndPreservesInvariants) vcKind

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
    (trTheoremName actName invariantClause) vcKind
    (style := .tr) (extraDeps := extraDeps)
    (extraTerms := extraTerms)

/-! ## Module VC Generation -/

/-- Get the list of actions/initializers that need VC generation. -/
private def Module.actsToCheck (mod : Module) : Array ProcedureSpecification :=
  mod.procedures.filter (fun s => match s.info with
    | .action _ _ | .initializer => true
    | .procedure _ => false)

def primaryWpInductionVCKey (actName propertyName : Name) : InductionVCKey :=
  { actionName := actName, property := propertyName, style := .wp, kind := .primary }

/-- Expected primary WP VCs for a finalized module.
Checking primaries is enough because invariant TR alternatives are added atomically with their primaries. -/
def Module.expectedPrimaryInductionVCKeys (mod : Module) : Array InductionVCKey :=
  mod.actsToCheck.flatMap fun act =>
    #[primaryWpInductionVCKey act.name `doesNotThrow] ++
      mod.checkableInvariants.map (fun inv => primaryWpInductionVCKey act.name inv.name)

/-- Generate doesNotThrow VCs for all actions.
    These VCs check that actions don't throw exceptions assuming the invariants hold. -/
def Module.generateDoesNotThrowVCs (mod : Module) : CommandElabM Unit := do
  let actsToCheck := mod.actsToCheck
  let wpTactic ← if mod._useLocalRPropTC then `(by veil_solve_wp) else `(by veil_solve_wp)
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

/-- Generate invariant preservation VCs for all actions × invariant clauses.
    These VCs check that each action preserves each invariant clause. -/
def Module.generateInvariantVCs (mod : Module) : CommandElabM Unit := do
  let actsToCheck := mod.actsToCheck
  -- Prepare all VC data outside the lock
  let vcData ← actsToCheck.foldlM (init := #[]) fun acc act => do
    let clauseVCs ← mod.checkableInvariants.foldlM (init := #[]) fun acc' invClause => do
      let wpVC ← mkMeetsSpecificationIfSuccessfulClauseVC mod act.name
        act.declarationKind invClause.name InductionVCKind.primary
      let trVC ← mkMeetsSpecificationIfSuccessfulClauseTrVC mod act.name
        act.declarationKind invClause.name InductionVCKind.alternative
      return acc'.push (act, wpVC, trVC)
    return acc ++ clauseVCs
  -- Add all VCs atomically
  Verifier.withVCManager fun ref => do
    for (_act, wpVC, trVC) in vcData do
      let mgr ← ref.get
      -- WP-style VC (primary)
      let (mgr, wpVCId) := mgr.addVC wpVC {} #[]
      -- TR-style VC (alternative) - only runs when WP-style VC fails
      let (mgr, _trVCId) := mgr.addAlternativeVC trVC wpVCId #[]
      ref.set mgr

private def restrictedWpTactic (support : Array Name) : CommandElabM Term := do
  let supportIds := support.map mkIdent
  `(by
    veil_intros
    veil_wp
    veil_enforce_invset_support [$[$supportIds],*]
    veil_concretize_wp
    veil_fol
    veil_solve)

private def restrictedTrTactic (support : Array Name) : CommandElabM Term := do
  let supportIds := support.map mkIdent
  `(by
    veil_intros
    veil_simp only [$(mkIdent `actSimp):ident] at *
    veil_enforce_invset_support [$[$supportIds],*]
    veil_simp only [$(mkIdent `invSimp):ident] at *
    veil_simp only [$(mkIdent `ifSimp):ident] at *
    veil_destruct only [$(mkIdent ``Exists):ident, $(mkIdent ``And):ident]
    veil_split_ifs
    all_goals (veil_concretize_tr; veil_fol; veil_solve))

private def wpTacticForSupport (support? : Option (Array Name)) : CommandElabM Term := do
  match support? with
  | some support => restrictedWpTactic support
  | none => `(by veil_solve_wp)

private def trTacticForSupport (support? : Option (Array Name)) : CommandElabM Term := do
  match support? with
  | some support => restrictedTrTactic support
  | none => `(by veil_solve_tr)

private def shouldAttachInvariantDischarger (filter : VCMetadata → Bool) : VerificationCondition VCMetadata SmtResult → Bool
  | vc =>
    if !filter vc.metadata then
      false
    else
      match vc.metadata with
      | .induction m => m.property != `doesNotThrow
      | .trace _ => false

def Module.attachInvariantDischargers (_mod : Module) (filter : VCMetadata → Bool)
    (support? : Option (Array Name) := none) : CommandElabM Unit := do
  let wpTactic ← wpTacticForSupport support?
  let trTactic ← trTacticForSupport support?
  Verifier.withVCManager fun ref => do
    let mut mgr ← ref.get
    for (vcId, vc) in mgr.nodes.toArray do
      unless shouldAttachInvariantDischarger filter vc do
        continue
      match vc.metadata with
      | .induction indMeta =>
        let tactic ← if indMeta.action == initializerName then
          match indMeta.style with
          | .wp => `(by veil_solve_wp)
          | .tr => `(by veil_solve_tr)
        else
          match indMeta.style with
          | .wp => pure wpTactic
          | .tr => pure trTactic
        let suffix := match indMeta.style with
          | .wp => "_WP"
          | .tr => "_TR"
        mgr ← mgr.mkAddDischarger vcId (VCDischarger.fromTerm tactic indMeta.action (nameSuffix := suffix))
      | .trace _ => pure ()
    ref.set mgr

/-- Generate all VCs (both doesNotThrow and invariant preservation). -/
def Module.generateVCs (mod : Module) : CommandElabM Unit := do
  mod.generateDoesNotThrowVCs
  mod.generateInvariantVCs

end Veil
