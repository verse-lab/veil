module

public meta import Veil.Frontend.DSL.Infra.TraceSyntax
public meta import Lean
public meta import Lean.Parser
public meta import Veil.Util.Meta
public meta import Veil.Frontend.DSL.Module.Util.Assertions
public meta import Veil.Frontend.DSL.Module.Names
public meta import Veil.Frontend.DSL.Util
public meta import Veil.Core.Tools.ModelChecker.TransitionSystem
public meta import Veil.Core.Tools.Verifier.Server
public meta import Veil.Core.Tools.Verifier.Results
public meta import Veil.Frontend.DSL.Module.VCGen
public meta import Veil.Core.UI.Trace.TraceDisplay
public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import ProofWidgets.Component.HtmlDisplay
public meta import Veil.Core.UI.Widget.RefreshComponent
public meta import Veil.Frontend.DSL.Module.Elaborators.Verification
public meta import Veil.Util.StreamingInfo

public meta section

/-!
  # Symbolic Trace Language

  This file defines the syntax and elaboration for symbolic model checking
  queries like `sat trace` and `unsat trace`.

  ## Example usage:

  ```lean4
  -- Automatic: registers with VCManager and runs SMT
  sat trace [can_elect_leader] {
    any 3 actions
    send
    assert (∃ l, leader l)
  }

  unsat trace {
    any 6 actions
    assert ¬ (leader L → le N L)
  }

  -- Manual: generates a theorem for debugging
  sat trace [debug_trace] {
    send
    recv
  } by { bmc_sat }
  ```
-/

namespace Veil
open Lean Elab Command Term Meta ProofWidgets RefreshComponent

/-- A single line in a trace specification -/
inductive TraceSpecLine
  | action : Name → TraceSpecLine
  | anyAction : TraceSpecLine
  | anyNActions : Nat → TraceSpecLine
  | assertion : Term → TraceSpecLine
deriving Inhabited, Repr

instance : ToString TraceSpecLine := ⟨fun
  | TraceSpecLine.action n => s!"action {n}"
  | TraceSpecLine.anyAction => "any action"
  | TraceSpecLine.anyNActions n => s!"any {n} actions"
  | TraceSpecLine.assertion t => s!"assertion {t}"⟩

abbrev TraceSpec := List TraceSpecLine

def parseTraceSpec [Monad m] [MonadError m] (stx : Syntax) : m TraceSpec := do
  match stx with
  | `(traceSpec| $[$ts]* ) => do
    let mut ts ← ts.mapM fun t => match t with
      | `(traceLine| any action) | `(traceLine| * ) => return TraceSpecLine.anyAction
      | `(traceLine| any $n:num actions) => do
        if n.getNat < 2 then throwErrorAt stx "any {n} actions: n must be >= 2"
        return TraceSpecLine.anyNActions n.getNat
      | `(traceLine| assert $term) => return TraceSpecLine.assertion term
      | `(traceLine| $id:ident) => return TraceSpecLine.action id.raw.getId
      | _ => throwErrorAt stx "unsupported syntax"
    return ts.toList
  | _ => throwUnsupportedSyntax

/-- Accumulated binders during trace spec elaboration -/
structure BinderAccum where
  params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  tags : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]

instance : Append BinderAccum where
  append a b := { params := a.params ++ b.params, tags := a.tags ++ b.tags }

def BinderAccum.all (acc : BinderAccum) : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) :=
  acc.tags ++ acc.params

/-- Build the transition expression: `tag = tagMember ∧ rts.tr th st label st'` -/
private def mkTransitionExpr (rtsExpr theoryId currState nextState : TSyntax `term)
    (tagId : Ident) (actionName : Name) (argIdents : Array Ident) : TermElabM (TSyntax `term) := do
  let actionTagMember ← `($actionTagEnumInst.$(mkIdent actionName))
  let labelConstructor := mkIdent $ labelTypeName ++ actionName
  let labelExpr ← `(term| ($labelConstructor $argIdents*))
  let trExpr ← `(term| (($rtsExpr).$(mkIdent `tr) $theoryId $currState $labelExpr $nextState))
  `(term| ($tagId = $actionTagMember ∧ $trExpr))

/-- Build a disjunction representing any action transition with ActionTag constraint -/
private def mkAnyActionDisjunction (mod : Module) (rtsExpr theoryId currState nextState : TSyntax `term)
    (tagId : Ident) (trIdx : Nat) : TermElabM (Term × Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  let results ← mod.actions.mapIdxM fun idx act => do
    let (_, specificParams) ← mod.declarationAllParams act.name act.declarationKind
    let (argIdents, binders) ← mkTransitionParamBinders trIdx idx specificParams.size
    return (← mkTransitionExpr rtsExpr theoryId currState nextState tagId act.name argIdents, binders)
  return (← repeatedOr (results.map (·.1)), results.flatMap (·.2))

/-- Collect module-level binders (sorts, user parameters, sort assumptions, user-defined typeclasses) -/
def traceModuleParams (mod : Module) : Array Parameter := Id.run do
  let typeclassParams := mod.parameters.filter fun p =>
    match p.kind with
    | .moduleTypeclass .sortAssumption | .moduleTypeclass .userDefined => true
    | _ => false
  return mod.uninterpretedParameters ++ typeclassParams

/-- State threaded through trace spec elaboration -/
structure TraceElabState where
  /-- Remaining state identifiers (head is current state) -/
  states : List Ident
  /-- Transition counter for unique naming -/
  trIdx : Nat := 1
  /-- Accumulated assertions -/
  assertions : Array (TSyntax `term) := #[]
  /-- The same constraints specialized to one concrete label per step. -/
  replayAssertions : Array Term := #[]
  replayLabels : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  /-- Accumulated binders -/
  binders : BinderAccum := {}

/-- Get current and next state, returning updated state list -/
def TraceElabState.advance (s : TraceElabState) : Option (Ident × Ident × TraceElabState) :=
  match s.states with
  | curr :: next :: rest => some (curr, next, { s with states := next :: rest, trIdx := s.trIdx + 1 })
  | _ => none

/-- Context for trace elaboration (immutable during processing) -/
structure TraceElabCtx where
  mod : Module
  tagType : Ident
  rtsExpr : TSyntax `term
  theoryId : TSyntax `term
  theoryT : TSyntax `term
  stateT : TSyntax `term
  sorts : Array Ident

/-- Process a transition (specific or any action), returning assertion and binders -/
private def processTransition (ctx : TraceElabCtx) (curr next : Ident) (trIdx : Nat)
    : TraceSpecLine → TermElabM (TSyntax `term × BinderAccum)
  | .action actionName => do
    let idx? := ctx.mod.actions.findIdx? (·.name == actionName)
    let some idx := idx? | throwError s!"action '{actionName}' not found. Available: {ctx.mod.actions.map (·.name)}"
    let act := ctx.mod.actions[idx]!
    let (_, specificParams) ← ctx.mod.declarationAllParams act.name act.declarationKind
    let (tagId, tagBinder) ← mkTransitionTagBinder ctx.tagType trIdx
    let (argIdents, paramBinders) ← mkTransitionParamBinders trIdx idx specificParams.size
    return (← mkTransitionExpr ctx.rtsExpr ctx.theoryId curr next tagId actionName argIdents,
            { params := paramBinders, tags := #[tagBinder] })
  | .anyAction => do
    let (tagId, tagBinder) ← mkTransitionTagBinder ctx.tagType trIdx
    let (disjunction, paramBinders) ← mkAnyActionDisjunction ctx.mod ctx.rtsExpr ctx.theoryId curr next tagId trIdx
    return (disjunction, { params := paramBinders, tags := #[tagBinder] })
  | _ => unreachable!

scoped syntax "veil_trace_assertion% " term:max : term

elab_rules : term <= expectedType
  | `(veil_trace_assertion% $assertion) => do
    let mod ← getCurrentModule
    let firstTree := (← getInfoTrees).size
    let value ← withSaveInfoContext <| elabTerm assertion expectedType
    mod.warnTermShadows assertion firstTree
    pure value

/-- Process a user assertion (no state transition) -/
private def processAssertion (ctx : TraceElabCtx) (currState : Ident) (t : Term) : TermElabM (TSyntax `term) := do
  let fieldRepInstance ← `(term| $instAbstractFieldRepresentation $(ctx.sorts)*)
  let stateSortTerm ← `(term| $fieldAbstractDispatcher $(ctx.sorts)*)
  let wrappedTerm ← withTheoryAndStateFn ctx.mod (← `(uqc% (($t:term):Prop))) (some $ ← `(term|Prop)) ctx.theoryT ctx.stateT fieldRepInstance stateSortTerm
  let assertion ← `(term|($wrappedTerm $(ctx.theoryId) $currState))
  let assertion := Syntax.inheritSourceSpanFrom assertion t
  `(term|veil_trace_assertion% $assertion)

/-- Expand anyNActions into individual anyAction entries -/
private def expandTraceLine : TraceSpecLine → List TraceSpecLine
  | .anyNActions k => List.replicate k .anyAction
  | other => [other]

open Lean.Parser.Term in
/-- Process a single trace spec line, returning updated state -/
private def processLine (ctx : TraceElabCtx) (s : TraceElabState) : TraceSpecLine → TermElabM TraceElabState
  | .assertion t => do
    let curr := s.states.head!
    let assertion ← processAssertion ctx curr t
    return { s with assertions := s.assertions.push assertion,
                    replayAssertions := s.replayAssertions.push assertion }
  | line => do  -- .action or .anyAction
    let (curr, next, s') ← s.advance.getDM (throwError "insufficient states for transition")
    let (assertion, newBinders) ← processTransition ctx curr next s.trIdx line
    let label ← Lean.mkIdent <$> mkFreshUserName `label
    let binder ← `(bracketedBinder| ($label : $labelType $(ctx.sorts)*))
    let edge ← `(($(ctx.rtsExpr)).tr $(ctx.theoryId) $curr $label $next)
    let edge ← match line with
      | .action actionName => `((($label matches $(mkIdent (labelTypeName ++ actionName)):ident ..) = true) ∧ $edge)
      | _ => pure edge
    return { s' with
      assertions := s'.assertions.push assertion, binders := s'.binders ++ newBinders
      replayAssertions := s'.replayAssertions.push edge, replayLabels := s'.replayLabels.push binder }

/-- Extract structured JSON trace from a discharger result (if SAT). -/
private def extractTraceJson? (result : Option (DischargerResult SmtResult)) : Option Json :=
  match result with
  | some (.proven _ (some (.sat counterexamples)) _)
  | some (.disproven (some (.sat counterexamples)) _) =>
    counterexamples.findSome? fun ce? => ce?.map (·.structuredJson)
  | _ => none

/-- Extract structured JSON trace and raw HTML from a discharger result (if SAT). -/
private def extractTraceData? (result : Option (DischargerResult SmtResult)) : Option (Json × Option Html) :=
  match result with
  | some (.proven _ (some (.sat counterexamples)) _)
  | some (.disproven (some (.sat counterexamples)) _) =>
    counterexamples.findSome? fun ce? => ce?.map (fun ce => (ce.structuredJson, some ce.rawHtml))
  | _ => none

/-- Log all errors from discharger results. -/
private def logDischargerErrors (dischargers : Array (DischargerResultData SmtResult)) : CommandElabM Unit := do
  for d in dischargers do
    if let some (.error exs _) := d.result then
      for (ex, _) in exs do logError ex.toMessageData

/-- Extract trace JSON from a VCResult's discharger results. -/
private def extractTraceJsonFromVC (vcResult : VCResult VCMetadata SmtResult) : Option Json :=
  vcResult.timing.dischargers.findSome? (extractTraceJson? ·.result)

/-- Extract trace JSON and raw HTML from a VCResult's discharger results. -/
private def extractTraceDataFromVC (vcResult : VCResult VCMetadata SmtResult) : Option (Json × Option Html) :=
  vcResult.timing.dischargers.findSome? (extractTraceData? ·.result)

/-- Check if we expect a trace based on query type and result. -/
private def shouldHaveTrace (isExpectedSat : Bool) (status : Option VCStatus) : Bool :=
  (isExpectedSat && status == some .proven) || (!isExpectedSat && status == some .disproven)

/-- Format a trace result status as a simple message (for widget display without trace JSON). -/
private def formatTraceStatus (isExpectedSat : Bool) (status : Option VCStatus) : String :=
  match status with
  | some .proven => if isExpectedSat then "Found satisfying trace" else "No counterexample found (as expected)"
  | some .disproven => if isExpectedSat then "No satisfying trace exists" else "Counterexample found"
  | some .unknown => "Solver returned unknown"
  | some .error => "Verification error"
  | some .timeout => "Solver timed out"
  | none => "Verification did not complete"

private def traceLoadingMessage : String := "⏳ Verifying trace query..."

private partial def runTraceRefreshStep (owner : VCManagerEnvironment) (getManager : BaseIO (VCManager VCMetadata SmtResult)) (managerId : ManagerId) (isExpectedSat : Bool) (_vcName : Name)
    (vcFilter : VCMetadata → Bool) (token : RefreshToken) : CoreM Unit := do
  -- CAREFUL: do not sleep while holding the lock
  IO.sleep 100
  let mgr ← getManager
  if (← owner.cancelTk.isSet) || mgr._managerId != managerId then
    throwError "verification interrupted: specification owner was canceled or reset"
  let result? ←
    if mgr.isDoneFiltered vcFilter then
      pure ((← mgr.toResults vcFilter).vcs.find? (vcFilter ·.metadata))
    else
      pure none
  match result? with
  | none =>
    token.update (.text traceLoadingMessage)
    runTraceRefreshStep owner getManager managerId isExpectedSat _vcName vcFilter token
  | some vcResult =>
    -- Show trace widget if we have JSON, otherwise show status message
    if let some (traceJson, rawHtml?) := extractTraceDataFromVC vcResult then
      let props : TraceDisplayProps :=
        { result := traceJson, layout := "vertical", rawHtml := rawHtml?,
          kind := .symbolicTrace }
      token.update (Html.ofComponent TraceDisplayViewer props #[])
    else
      token.update (.text s!"{formatTraceStatus isExpectedSat vcResult.status}")

/-- Display a streaming widget for trace verification that shows the TraceDisplayViewer when done. -/
private def displayTraceStreamingResults (stx : Syntax) (managerId : ManagerId) (isExpectedSat : Bool)
    (vcName : Name) (vcFilter : VCMetadata → Bool) : CommandElabM Unit := do
  let owner ← Verifier.getVCManagerOwner
  let getManager ← Verifier.captureVCManager
  let html ← Veil.keyedPerElaboration (← liftCoreM <| mkRefreshComponentM (.text traceLoadingMessage)
    (runTraceRefreshStep owner getManager managerId isExpectedSat vcName vcFilter))
  liftCoreM <| Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.rpcEncode html) })
    stx

/-- Log trace verification results (called asynchronously). -/
private def logTraceResults (stx : Syntax) (isExpectedSat : Bool) (vcName : Name)
    (vcFilter : VCMetadata → Bool) (results : VerificationResults VCMetadata SmtResult) : CommandElabM Unit := do
  let some vcResult := results.vcs.find? (vcFilter ·.metadata)
    | throwErrorAt stx s!"trace [{vcName}]: VC result not found"

  let traceJson? := extractTraceJsonFromVC vcResult
  let violationIsError := veil.violationIsError.get (← getOptions)
  let logViolation := if violationIsError then logErrorAt stx else logInfoAt stx

  match vcResult.status with
  | some .proven =>
    if isExpectedSat then
      if let some traceJson := traceJson? then logInfoAt stx m!"{Veil.TraceDisplay.formatResult .symbolicTrace traceJson}"
      else logInfoAt stx "Found satisfying trace"
  | some .disproven =>
    if isExpectedSat then logViolation "No satisfying trace exists"
    else if let some traceJson := traceJson? then
      logViolation m!"Counterexample found\n{Veil.TraceDisplay.formatResult .symbolicTrace traceJson}"
    else logViolation "Counterexample found"
  | some .unknown => logViolation "Solver returned unknown"
  | some .error => logViolation "Verification error"; logDischargerErrors vcResult.timing.dischargers
  | some .timeout => logViolation "Solver timed out"; logDischargerErrors vcResult.timing.dischargers
  | none => logViolation "Verification did not complete"

  if shouldHaveTrace isExpectedSat vcResult.status && traceJson?.isNone then
    logViolation "Could not extract trace JSON"; logDischargerErrors vcResult.timing.dischargers

/-- Elaborate the SMT query and the positive predicate replayed on decoded labels and states. -/
def mkTraceQuery (mod : Module) (spec : TSyntax `traceSpec) : TermElabM (Term × TraceReplay) := do
  let expandedSpec := (← parseTraceSpec spec).flatMap expandTraceLine
  let numTransitions := expandedSpec.filter (!· matches .assertion _) |>.length
  let stateIds := (List.range (numTransitions + 1)).map fun i =>
    mkIdent (modelBinderName (traceStateName i))

  let sorts ← mod.uninterpretedParamIdents
  let theoryId := mkIdent (modelBinderName `th)
  let theoryT ← mod.theoryStx
  let stateT ← `(term| $(mkIdent stateName) ($fieldAbstractDispatcher $sorts*))
  let rtsExpr ← `(term| @$assembledRTS $sorts*)
  let tagType ← Lean.mkIdent <$> mkFreshUserName actionTagTypeName
  let ctx : TraceElabCtx := { mod, tagType, rtsExpr, theoryId, theoryT, stateT, sorts }

  let initAssertion ← `(term|
    ($rtsExpr).$(mkIdent `assumptions) $theoryId ∧
    (($rtsExpr).$(mkIdent `init) $theoryId $(stateIds.head!)))
  let initState : TraceElabState := {
    states := stateIds, assertions := #[initAssertion], replayAssertions := #[initAssertion] }
  let finalState ← expandedSpec.foldlM (processLine ctx) initState

  let conjunction ← repeatedAnd finalState.assertions
  let actionTagBinders ← if mod.actions.isEmpty then pure #[] else mkActionTagBinders tagType
  let params := traceModuleParams mod
  let moduleBinders ← params.mapM (·.binder)
  let allBinders := moduleBinders ++ actionTagBinders ++ finalState.binders.all
  let stateNames := stateIds.toArray
  let assertion ← `(∀ $allBinders* ($theoryId:ident : $theoryT) ($stateNames* : $stateT), ¬ $conjunction)

  let query ← `(∀ $moduleBinders* ($theoryId:ident : $theoryT) ($stateNames* : $stateT)
    $(finalState.replayLabels)*, $(← repeatedAnd finalState.replayAssertions))
  return (assertion, { params, statement := query, numTransitions })

/-- Elaborate the trace command at the current ref. Its widget shows the result while the solver
runs, through `withStreamingInfo`, so the elaborator that calls this is `@[incremental]`. -/
def elabTraceSpec (r : TSyntax `expected_smt_result) (name : Option (TSyntax `ident))
    (spec : TSyntax `traceSpec) (pf : Option (TSyntax `term)) : CommandElabM Unit := do
  let stx ← getRef
  withStreamingInfo stx do
  let mod ← getCurrentModule (errMsg := "trace commands can only be used inside a Veil module")
  let mod ← mod.ensureVerificationSpec stx

  -- Determine if this is a sat or unsat trace query
  let isExpectedSat := r.raw.isOfKind ``expected_sat

  let vcName ← match name with | some n => pure n.getId | none => liftCoreM (mkFreshUserName `trace)
  let (assertion, replay) ← Command.runTermElabM fun _ => mkTraceQuery mod spec

  match pf with
  | some proofTerm =>
    -- Generate a theorem for manual debugging
    let thmName := mkIdent vcName
    elabCommand (← `(theorem $thmName : $assertion := $proofTerm))
  | none =>
    -- Use VCManager with automatic discharger
    let vcStatement ← mkTraceVCStatement mod vcName assertion
    let metadata := mkTraceVCMetadata isExpectedSat replay.numTransitions (some vcName) (some assertion)
    -- Filter for matching trace VCs
    let vcFilter := (· == metadata)
    -- Check if a VC with this name already exists (avoid duplicate work)
    let _ ← Verifier.withVCManager fun ref => do
      let mgr ← ref.get
      if let some existingId := mgr.findVCByFilter vcFilter then
        return existingId
      -- Add VC and discharger atomically
      let (mgr', vcId) := mgr.addVC ⟨vcStatement, metadata⟩ {} #[]
      let mgr'' ← mgr'.mkAddDischarger vcId (TraceDischarger.fromAssertion replay isExpectedSat)
      ref.set mgr''
      return vcId

    -- Start async verification with logging callback
    let managerId ← Verifier.runFilteredAsyncWithManagerId vcFilter (logTraceResults stx isExpectedSat vcName vcFilter)

    -- Display streaming widget (shows progress then trace widget)
    displayTraceStreamingResults stx managerId isExpectedSat vcName vcFilter


@[incremental] elab_rules : command
  | `(command| $r:expected_smt_result trace [ $name ] { $spec:traceSpec } $pf:term) => elabTraceSpec r (some name) spec (some pf)
  | `(command| $r:expected_smt_result trace [ $name ] { $spec:traceSpec }) => elabTraceSpec r (some name) spec none
  | `(command| $r:expected_smt_result trace { $spec:traceSpec } $pf:term) => elabTraceSpec r none spec (some pf)
  | `(command| $r:expected_smt_result trace { $spec:traceSpec }) => elabTraceSpec r none spec none

end Veil
