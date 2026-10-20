module

public meta import Veil.Frontend.DSL.Module.Util.TraceTemplates
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

public meta section

/-!
  # Symbolic Trace Language

  This file defines the syntax and elaboration for symbolic model checking
  queries like `sat trace` and `unsat trace`.

  ## Example usage:

  ```lean4
  -- Automatic: registers with VCManager and runs SMT
  sat trace [can_elect_leader] (n : node) {
    any 3 actions
    send n _
    assert (leader n)
  }

  unsat trace (l n : node) {
    any 6 actions
    assert ¬ (leader l → le n l)
  }

  -- Manual: generates a theorem for debugging
  unsat trace [debug_trace] {
    send
    assert False
  } by veil_bmc
  ```
-/

namespace Veil
open Lean Elab Command Term Meta ProofWidgets RefreshComponent

/-- A single line in a trace specification -/
inductive TraceSpecLine
  | action : Ident → Array Term → TraceSpecLine
  | anyAction : TraceSpecLine
  | anyNActions : Nat → TraceSpecLine
  | assertion : Term → TraceSpecLine
deriving Inhabited, Repr

instance : ToString TraceSpecLine := ⟨fun
  | TraceSpecLine.action n args => s!"action {n.getId} {args}"
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
      | `(traceLine| $id:ident $args:term*) => return TraceSpecLine.action id args
      | _ => throwErrorAt stx "unsupported syntax"
    return ts.toList
  | _ => throwUnsupportedSyntax

/-- Accumulated binders during trace spec elaboration -/
structure BinderAccum where
  params : Array BinderPair := #[]
  tags : Array BinderPair := #[]

instance : Append BinderAccum where
  append a b := { params := a.params ++ b.params, tags := a.tags ++ b.tags }

def BinderAccum.all (acc : BinderAccum) : Array BinderPair := acc.tags ++ acc.params

/-- Create a tag binder for a transition -/
private def mkTagBinder (trIdx : Nat) : TermElabM (Ident × BinderPair) := do
  let tagId := mkIdent $ Name.mkSimple s!"_tr{trIdx}_tag"
  return (tagId, ← mkBinderPair tagId actionTagType)

/-- State threaded through trace spec elaboration -/
structure TraceElabState where
  /-- Remaining state identifiers (head is current state) -/
  states : List Ident
  /-- Transition counter for unique naming -/
  trIdx : Nat := 1
  /-- Accumulated assertions -/
  assertions : Array (TSyntax `term) := #[]
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
  rtsExpr : TSyntax `term
  theoryId : TSyntax `term
  theoryT : TSyntax `term
  stateT : TSyntax `term
  sorts : Array Ident

/-- Evaluate an argument expression in the source state of its action. The type
ascription also prevents numerals and other overloaded terms from defaulting to
a type different from the action parameter's type. -/
private def processArgument (ctx : TraceElabCtx) (currState : Ident) (t ty : Term) : TermElabM Term := do
  let fieldRepInstance ← `(term| $instAbstractFieldRepresentation $(ctx.sorts)*)
  let stateSortTerm ← `(term| $fieldAbstractDispatcher $(ctx.sorts)*)
  let wrapped ← withTheoryAndStateFn ctx.mod (← `(term| ($t : $ty))) (some ty)
    ctx.theoryT ctx.stateT fieldRepInstance stateSortTerm
  `(term| ($wrapped $(ctx.theoryId) $currState))

/-- Standalone holes are trace choices, not Lean inference metavariables. -/
private def isTraceWildcard (t : Term) : Bool := t.raw.isOfKind ``Lean.Parser.Term.hole

/-- Elaborate a named call's argument telescope. Supplied values are used directly
in the call, so later dependent argument types specialize definitionally. Fresh
variables constrained to those values are retained as observable SMT witnesses. -/
private def mkCallParams (ctx : TraceElabCtx) (curr : Ident) (trIdx : Nat)
    (params : Array Parameter) (supplied : Array Term)
    : TermElabM (Array Term × Array BinderPair × Array Term) := do
  let mut args := #[]
  let mut binders := #[]
  let mut constraints := #[]
  for idx in [:params.size] do
    let p := params[idx]!
    let ty ← instantiateParamType p.type (params.extract 0 idx) args
    let id := mkIdent $ Name.mkSimple s!"_tr{trIdx}_arg{idx}_{p.name}"
    binders := binders.push (← mkBinderPair id ty)
    let arg ← match supplied[idx]? with
      | some t =>
        if isTraceWildcard t then pure (⟨id.raw⟩ : Term)
        else do
          let value ← withRef t <| processArgument ctx curr t ty
          constraints := constraints.push (← `(term| Veil.eqWithoutSubst $id $value))
          pure value
      | none => pure (⟨id.raw⟩ : Term)
    args := args.push arg
  return (args, binders, constraints)

/-- Process a transition (specific or any action), returning assertion and binders -/
private def processTransition (ctx : TraceElabCtx) (curr next : Ident) (trIdx : Nat)
    : TraceSpecLine → TermElabM (TSyntax `term × BinderAccum)
  | .action actionId supplied => withRef actionId do
    let actionName := actionId.getId
    let proc := ctx.mod.actions.find? (·.name == actionName)
    let specificParams ← match proc with
      | some p => pure (← ctx.mod.declarationAllParams p.name p.declarationKind).2
      | none => throwError s!"action '{actionName}' not found. Available: {ctx.mod.actions.map (·.name)}"
    let (tagId, tagPair) ← mkTagBinder trIdx
    unless supplied.isEmpty || supplied.size == specificParams.size do
      throwError "action '{actionName}' expects {specificParams.size} arguments, but {supplied.size} were supplied; use '_' for unspecified arguments"
    let (args, paramPairs, constraints) ← mkCallParams ctx curr trIdx specificParams supplied
    let trExpr ← mkTransitionExpr ctx.rtsExpr ctx.theoryId curr next tagId actionName args
    return (← combineTraceTerms ``And ``True (#[trExpr] ++ constraints),
            { params := paramPairs, tags := #[tagPair] })
  | .anyAction => do
    let (tagId, tagPair) ← mkTagBinder trIdx
    let (disjunction, paramBinders) ← mkAnyActionDisjunction ctx.mod ctx.rtsExpr ctx.theoryId curr next tagId trIdx
    return (disjunction, { params := paramBinders, tags := #[tagPair] })
  | _ => unreachable!

/-- Process a user assertion (no state transition) -/
private def processAssertion (ctx : TraceElabCtx) (currState : Ident) (t : Term) : TermElabM (TSyntax `term) := do
  let fieldRepInstance ← `(term| $instAbstractFieldRepresentation $(ctx.sorts)*)
  let stateSortTerm ← `(term| $fieldAbstractDispatcher $(ctx.sorts)*)
  let wrappedTerm ← withTheoryAndStateFn ctx.mod (← `(uqc% (($t:term):Prop))) (some $ ← `(term|Prop)) ctx.theoryT ctx.stateT fieldRepInstance stateSortTerm
  `(term|($wrappedTerm $(ctx.theoryId) $currState))

/-- Expand anyNActions into individual anyAction entries -/
private def expandTraceLine : TraceSpecLine → List TraceSpecLine
  | .anyNActions k => List.replicate k .anyAction
  | other => [other]

/-- Process a single trace spec line, returning updated state -/
private def processLine (ctx : TraceElabCtx) (s : TraceElabState) : TraceSpecLine → TermElabM TraceElabState
  | .assertion t => do
    let curr := s.states.head!
    let assertion ← processAssertion ctx curr t
    return { s with assertions := s.assertions.push assertion }
  | line => do  -- .action or .anyAction
    let (curr, next, s') ← s.advance.getDM (throwError "insufficient states for transition")
    let (assertion, newBinders) ← processTransition ctx curr next s.trIdx line
    return { s' with assertions := s'.assertions.push assertion, binders := s'.binders ++ newBinders }

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

private partial def runTraceRefreshStep (isExpectedSat : Bool) (_vcName : Name)
    (vcFilter : VCMetadata → Bool) (token : RefreshToken) : CoreM Unit := do
  -- CAREFUL: do not sleep while holding the lock
  IO.sleep 100
  let mgr ← Verifier.vcManager.atomically fun ref => ref.get
  let result? ←
    if mgr.isDoneFiltered vcFilter then
      pure ((← mgr.toResults vcFilter).vcs.find? (vcFilter ·.metadata))
    else
      pure none
  match result? with
  | none =>
    token.update (.text traceLoadingMessage)
    runTraceRefreshStep isExpectedSat _vcName vcFilter token
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
private def displayTraceStreamingResults (stx : Syntax) (isExpectedSat : Bool)
    (vcName : Name) (vcFilter : VCMetadata → Bool) : CommandElabM Unit := do
  let html ← liftCoreM <| mkRefreshComponentM (.text traceLoadingMessage)
    (runTraceRefreshStep isExpectedSat vcName vcFilter)
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

/-- Validate user bindings before state/field wrappers introduce their own names. -/
private def parseTraceBinders (mod : Module) (binders : Array (TSyntax ``traceBinder))
    : TermElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Array Name) := do
  let env ← getEnv
  let mut result := #[]
  let mut names := #[]
  for binder in binders do
    match binder with
    | `(traceBinder| ($ids:ident* : $ty)) =>
      for id in ids do
        let name := id.getId
        unless name.isAtomic do
          throwErrorAt id "trace binding '{name}' must be an unqualified name"
        if names.contains name then
          throwErrorAt id "duplicate trace binding '{name}'"
        let text := name.toString
        let reserved := name == `th || name == `st || name == fieldConcreteTypeName ||
          name == actionTagTypeName ||
          text.startsWith "_tr" || text.startsWith "__veil" ||
          (text.startsWith "st" && (text.drop 2).toString.toNat?.isSome) ||
          mod.mutableComponents.any (fun c => c.name.appendAfter "_conc" == name)
        if reserved || mod.parameters.any (·.name == name) ||
            (mod.mutableComponents ++ mod.immutableComponents).any (·.name == name) ||
            mod._declarations.contains name || env.contains (mod.name ++ name) then
          throwErrorAt id "trace binding '{name}' conflicts with a module or reserved trace name"
        result := result.push (← `(bracketedBinder| ($id : $ty)))
        names := names.push name
    | _ => throwErrorAt binder "expected a typed trace binding '(name : type)'"
  return (result, names)

def elabTraceSpec (r : TSyntax `expected_smt_result) (name : Option (TSyntax `ident))
    (queryBinders : Array (TSyntax ``traceBinder))
    (spec : TSyntax `traceSpec) (pf : Option (TSyntax `term)) : CommandElabM Unit := do
  let stx ← getRef
  let mod ← getCurrentModule (errMsg := "trace commands can only be used inside a Veil module")
  let mod ← mod.ensureVerificationSpec stx

  -- Determine if this is a sat or unsat trace query
  let isExpectedSat := r.raw.isOfKind ``expected_sat

  -- Build the trace specification
  let (assertion, numTransitions, vcName, queryBindings, specifiedArgs) ← Command.runTermElabM fun _ => do
    let (queryBinders, queryBindings) ← parseTraceBinders mod queryBinders
    let expandedSpec := (← parseTraceSpec spec).flatMap expandTraceLine
    let numTransitions := expandedSpec.filter (!· matches .assertion _) |>.length
    let stateIds := (List.range (numTransitions + 1)).map fun i => mkIdent (Name.mkSimple s!"st{i}")

    let sorts ← mod.uninterpretedParamIdents
    let theoryId := mkIdent `th
    let theoryT ← mod.theoryStx
    let stateT ← `(term| $(mkIdent stateName) ($fieldAbstractDispatcher $sorts*))
    let rtsExpr ← `(term| @$assembledRTS $sorts*)
    let ctx : TraceElabCtx := { mod, rtsExpr, theoryId, theoryT, stateT, sorts }

    let initAssertion ← `(term|
      ($rtsExpr).$(mkIdent `assumptions) $theoryId ∧
      (($rtsExpr).$(mkIdent `init) $theoryId $(stateIds.head!)))
    let initState : TraceElabState := { states := stateIds, assertions := #[initAssertion] }
    let finalState ← expandedSpec.foldlM (processLine ctx) initState

    let vcName ← match name with | some n => pure n.getId | none => mkFreshUserName `trace
    let conjunction ← combineTraceTerms ``And ``True finalState.assertions
    let actionTagBinders ← if mod.actions.isEmpty then pure #[] else mkActionTagBinders
    let allBinders := (← collectModuleBinders mod) ++ actionTagBinders ++ finalState.binders.tags
    let bracketedBinders := allBinders.map (·.1) ++ queryBinders
    let paramBinders := finalState.binders.params.map (·.1)
    let stateNames := stateIds.toArray
    -- Argument types may depend on supplied arguments which read a pre-state.
    -- Bind theory and states before introducing those arguments.
    let assertion ←
      `(∀ $[$bracketedBinders]* ($theoryId:ident : $theoryT) ($[$stateNames]* : $stateT)
          $[$paramBinders]*, ¬ $conjunction)
    let mut specifiedArgs := #[]
    let mut trIdx := 1
    for line in expandedSpec do
      match line with
      | .assertion _ => pure ()
      | .action _ args =>
        for idx in [:args.size] do
          unless isTraceWildcard args[idx]! do
            specifiedArgs := specifiedArgs.push (trIdx, idx)
        trIdx := trIdx + 1
      | _ => trIdx := trIdx + 1
    return (assertion, numTransitions, vcName, queryBindings, specifiedArgs)

  match pf with
  | some proofTerm =>
    -- Generate a theorem for manual debugging
    let thmName := mkIdent vcName
    elabCommand (← `(theorem $thmName : $assertion := $proofTerm))
  | none =>
    -- Use VCManager with automatic discharger
    let vcStatement ← mkTraceVCStatement mod vcName assertion
    let metadata := mkTraceVCMetadata isExpectedSat numTransitions (some vcName) (some assertion)
    -- Filter for matching trace VCs
    let vcFilter := (· == metadata)
    -- Check if a VC with this name already exists (avoid duplicate work)
    let _ ← Verifier.withVCManager fun ref => do
      let mgr ← ref.get
      if let some existingId := mgr.findVCByFilter vcFilter then
        return existingId
      -- Add VC and discharger atomically
      let (mgr', vcId) := mgr.addVC ⟨vcStatement, metadata⟩ {} #[]
      let mgr'' ← mgr'.mkAddDischarger vcId (TraceDischarger.fromAssertion numTransitions isExpectedSat
        (queryBindings := queryBindings) (specifiedArgs := specifiedArgs))
      ref.set mgr''
      return vcId

    -- Start async verification with logging callback
    Verifier.runFilteredAsync vcFilter (logTraceResults stx isExpectedSat vcName vcFilter)

    -- Display streaming widget (shows progress then trace widget)
    displayTraceStreamingResults stx isExpectedSat vcName vcFilter


elab_rules : command
  | `(command| $r:expected_smt_result trace [ $name ] $binders:traceBinder* { $spec:traceSpec } $pf:term) => elabTraceSpec r (some name) binders spec (some pf)
  | `(command| $r:expected_smt_result trace [ $name ] $binders:traceBinder* { $spec:traceSpec }) => elabTraceSpec r (some name) binders spec none
  | `(command| $r:expected_smt_result trace $binders:traceBinder* { $spec:traceSpec } $pf:term) => elabTraceSpec r none binders spec (some pf)
  | `(command| $r:expected_smt_result trace $binders:traceBinder* { $spec:traceSpec }) => elabTraceSpec r none binders spec none

end Veil
