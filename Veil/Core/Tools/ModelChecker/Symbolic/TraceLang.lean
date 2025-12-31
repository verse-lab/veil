import Lean
import Lean.Parser
import Veil.Util.Meta
import Veil.Frontend.DSL.Module.Util.Assertions
import Veil.Frontend.DSL.Module.Names
import Veil.Frontend.DSL.Util
import Veil.Core.Tools.ModelChecker.TransitionSystem
import Veil.Core.Tools.Verifier.Server
import Veil.Core.Tools.Verifier.Results
import Veil.Frontend.DSL.Module.VCGen
import Veil.Core.UI.Trace.TraceDisplay
import ProofWidgets.Component.HtmlDisplay

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

declare_syntax_cat expected_smt_result
syntax (name := expected_sat) "sat" : expected_smt_result
syntax (name := expected_unsat) "unsat" : expected_smt_result

declare_syntax_cat trace_line
syntax (name := any_action_star) "*" : trace_line
syntax (name := any_action) atomic("any" "action") : trace_line
syntax traceAnyAction := any_action_star <|> any_action

syntax (name := traceAnyNActions) "any " num " actions": trace_line

syntax (name := traceActionName) ident : trace_line
syntax traceAction := (traceActionName <|> traceAnyAction <|> traceAnyNActions)

syntax (name := traceAssertion) "assert " term:max : trace_line

syntax traceLine := (traceAction <|> traceAssertion)
syntax traceSpec := (traceLine colEq)*

syntax expected_smt_result "trace" ("[" ident "]")? "{"
  traceSpec
"}" (term)? : command


namespace Veil
open Lean Elab Command Term Meta

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

def parseTraceSpec [Monad m] [MonadExceptOf Exception m] [MonadError m] (stx : Syntax) : m TraceSpec := do
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

open Lean.Parser.Term in
/-- Convert a bracketed binder to an explicit binder for use in existential quantification -/
private def toExplicitBindersForExists (stx : TSyntax `Lean.Parser.Term.bracketedBinder)
    : TermElabM (TSyntax `Lean.bracketedExplicitBinders) := do
  match stx with
  | `(bracketedBinder| ($id:ident : $tp)) | `(bracketedBinder| {$id:ident : $tp})
  | `(bracketedBinder| [$id:ident : $tp]) =>
    `(bracketedExplicitBinders| ($(identToBinderIdent id) : $tp))
  | `(bracketedBinder| [$tp]) =>
    let freshId := mkIdent (← mkFreshUserName `inst)
    `(bracketedExplicitBinders| ($(identToBinderIdent freshId) : $tp))
  | _ => throwError s!"toExplicitBindersForExists: unexpected syntax: {stx}"

/-- A pair of bracketed and explicit binders that are always created together -/
abbrev BinderPair := TSyntax `Lean.Parser.Term.bracketedBinder × TSyntax `Lean.bracketedExplicitBinders

/-- Accumulated binders during trace spec elaboration -/
structure BinderAccum where
  params : Array BinderPair := #[]
  tags : Array BinderPair := #[]

instance : Append BinderAccum where
  append a b := { params := a.params ++ b.params, tags := a.tags ++ b.tags }

def BinderAccum.all (acc : BinderAccum) : Array BinderPair := acc.tags ++ acc.params

/-- Create both bracketed and explicit binders for an identifier with type -/
private def mkBinderPair (id : Ident) (ty : Term) : TermElabM BinderPair := do
  return (← `(bracketedBinder| ($id : $ty)),
          ← `(bracketedExplicitBinders| ($(identToBinderIdent id) : $ty)))

/-- Create a tag binder for a transition -/
private def mkTagBinder (trIdx : Nat) : TermElabM (Ident × BinderPair) := do
  let tagId := mkIdent $ Name.mkSimple s!"_tr{trIdx}_tag"
  return (tagId, ← mkBinderPair tagId actionTagType)

/-- Create parameter binders with unique names for a transition -/
private def mkParamBinders (params : Array Parameter) (prefix_ : String)
    : TermElabM (Array Ident × Array BinderPair) := do
  let results ← params.mapIdxM fun idx p => do
    let uniqueId := mkIdent $ Name.mkSimple s!"{prefix_}_arg{idx}_{p.name}"
    return (uniqueId, ← mkBinderPair uniqueId p.type)
  return (results.map (·.1), results.map (·.2))

/-- Build the transition expression: `tag = tagMember ∧ rts.tr th st label st'` -/
private def mkTransitionExpr (rtsExpr theoryId currState nextState : TSyntax `term)
    (tagId : Ident) (actionName : Name) (argIdents : Array Ident) : TermElabM (TSyntax `term) := do
  let actionTagMember := mkIdent $ actionTagEnumInstName ++ actionName
  let labelConstructor := mkIdent $ labelTypeName ++ actionName
  let labelExpr ← `(term| ($labelConstructor $argIdents*))
  let trExpr ← `(term| (($rtsExpr).$(mkIdent `tr) $theoryId $currState $labelExpr $nextState))
  `(term| ($tagId = $actionTagMember ∧ $trExpr))

/-- Build a disjunction representing any action transition with ActionTag constraint -/
private def mkAnyActionDisjunction (mod : Module) (rtsExpr theoryId currState nextState : TSyntax `term)
    (tagId : Ident) (trIdx : Nat) : TermElabM (TSyntax `term × Array BinderPair) := do
  let results ← mod.actions.mapIdxM fun actionIdx act => do
    let (_, specificParams) ← mod.declarationAllParams act.name act.declarationKind
    let (argIdents, binders) ← mkParamBinders specificParams s!"_tr{trIdx}_act{actionIdx}"
    return (← mkTransitionExpr rtsExpr theoryId currState nextState tagId act.name argIdents, binders)
  return (← repeatedOr (results.map (·.1)), results.flatMap (·.2))

/-- Collect module-level binders (sorts, sort assumptions, user-defined typeclasses) -/
private def collectModuleBinders (mod : Module) : TermElabM (Array BinderPair) := do
  let sortBinders ← mod.sortBinders
  let typeclassParams := mod.parameters.filter fun p =>
    match p.kind with
    | .moduleTypeclass .sortAssumption | .moduleTypeclass .userDefined => true
    | _ => false
  let typeclassBinders ← typeclassParams.mapM (·.binder)
  let allBinders := sortBinders ++ typeclassBinders
  allBinders.mapM fun b => do return (b, ← toExplicitBindersForExists b)

/-- Create ActionTag type and enum binders -/
private def mkActionTagBinders : TermElabM (Array BinderPair) := do
  let typePair ← mkBinderPair actionTagType (← `(term| Type))
  let actionTagEnumClass := Ident.toEnumClass actionTagType
  let enumBinder ← `(bracketedBinder| ($actionTagEnumInst : $actionTagEnumClass $actionTagType))
  let enumExplicit ← `(bracketedExplicitBinders| ($(identToBinderIdent actionTagEnumInst) : $actionTagEnumClass $actionTagType))
  return #[typePair, (enumBinder, enumExplicit)]

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

/-- Process a transition (specific or any action), returning assertion and binders -/
private def processTransition (ctx : TraceElabCtx) (curr next : Ident) (trIdx : Nat)
    : TraceSpecLine → TermElabM (TSyntax `term × BinderAccum)
  | .action actionName => do
    let proc := ctx.mod.actions.find? (·.name == actionName)
    let specificParams ← match proc with
      | some p => pure (← ctx.mod.declarationAllParams p.name p.declarationKind).2
      | none => throwError s!"action '{actionName}' not found. Available: {ctx.mod.actions.map (·.name)}"
    let (tagId, tagPair) ← mkTagBinder trIdx
    let (argIdents, paramPairs) ← mkParamBinders specificParams s!"_tr{trIdx}"
    return (← mkTransitionExpr ctx.rtsExpr ctx.theoryId curr next tagId actionName argIdents,
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
  let wrappedTerm ← withTheoryAndStateFn ctx.mod (← `(uqc% (($t:term):Prop))) ctx.theoryT ctx.stateT fieldRepInstance stateSortTerm
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

/-- Log all errors from discharger results. -/
private def logDischargerErrors (dischargers : Array (DischargerResultData SmtResult)) : CommandElabM Unit := do
  for d in dischargers do
    if let some (.error exs _) := d.result then
      for (ex, _) in exs do logError ex.toMessageData

def elabTraceSpec (r : TSyntax `expected_smt_result) (name : Option (TSyntax `ident))
    (spec : TSyntax `traceSpec) (pf : Option (TSyntax `term)) : CommandElabM Unit := do
  let stx ← getRef
  let mod ← getCurrentModule (errMsg := "trace commands can only be used inside a Veil module after #gen_spec")
  if !mod.isSpecFinalized then throwError "trace commands can only be used after #gen_spec"

  -- Determine if this is a sat or unsat trace query
  let isExpectedSat := r.raw.isOfKind ``expected_sat

  -- Build the trace specification
  let (assertion, numTransitions, vcName) ← Command.runTermElabM fun _ => do
    let expandedSpec := (← parseTraceSpec spec).flatMap expandTraceLine
    let numTransitions := expandedSpec.filter (!· matches .assertion _) |>.length
    let stateIds := (List.range (numTransitions + 1)).map fun i => mkIdent (Name.mkSimple s!"st{i}")

    let sorts ← mod.sortIdents
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
    let conjunction ← repeatedAnd finalState.assertions
    let allBinders := (← collectModuleBinders mod) ++ (← mkActionTagBinders) ++ finalState.binders.all
    let bracketedBinders := allBinders.map (·.1)
    let stateNames := stateIds.toArray
    -- let explicitBinders := allBinders.map (·.2)
    -- let binderNames := stateNames.map identToBinderIdent

    let assertion ← --if r.raw.isOfKind ``expected_unsat then
      `(∀ $[$bracketedBinders]* ($theoryId:ident : $theoryT) ($[$stateNames]* : $stateT), ¬ $conjunction)
    -- else
      -- `(∃ $[$explicitBinders]* ($theoryId:ident : $theoryT) ($[$binderNames]* : $stateT), $conjunction)

    return (assertion, numTransitions, vcName)

  match pf with
  | some proofTerm =>
    -- Generate a theorem for manual debugging
    let thmName := mkIdent vcName
    elabCommand (← `(theorem $thmName : $assertion := $proofTerm))
  | none =>
    -- Use VCManager with automatic discharger
    let vcStatement ← mkTraceVCStatement mod vcName assertion
    let metadata := mkTraceVCMetadata isExpectedSat numTransitions (some vcName)
    let traceVC ← Verifier.addVC ⟨vcStatement, metadata⟩ {}
    Verifier.mkAddDischarger traceVC (TraceDischarger.fromAssertion numTransitions isExpectedSat)

    -- Wait synchronously for the VC to complete (allows widget display on main thread)
    let results ← Verifier.waitFilteredSync (fun m => m.isTrace && m.propertyName? == some vcName)
    let some vcResult := results.vcs.find? (·.id == traceVC)
      | throwError s!"trace [{vcName}]: VC result not found"

    -- Extract trace JSON (only present when SMT result is SAT)
    let traceJson? := vcResult.timing.dischargers.findSome? (extractTraceJson? ·.result)

    -- Determine if we expect a trace to exist based on query type and result
    let shouldHaveTrace := (isExpectedSat && vcResult.status == some .proven) ||
                           (!isExpectedSat && vcResult.status == some .disproven)

    -- Display trace widget if we have one
    if let some traceJson := traceJson? then
      ProofWidgets.displayTraceWidget stx traceJson

    -- Report results based on expectation
    if vcResult.status != some .proven then
      let kind := if isExpectedSat then "sat" else "unsat"
      match vcResult.status with
      | some .disproven =>
        if isExpectedSat then logError s!"sat trace [{vcName}]: no satisfying trace exists"
        else if let some traceJson := traceJson? then
          logError s!"unsat trace [{vcName}]: counterexample found\n{traceJson}"
        else
          logError s!"unsat trace [{vcName}]: counterexample found"
      | some .unknown => logError s!"{kind} trace [{vcName}]: solver returned unknown"
      | some .error =>
        logError s!"{kind} trace [{vcName}]: verification error"
        logDischargerErrors vcResult.timing.dischargers
      | _ => logError s!"{kind} trace [{vcName}]: verification did not complete"
    else
      if isExpectedSat then
        if let some traceJson := traceJson? then
          logInfo s!"sat trace [{vcName}]: found satisfying trace\n{traceJson}"
        else
          logInfo s!"sat trace [{vcName}]: found satisfying trace"
      -- Log error if we expected a trace but couldn't extract it
      if shouldHaveTrace && traceJson?.isNone then
        logError s!"trace [{vcName}]: could not extract trace JSON"
        logDischargerErrors vcResult.timing.dischargers


elab_rules : command
  | `(command| $r:expected_smt_result trace [ $name ] { $spec:traceSpec } $pf:term) => elabTraceSpec r (some name) spec (some pf)
  | `(command| $r:expected_smt_result trace [ $name ] { $spec:traceSpec }) => elabTraceSpec r (some name) spec none
  | `(command| $r:expected_smt_result trace { $spec:traceSpec } $pf:term) => elabTraceSpec r none spec (some pf)
  | `(command| $r:expected_smt_result trace { $spec:traceSpec }) => elabTraceSpec r none spec none

end Veil
