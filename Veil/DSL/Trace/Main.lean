import Lean
import Lean.Parser
import Veil.Util.Meta
import Veil.Util.DSL
import Veil.Model.TransitionSystem
import Veil.DSL.Specification.SpecDef

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
"}" term : command


open Lean Elab Command Term

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
      | `(traceLine| any $n:num actions) => do (
        if n.getNat < 2 then
          throwErrorAt stx "any {n} actions: n must be >= 2"
        else
          return TraceSpecLine.anyNActions n.getNat
      )
      | `(traceLine| assert $term) => return TraceSpecLine.assertion term
      | `(traceLine| $id:ident) => return TraceSpecLine.action id.raw.getId
      | _ => throwErrorAt stx "unsupported syntax"
    return ts.toList
  | _ => throwUnsupportedSyntax

open Lean.Parser.Term in

def elabTraceSpec (r : TSyntax `expected_smt_result) (name : Option (TSyntax `ident)) (spec : TSyntax `traceSpec) (pf : TSyntax `term)
  : CommandElabM Unit := do
  liftCoreM errorIfStateNotDefined
  liftCoreM errorIfSpecNotDefined
  let vd ← getAssertionParameters
  let th ← Command.runTermElabM fun vs => do
    let systemTp ← getSystemTpStx vs
    let spec ← parseTraceSpec spec
    let numActions := spec.foldl (fun n s =>
      match s with
      | TraceSpecLine.assertion _ => n
      | TraceSpecLine.anyNActions k => n + k
      | _ => n + 1) 0
    let numStates := numActions + 1
    let stateNames := List.toArray $ (List.range numStates).map fun i => mkIdent (Name.mkSimple s!"st{i}")

    /- Track which state assertions refer to. -/
    let mut currStateId := 0
    /- Which assertions, including state-transitions, does the spec contain. -/
    let mut assertions : Array (TSyntax `term) := #[]
    assertions := assertions.push (← `(term|(($systemTp).$(mkIdent `assumptions) $(stateNames[0]!) ∧ (($systemTp).$(mkIdent `init) $(stateNames[0]!)))))
    for s in spec do
      let currState := stateNames[currStateId]!
      match s with
      | TraceSpecLine.action n => do
        let nextState := stateNames[currStateId + 1]!
        let vs <- getSectionArgumentsStxWithConcreteState vs
        let stx <- `(@$(mkIdent $ toTrName n) $vs*)
        -- FIXME: make a correct application, i.e. providing the `vd` names
        let t ← `(term|($stx $currState $nextState))
        assertions := assertions.push t
        currStateId := currStateId + 1
      | TraceSpecLine.anyAction => do
        let nextState := stateNames[currStateId + 1]!
        let t ← `(term|(($systemTp).$(mkIdent `next) $currState $nextState))
        assertions := assertions.push t
        currStateId := currStateId + 1
      -- FIXME: remove code duplication with above
      | TraceSpecLine.anyNActions k => do
        for _ in [0:k] do
          let currState := stateNames[currStateId]!
          let nextState := stateNames[currStateId + 1]!
          let t ← `(term|(($systemTp).$(mkIdent `next) $currState $nextState))
          assertions := assertions.push t
          currStateId := currStateId + 1
      | TraceSpecLine.assertion t => do
        -- Elaborate assertions in the same way we elaborate invariants.
        -- See `elab "invariant"` in `DSL.lean`.
        let stx <- funcasesM t
        let t ← elabBindersAndCapitals #[] vs stx fun _ e => do
          let e <- delabWithMotives e
          `(fun $(mkIdent `st) => $e: term)
        let t ← `(term|($t $currState))
        assertions := assertions.push t
    let name : Name ← match name with
    | some n => pure n.getId
    | none => mkFreshUserName (Name.mkSimple "trace")
    let th_id := mkIdent name
    let conjunction ← repeatedAnd assertions
    -- sat trace -> ∃ states, (conjunction of assertions)
    -- unsat trace -> ∀ states, ¬ (conjunction of assertions)
    let stateTp ← getStateTpStx
    let binderNames : Array (TSyntax ``Lean.binderIdent) := stateNames.map toBinderIdent
    let vdE ← vd.mapM toExplicitBinders
    let assertion ← match r with
    | `(expected_smt_result| unsat) => `(∀ $[$vd]* ($[$stateNames]* : $stateTp), ¬ $conjunction)
    | `(expected_smt_result| sat) => `(∃ $[$vdE]* ($[$binderNames]* : $stateTp), $conjunction)
    | _ => dbg_trace "expected result is neither sat nor unsat!" ; unreachable!
    `(theorem $th_id : $assertion := by exact $pf)
  elabCommand $ th

elab_rules : command
  | `(command| $r:expected_smt_result trace [ $name ] { $spec:traceSpec } $pf) => elabTraceSpec r name spec pf
  | `(command| $r:expected_smt_result trace { $spec:traceSpec } $pf) => elabTraceSpec r none spec pf
