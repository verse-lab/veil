import Lean
import Lean.Parser
import LeanSts.DSL.Util
import LeanSts.TransitionSystem

declare_syntax_cat expected_smt_result
syntax (name := expected_sat) "sat" : expected_smt_result
syntax (name := expected_unsat) "unsat" : expected_smt_result

declare_syntax_cat trace_line
syntax (name := any_action_star) "*" : trace_line
syntax (name := any_action) "any action" : trace_line
syntax traceAnyAction := any_action_star <|> any_action

syntax (name := traceActionName) ident : trace_line
syntax traceAction := (traceActionName <|> traceAnyAction)

syntax (name := traceAssertion) "assert " term : trace_line

syntax traceLine := (traceAction <|> traceAssertion)
syntax traceSpec := (traceLine colEq)*

syntax expected_smt_result "trace" ("[" ident "]")? "{"
  traceSpec
"}" : command


open Lean Elab Command Term RelationalTransitionSystem

/-- A single line in a trace specification -/
inductive TraceSpecLine
  | action : Name → TraceSpecLine
  | anyAction : TraceSpecLine
  | assertion : Term → TraceSpecLine
deriving Inhabited, Repr

instance : ToString TraceSpecLine := ⟨fun
  | TraceSpecLine.action n => s!"action {n}"
  | TraceSpecLine.anyAction => "any action"
  | TraceSpecLine.assertion t => s!"assertion {t}"⟩

abbrev TraceSpec := List TraceSpecLine

def parseTraceSpec [Monad m] [MonadExceptOf Exception m] (stx : Syntax) : m TraceSpec := do
  match stx with
  | `(traceSpec| $[$ts]* ) => do
    let mut ts := ts.map fun t => match t with
      | `(traceLine| any action) | `(traceLine| * ) => TraceSpecLine.anyAction
      | `(traceLine| assert $term) => TraceSpecLine.assertion term
      | `(traceLine| $id:ident) => TraceSpecLine.action id.raw.getId
      | x => dbg_trace "unsupported syntax: {x}" ; unreachable!
    return ts.toList
  | _ => throwUnsupportedSyntax

open Lean.Parser.Term in
def elabTraceSpec (r : TSyntax `expected_smt_result) (name : Option (TSyntax `ident)) (spec : TSyntax `traceSpec)
  : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  let th ← Command.runTermElabM fun vs => do
    dbg_trace "vs = {vs}"
    let finalResult ← match r with
    | `(expected_smt_result| sat) => `(True)
    | `(expected_smt_result| unsat) => `(False)
    | _ => unreachable!

    let spec ← parseTraceSpec spec
    let numActions := spec.foldl (fun n s => match s with | TraceSpecLine.assertion _ => n | _ => n + 1) 0
    let numStates := numActions + 1
    let stateNames := List.toArray $ (List.range numStates).map fun i => mkIdent (Name.mkSimple s!"st{i}")

    /- Track which state assertions refer to. -/
    let mut currStateId := 0
    /- Which assertions, including state-transitions, does the spec contain. -/
    let mut assertions : Array (TSyntax ``bracketedBinder) := #[]
    assertions := assertions.push (← `(bracketedBinderF|(t0 : RelationalTransitionSystem.init $(stateNames[0]!))))
    for s in spec do
      let currState := stateNames[currStateId]!
      let assertionId := assertions.size
      match s with
      | TraceSpecLine.action n => do
        let assertionName := mkIdent (Name.mkSimple s!"t{assertionId}")
        let actionName := mkIdent n
        let nextState := stateNames[currStateId + 1]!
        -- FIXME: make a correct application, i.e. providing the `vd` names
        let t ← `(bracketedBinderF|($assertionName : $actionName $currState $nextState))
        assertions := assertions.push t
        currStateId := currStateId + 1
      | TraceSpecLine.anyAction => do
        let assertionName := mkIdent (Name.mkSimple s!"t{assertionId}")
        let nextState := stateNames[currStateId + 1]!
        let t ← `(($assertionName : RelationalTransitionSystem.next $currState $nextState))
        currStateId := currStateId + 1
      | TraceSpecLine.assertion t => do
        let assertionName := mkIdent (Name.mkSimple s!"h{assertionId}")
        -- FIXME: elaborate the assertions in the same way we elaborate invariants
        -- see `elab "invariant"` in DSL.lean
        let t ← `(bracketedBinderF|($assertionName : $t $currState))
        assertions := assertions.push t

    dbg_trace "{spec} with {numActions} actions"
    let name : Name ← match name with
    | some n => pure n.getId
    | none => mkFreshUserName (Name.mkSimple "trace")
    let th_id := mkIdent name
    let stateTp   <- PrettyPrinter.delab (<- stateTp vs)
    `(theorem $th_id $[$vd]* ($[$stateNames]* : $stateTp)
      $[$assertions]*
     : $finalResult := by sorry)
  dbg_trace "{th}"
  elabCommand $ th

elab_rules : command
  | `(command| $r:expected_smt_result trace [ $name ] { $spec:traceSpec }) => elabTraceSpec r name spec
  | `(command| $r:expected_smt_result trace { $spec:traceSpec }) => elabTraceSpec r none spec
