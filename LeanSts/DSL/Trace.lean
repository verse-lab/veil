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
"}" term : command


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

def mkAndNStx (args : List (TSyntax `term)) : TermElabM (TSyntax `term) :=
  match args with
  | [] => `(term|True)
  | [a] => pure a
  | x :: xs => do
    let xs ← mkAndNStx xs
    `(term|($x ∧ $xs))

/- From: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/binderIdent.20vs.20Ident -/
def toBinderIdent (i : Ident) : TSyntax ``binderIdent := Unhygienic.run <|
  withRef i `(binderIdent| $i:ident)

def elabTraceSpec (r : TSyntax `expected_smt_result) (name : Option (TSyntax `ident)) (spec : TSyntax `traceSpec) (pf : TSyntax `term)
  : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  let th ← Command.runTermElabM fun vs => do
    let spec ← parseTraceSpec spec
    let numActions := spec.foldl (fun n s => match s with | TraceSpecLine.assertion _ => n | _ => n + 1) 0
    let numStates := numActions + 1
    let stateNames := List.toArray $ (List.range numStates).map fun i => mkIdent (Name.mkSimple s!"st{i}")

    /- Track which state assertions refer to. -/
    let mut currStateId := 0
    /- Which assertions, including state-transitions, does the spec contain. -/
    let mut assertions : Array (TSyntax `term) := #[]
    assertions := assertions.push (← `(term|(RelationalTransitionSystem.init $(stateNames[0]!))))
    for s in spec do
      let currState := stateNames[currStateId]!
      match s with
      | TraceSpecLine.action n => do
        let nextState := stateNames[currStateId + 1]!
        let actApp := mkAppN (Expr.const n []) vs
        let stx ← PrettyPrinter.delab actApp
        -- FIXME: make a correct application, i.e. providing the `vd` names
        let t ← `(term|($stx $currState $nextState))
        assertions := assertions.push t
        currStateId := currStateId + 1
      | TraceSpecLine.anyAction => do
        let nextState := stateNames[currStateId + 1]!
        let t ← `(term|(RelationalTransitionSystem.next $currState $nextState))
        assertions := assertions.push t
        currStateId := currStateId + 1
      | TraceSpecLine.assertion t => do
        -- Elaborate assertions in the same way we elaborate invariants.
        -- See `elab "invariant"` in `DSL.lean`.
        let stx <- funcasesM t vs
        let t ← elabBindersAndCapitals #[] vs stx fun _ e => do
          let e <- my_delab e
          `(fun $(mkIdent "st") => $e: term)
        let t ← `(term|($t $currState))
        assertions := assertions.push t
    let name : Name ← match name with
    | some n => pure n.getId
    | none => mkFreshUserName (Name.mkSimple "trace")
    let th_id := mkIdent name
    let conjunction ← mkAndNStx assertions.toList
    -- sat trace -> ∃ states, (conjunction of assertions)
    -- unsat trace -> ∀ states, ¬ (conjunction of assertions)
    let stateTp ← PrettyPrinter.delab (<- stateTp vs)
    let binderNames : Array (TSyntax ``Lean.binderIdent) := stateNames.map toBinderIdent
    let assertion ← match r with
    | `(expected_smt_result| unsat) => `(∀ ($[$stateNames]* : $stateTp), ¬ $conjunction)
    | `(expected_smt_result| sat) => `(∃ ($[$binderNames]* : $stateTp), $conjunction)
    | _ => dbg_trace "expected result is neither sat nor unsat!" ; unreachable!
    `(theorem $th_id $[$vd]* : $assertion := by exact $pf)
  elabCommand $ th

elab_rules : command
  | `(command| $r:expected_smt_result trace [ $name ] { $spec:traceSpec } $pf) => elabTraceSpec r name spec pf
  | `(command| $r:expected_smt_result trace { $spec:traceSpec } $pf) => elabTraceSpec r none spec pf
