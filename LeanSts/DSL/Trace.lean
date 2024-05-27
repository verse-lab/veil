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


open Lean Elab Command RelationalTransitionSystem

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

def elabTraceSpec (r : TSyntax `expected_smt_result) (name : Option (TSyntax `ident)) (spec : TSyntax `traceSpec)
  : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  let th ← Command.runTermElabM fun vs => do
    let spec ← parseTraceSpec spec
    dbg_trace "{spec}"
    let name : Name ← match name with
    | some n => pure n.getId
    | none => mkFreshUserName (Name.mkSimple "trace")
    let th_id := mkIdent name
    let stateTp   <- PrettyPrinter.delab (<- stateTp vs)
    `(theorem $th_id $[$vd]* : invInit (σ := $stateTp) :=
      by unfold invInit ; sorry)
  dbg_trace "{th}"
  elabCommand $ th

elab_rules : command
  | `(command| $r:expected_smt_result trace [ $name ] { $spec:traceSpec }) => elabTraceSpec r name spec
  | `(command| $r:expected_smt_result trace { $spec:traceSpec }) => elabTraceSpec r none spec
