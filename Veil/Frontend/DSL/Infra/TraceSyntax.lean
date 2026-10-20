module

public meta import Lean

public meta section

declare_syntax_cat expected_smt_result
syntax (name := expected_sat) "sat" : expected_smt_result
syntax (name := expected_unsat) "unsat" : expected_smt_result

declare_syntax_cat trace_line
syntax (name := any_action_star) "*" : trace_line
syntax (name := any_action) atomic("any" "action") : trace_line
syntax traceAnyAction := any_action_star <|> any_action

syntax (name := traceAnyNActions) "any " num " actions": trace_line

syntax (name := traceActionName) ident (ppSpace colGt term:max)* : trace_line
syntax traceAction := (traceActionName <|> traceAnyAction <|> traceAnyNActions)

syntax (name := traceAssertion) "assert " term:max : trace_line

syntax traceLine := (traceAction <|> traceAssertion)
syntax traceSpec := manyIndent(traceLine)

/-- Explicit existential witnesses shared by all lines of a trace. -/
syntax traceBinder := "(" ident+ " : " term ")"

syntax expected_smt_result "trace" ("[" ident "]")? traceBinder* "{"
  traceSpec
"}" (term)? : command


