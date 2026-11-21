module

public meta import Lean

public meta section

namespace Veil

declare_syntax_cat expected_smt_result
scoped syntax (name := expected_sat) "sat" : expected_smt_result
scoped syntax (name := expected_unsat) "unsat" : expected_smt_result

declare_syntax_cat trace_line
scoped syntax (name := any_action_star) "*" : trace_line
scoped syntax (name := any_action) atomic("any" "action") : trace_line
syntax traceAnyAction := any_action_star <|> any_action

scoped syntax (name := traceAnyNActions) "any " num " actions": trace_line

scoped syntax (name := traceActionName) ident : trace_line
syntax traceAction := (traceActionName <|> traceAnyAction <|> traceAnyNActions)

scoped syntax (name := traceAssertion) "assert " term:max : trace_line

syntax traceLine := (traceAction <|> traceAssertion)
syntax traceSpec := manyIndent(traceLine)

scoped syntax expected_smt_result "trace" ("[" ident "]")? "{"
  traceSpec
"}" (term)? : command

end Veil
