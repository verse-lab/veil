import VeilTest.ActionExecution

/-!
Concrete tests for ordinary Lean `do` constructs and for current-state
coherence around nested Veil computations.
-/

set_option linter.unusedVariables false

open VeilTest.ActionExecution

veil module ActionExecutionControlFlow

immutable individual bias : Nat
individual x : Nat
individual y : Nat
individual flag : Bool

#gen_state

procedure set_x_return (value : Nat) {
  x := value
  return x
}

procedure set_flag {
  flag := true
  return flag
}

-- A normal bind observes the state written by its callee.
procedure call_then_read {
  let value ← set_x_return 7
  y := x + value
  return (value, y)
}

-- Arrow reassignment of a local preserves the callee's global state effects.
procedure local_arrow_then_read {
  let mut value := 0
  value ← set_x_return 6
  y := x + value
  return (value, y)
}

-- Lean eagerly lifts `( ← ...)` from an operand of `&&`.
procedure eager_and {
  let conjunction := false && (← set_flag)
  x := if flag then 1 else 0
  return conjunction
}

-- An effect in a term-level `if` condition runs before branch selection.
procedure eager_if_condition {
  let selected := if (← set_flag) then 11 else 12
  x := selected
  return flag
}

-- A statement-level branch remains genuinely conditional.
procedure statement_if {
  if false then
    let _ ← set_flag
  x := if flag then 1 else 2
  return flag
}

-- `unless`, `if let`, and `match` are delegated to Lean's handlers.
procedure structured_control (input : Option Nat) {
  unless flag do
    x := x + 1
  if let some value := input then
    x := x + value
  else
    x := x + 20
  match input with
  | some value => x := x + value + 2
  | none => x := x + 30
  return x
}

-- Refutable `let` with a fallback is Lean's `doLetElse` construct.
procedure let_else_control (input : Option Nat) {
  let some value := input | return 99
  x := value
  return x
}

-- Early returns use Lean's continuation/join-point machinery.
procedure early_return (stop : Bool) {
  x := x + 1
  if stop then
    return x
  x := x + 10
  return x
}

-- Exercise typed patterns, local mutation, and an immediate nested `do`.
procedure locals_and_nested_do {
  let (a, b) : Nat × Nat := (2, 3)
  have increment : Nat := 2
  let mut total := a
  total := total + b + increment
  do
    x := total
    y := x + 1
  return (total, y)
}

-- A nested block on a bind RHS executes immediately and returns its result.
procedure bind_nested_do {
  let value ← do
    x := 9
    pure (x + 1)
  y := value
  return (x, y)
}

/--
warning: local `x` shadows mutable state component `x`; references to this name resolve to the local
-/
#guard_msgs(warning) in
procedure theory_and_shadow {
  let x := bias
  y := x + 1
  return x
}

/--
warning: parameter `x` shadows mutable state component `x`; references to this name resolve to the parameter
-/
#guard_msgs(warning) in
procedure parameter_shadow (x : Nat) {
  y := x
  return x
}

/--
warning: local `x` shadows mutable state component `x`; references to this name resolve to the local
-/
#guard_msgs(warning) in
procedure shadow_scope_restores {
  if true then
    let x := 99
    y := x
  x := 4
  return (x, y)
}

def background : Theory := { bias := 40 }
def initial : State FieldConcreteType := { x := 1, y := 2, flag := false }

def callResult := __veil_exec_action% {} background initial call_then_read
#guard exactlyOneSuccess callResult fun value state =>
  value == (7, 14) && state.x == 7 && state.y == 14 && !state.flag

def arrowResult := __veil_exec_action% {} background initial local_arrow_then_read
#guard exactlyOneSuccess arrowResult fun value state =>
  value == (6, 12) && state.x == 6 && state.y == 12 && !state.flag

def eagerAndResult := __veil_exec_action% {} background initial eager_and
#guard exactlyOneSuccess eagerAndResult fun value state =>
  !value && state.flag && state.x == 1 && state.y == 2

def eagerIfResult := __veil_exec_action% {} background initial eager_if_condition
#guard exactlyOneSuccess eagerIfResult fun value state =>
  value && state.flag && state.x == 11 && state.y == 2

def statementIfResult := __veil_exec_action% {} background initial statement_if
#guard exactlyOneSuccess statementIfResult fun value state =>
  !value && !state.flag && state.x == 2 && state.y == 2

def structuredSomeResult :=
  __veil_exec_action% {} background initial (structured_control (some 3))
#guard exactlyOneSuccess structuredSomeResult fun value state =>
  value == 10 && state.x == 10 && state.y == 2 && !state.flag

def structuredNoneResult :=
  __veil_exec_action% {} background initial (structured_control none)
#guard exactlyOneSuccess structuredNoneResult fun value state =>
  value == 52 && state.x == 52 && state.y == 2 && !state.flag

def letElseSomeResult :=
  __veil_exec_action% {} background initial (let_else_control (some 8))
#guard exactlyOneSuccess letElseSomeResult fun value state =>
  value == 8 && state.x == 8 && state.y == 2

def letElseNoneResult :=
  __veil_exec_action% {} background initial (let_else_control none)
#guard exactlyOneSuccess letElseNoneResult fun value state =>
  value == 99 && state.x == 1 && state.y == 2

def earlyStopResult := __veil_exec_action% {} background initial (early_return true)
#guard exactlyOneSuccess earlyStopResult fun value state =>
  value == 2 && state.x == 2 && state.y == 2

def earlyContinueResult := __veil_exec_action% {} background initial (early_return false)
#guard exactlyOneSuccess earlyContinueResult fun value state =>
  value == 12 && state.x == 12 && state.y == 2

def nestedResult := __veil_exec_action% {} background initial locals_and_nested_do
#guard exactlyOneSuccess nestedResult fun value state =>
  value == (7, 8) && state.x == 7 && state.y == 8

def boundNestedResult := __veil_exec_action% {} background initial bind_nested_do
#guard exactlyOneSuccess boundNestedResult fun value state =>
  value == (9, 10) && state.x == 9 && state.y == 10

def shadowResult := __veil_exec_action% {} background initial theory_and_shadow
#guard exactlyOneSuccess shadowResult fun value state =>
  value == 40 && state.x == 1 && state.y == 41

def parameterShadowResult :=
  __veil_exec_action% {} background initial (parameter_shadow 23)
#guard exactlyOneSuccess parameterShadowResult fun value state =>
  value == 23 && state.x == 1 && state.y == 23

def restoredScopeResult :=
  __veil_exec_action% {} background initial shadow_scope_restores
#guard exactlyOneSuccess restoredScopeResult fun value state =>
  value == (4, 99) && state.x == 4 && state.y == 99

end ActionExecutionControlFlow
