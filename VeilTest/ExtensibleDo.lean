import Veil

/-! Regression coverage specific to the extensible-`do` action elaborator. -/

-- Importing Veil must not change ordinary Lean `do` notation.
def ordinaryState : StateM Nat Nat := do
  let n ← get
  set (n + 1)
  return n

example : ordinaryState.run 4 = (4, 5) := rfl

-- Veil's existential-if parser must preserve native dependent `if` outside
-- action bodies.
def ordinaryDependentIf (p : Prop) [Decidable p] : Id Bool := do
  if h : p then
    have _proof := h
    return true
  else
    return false

example : ordinaryDependentIf True = true := rfl

set_option veil.smt.trust false
set_option veil.printCounterexamples false

veil module ExtensibleDoSemantics

individual x : Bool
individual y : Bool

#gen_state

after_init {
  x := false
  y := false
}

procedure set_x {
  x := true
  return true
}

-- Lean eagerly lifts the nested action before evaluating `&&`.
action eager_and {
  let _ := false && (← set_x)
  y := x
}

-- A nested action in a term-level `if` condition runs before selection.
action eager_term_if_condition {
  let selected := if (← set_x) then true else false
  if selected then
    y := x
}

-- Statement-level branches remain conditional.
action conditional_statement {
  if false then
    x := true
  y := !x
}

/--
warning: local `x` shadows mutable state component `x`; references to this name resolve to the local
-/
#guard_msgs(warning) in
action mutable_local_shadow {
  let mut x := false
  x := true
  y := x
}

/--
warning: local `x` shadows mutable state component `x`; references to this name resolve to the local
-/
#guard_msgs(warning) in
action shadow_scope_restores {
  if true then
    let x := false
    pure ()
  x := true
}

/--
warning: parameter `x` shadows mutable state component `x`; references to this name resolve to the parameter
-/
#guard_msgs(warning) in
action parameter_shadow (x : Bool) {
  return x
}

#guard_msgs(drop warning) in
#gen_spec

#guard_msgs(error, drop info, drop warning) in
sat trace {
  eager_and
  assert (x ∧ y)
}

#guard_msgs(error, drop info, drop warning) in
sat trace {
  eager_term_if_condition
  assert (x ∧ y)
}

#guard_msgs(error, drop info, drop warning) in
sat trace {
  conditional_statement
  assert (¬x ∧ y)
}

#guard_msgs(error, drop info, drop warning) in
sat trace {
  mutable_local_shadow
  assert (¬x ∧ y)
}

#guard_msgs(error, drop info, drop warning) in
sat trace {
  shadow_scope_restores
  assert x
}

end ExtensibleDoSemantics

veil module ExtensibleDoDiagnostics

type node
individual x : Bool
relation r : node → node → Bool

#gen_state

procedure set_x {
  x := true
  return true
}

/-- error: Error in action reject_term_if_branch: Nested action `← set_x` must be nested inside a `do` expression. -/
#guard_msgs(error, drop warning) in
action reject_term_if_branch {
  let _ := if true then (← set_x) else false
}

/--
error: Error in action reject_term_match_branch: Cannot lift nested action `← set_x` over a binder.
This error usually happens when you are trying to lift a method nested in a `fun`, `let`, or `match`-alternative, and it can often be fixed by adding a missing `do`.
-/
#guard_msgs(error, drop warning) in
action reject_term_match_branch {
  let _ := match true with
    | true => (← set_x)
    | false => false
}

/-- error: Error in action reject_deferred_veil: term-level `do` blocks cannot be stored, passed, or otherwise deferred inside Veil actions; execute the block directly as a statement or bind its result -/
#guard_msgs(error, drop warning) in
action reject_deferred_veil {
  let later := do
    set_x
  pure later
}

/-- error: Error in action reject_deferred_state_write: term-level `do` blocks cannot be stored, passed, or otherwise deferred inside Veil actions; execute the block directly as a statement or bind its result -/
#guard_msgs(error, drop warning) in
action reject_deferred_state_write {
  let later := do
    x := true
  pure later
}

/-- error: Error in action reject_deferred_other_monad: term-level `do` blocks cannot be stored, passed, or otherwise deferred inside Veil actions; execute the block directly as a statement or bind its result -/
#guard_msgs(error, drop warning) in
action reject_deferred_other_monad {
  let program : StateM Nat Nat := do
    let n ← get
    set (n + 1)
    return n
  pure program
}

/--
error: Error in action reject_immutable_shadow: this immutable local shadows a mutable state component with the same name; rename the local to assign to the state component
-/
#guard_msgs(error, drop warning) in
action reject_immutable_shadow {
  let x := false
  x := true
}

/--
error: Error in action reject_repeated_capital: you cannot use the same capitalized identifier more than once in an assignment; diagonal updates are not yet supported
-/
#guard_msgs(error, drop warning) in
action reject_repeated_capital {
  r N N := true
}

/-- error: Error in action reject_loop: `for` loops are not supported in Veil actions -/
#guard_msgs(error, drop warning) in
action reject_loop {
  for _ in [true] do
    x := true
}

/--
error: Error in action reject_recursion: recursive Veil action calls are not supported; action bodies must terminate structurally
-/
#guard_msgs(error, drop warning) in
action reject_recursion {
  reject_recursion
}

-- Since the existential `if` uses `:|`, Lean's native dependent `if h : p`
-- works inside actions.
#guard_msgs(drop warning) in
action native_dependent_if {
  if h : x = x then
    let _proof := h
    x := true
}

/--
error: Error in action reject_bad_witness_pattern: unsupported witness pattern for Veil existential `if`; expected an identifier or flat tuple of identifiers
-/
#guard_msgs(error, drop warning) in
action reject_bad_witness_pattern {
  if (¬ x) :| True then
    x := true
}

-- The pre-`:|` existential-if shape now parses as a dependent `if`, so stale
-- specs fail loudly with an unbound witness.
/--
error: Error in action old_existential_if_syntax: Unknown identifier `v`
-/
#guard_msgs(error, drop warning) in
action old_existential_if_syntax {
  if v : r v v then
    x := true
}

end ExtensibleDoDiagnostics
