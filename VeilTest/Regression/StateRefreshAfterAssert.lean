import Veil

/-!
# Regression: current-state coherence after a call in an argument position

Lean lifts a call embedded as `(← p)` into a preceding bind. Veil opens the
current state before the assertion-bearing statement and before its successor,
so a later field read observes the call's post-state.
action embedded {
assert (← set_x) -- set_x performs x := true
y := x -- must read x = true, hence y := true
}
This file pins that behavior for `assert`, `require`, and `assume`.
-/

set_option linter.unusedVariables false
set_option veil.smt.trust false
set_option veil.printCounterexamples false

veil module StateRefreshInEmbeddedComputation

individual x : Bool
individual y : Bool

#gen_state

after_init {
  x := false
  y := false
}

-- Writes a state field and returns a value.
procedure set_x {
  x := true
  return true
}

-- Control: bind the call explicitly.
action c_let_assert {
  let h ← set_x
  assert h
  y := x
}

action p_assert  { assert (← set_x)  ; y := x }
action p_require { require (← set_x) ; y := x }
action p_assume  { assume (← set_x)  ; y := x }

-- After any of these, `set_x` has run, so `x = true` and `y := x` gives
-- `y = true`. The invariant holds for all four.
invariant [xy] x = y

#guard_msgs(drop warning) in
#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  xy ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  p_require
    doesNotThrow ... ✅
    xy ... ✅
  c_let_assert
    doesNotThrow ... ✅
    xy ... ✅
  p_assert
    doesNotThrow ... ✅
    xy ... ✅
  p_assume
    doesNotThrow ... ✅
    xy ... ✅
-/
#guard_msgs(info, drop warning) in
#check_invariants

end StateRefreshInEmbeddedComputation
