import Veil

/-!
# Regression: state binders are refreshed after a call in an argument position

Veil's action do-notation caches each mutable state field in a binder and
refreshes it (re-reads `get`) after a statement that runs a computation. The
refresh is applied per syntactic shape. The shapes that return `#[stx]`
unchanged (`DoNotation.lean`, the `assume` / `require` / `assert` group) do not
refresh, so a read *after* a call embedded as `(← p)` in one of those positions
observes the pre-call value.
action embedded {
assert (← set_x) -- set_x performs x := true
y := x -- must read x = true, hence y := true
}


The elaborated post-state shows it directly (`set_option trace.veil.desugar`):

    embedded   __veil_post ... { x := true, y := State.x __veil_st }
    hoisted    __veil_post ... { x := true, y := true }

`embedded` assigns `y` from `__veil_st`, the state captured *before* the call.

**Effect.** A false rejection: a specification that is correct is reported as
violating its invariant. Confirmed for `assert`, `require` and `assume`.
`return (← p)` is unaffected -- the caller refreshes after the call, so a stale
binding cannot escape the callee. `let x :| (← p)` cannot host the form at all
(the lift over a binder is rejected).

This file pins the CORRECT (post-fix) behaviour, so it FAILS if the defect is
present.
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

-- Control: the call is bound by `let`, which refreshes.
action c_let {
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
  p_assert
    doesNotThrow ... ✅
    xy ... ✅
  c_let
    doesNotThrow ... ✅
    xy ... ✅
  p_assume
    doesNotThrow ... ✅
    xy ... ✅
-/
#guard_msgs(info, drop warning) in
#check_invariants

end StateRefreshInEmbeddedComputation
