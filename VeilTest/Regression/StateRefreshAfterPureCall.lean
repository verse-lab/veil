import Veil

/-!
# Regression: state binders are refreshed after `pure (← someProc)`

A statement-level `pure (← proc)` runs `proc` (Lean lifts the `←` out and
executes it, mutating the state) and discards/forwards its value. Any subsequent
read of a field that `proc` wrote must observe the write. So in

```
pure (← set_x)   -- callee performs `x := true`, value discarded
y := x           -- must read x = true, hence y := true
```

the post-state must be `x = true, y = true`, and `x → y` is an invariant.

**History:** previously `pure $t` was passed through unchanged (the
self-acknowledged FIXME at DoNotation.lean:121-126: "we could have
`pure (← state_modifying_action)`, so this isn't sound"), so the cached `let mut
x` binder stayed stale and `y := x` read the pre-call `false`. Fixed 2026-06-11:
a `pure $t` whose argument runs a sub-computation is now handled like a bare-term
statement — bind the value, refresh the field binders, then re-emit `pure b` —
which preserves the statement's return value *and* refreshes the state.

`return $t` deliberately stays a passthrough: it short-circuits the rest of the
block, so no later statement can read the (stale) binders.

**Reference:** audit/02-action-dsl.md issue B2; audit/fix-plan-stale-binders.md.
**Source:** Veil/Frontend/DSL/Action/DoNotation.lean (`pure $t` case).

This file pins the CORRECT (post-fix) behavior, so it FAILS if the stale-binder
bug ever regresses.
-/

set_option linter.unusedVariables false
set_option veil.smt.trust false
set_option veil.printCounterexamples false

veil module StateRefreshAfterPureCall

individual x : Bool
individual y : Bool

#gen_state

after_init {
  x := false
  y := false
}

-- A Unit-returning procedure (no `return`) that WRITES a state field.
procedure set_x {
  x := true
}

-- The previously-buggy form: a state-modifying call invoked via `pure (← …)`
-- for effect. The field binders are now refreshed after it, so `y := x` reads
-- the up-to-date `x = true`.
action pure_call_then_read {
  pure (← set_x)
  y := x
}

-- Control: the same call as a bare statement (the bare-term path, which always
-- refreshed). Both actions must behave identically.
action bare_call_then_read {
  set_x
  y := x
}

-- Both actions establish `x = true ∧ y = true`, so `x → y` is an invariant.
invariant [y_tracks_x] x → y

#guard_msgs(drop warning) in
#gen_spec

-- Both actions preserve `y_tracks_x`.
/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  y_tracks_x ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  bare_call_then_read
    doesNotThrow ... ✅
    y_tracks_x ... ✅
  pure_call_then_read
    doesNotThrow ... ✅
    y_tracks_x ... ✅
-/
#guard_msgs(info, drop warning) in
#check_invariants

-- The correct outcome (`x ∧ y`) is reachable after the previously-buggy action;
-- the trace shows the corrected post-state `x = true, y = true`.
/--
info: ✅ Satisfying trace found
  State 0 (via init):
    x = false
    y = false
  State 1 (via pure_call_then_read):
    x = true
    y = true
-/
#guard_msgs(info, drop warning) in
sat trace {
  pure_call_then_read
  assert (x ∧ y)
}

-- The stale outcome (`x ∧ ¬y`) is NOT reachable anymore.
/-- error: No satisfying trace exists -/
#guard_msgs(error, drop info, drop warning) in
sat trace {
  pure_call_then_read
  assert (x ∧ ¬ y)
}

end StateRefreshAfterPureCall
