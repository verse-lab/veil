import Veil

/-!
# Regression: state binders are refreshed after `v ← someProc` (local-var target)

When a procedure that writes a state field is called and its result is bound to
a **local** variable (`let mut v := …; v ← proc`, which the preprocessor
normalizes to `v := ← proc`), every subsequent read of that field in the caller
must observe the callee's write. So in

```
let mut v := false
v ← set_x      -- callee performs `x := true`
y := x         -- must read x = true, hence y := true
```

the post-state must be `x = true, y = true`, and `x → y` is an invariant.

**History:** previously the local-variable branch of `assignState`
(DoNotation.lean) emitted the assignment with no `getState` refresh, so the
cached `let mut x` binder stayed at its pre-call value and `y := x` read the
STALE `false`. Fixed 2026-06-11 by refreshing the field binders after any
assignment whose RHS runs a sub-computation (`stmtRunsComputation`).

**Reference:** audit/02-action-dsl.md issue B1; audit/fix-plan-stale-binders.md.
**Source:** Veil/Frontend/DSL/Action/DoNotation.lean (`assignState`,
local/struct-target branch, conditional `getState` refresh).

This file pins the CORRECT (post-fix) behavior, so it FAILS if the stale-binder
bug ever regresses.
-/

set_option linter.unusedVariables false
set_option veil.smt.trust false
set_option veil.printCounterexamples false

veil module StateRefreshAfterCallToLocalVar

individual x : Bool
individual y : Bool

#gen_state

after_init {
  x := false
  y := false
}

-- A procedure that WRITES a state field (`x`) and RETURNS a value.
procedure set_x {
  x := true
  return true
}

-- The previously-buggy form: the call's result is bound to a LOCAL mutable
-- variable. `v ← set_x` is normalized to `v := ← set_x`; the RHS runs a
-- computation, so the field binders are now refreshed afterward and `y := x`
-- reads the up-to-date `x = true`.
action call_then_read_via_local {
  let mut v := false
  v ← set_x
  y := x
}

-- Control: the same logic via `let v ← set_x` (the generic-doElem path, which
-- always refreshed). Both actions must behave identically.
action control_fresh_read {
  let v ← set_x
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
  control_fresh_read
    doesNotThrow ... ✅
    y_tracks_x ... ✅
  call_then_read_via_local
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
  State 1 (via call_then_read_via_local):
    x = true
    y = true
-/
#guard_msgs(info, drop warning) in
sat trace {
  call_then_read_via_local
  assert (x ∧ y)
}

-- The stale outcome (`x ∧ ¬y`) is NOT reachable anymore.
/-- error: No satisfying trace exists -/
#guard_msgs(error, drop info, drop warning) in
sat trace {
  call_then_read_via_local
  assert (x ∧ ¬ y)
}

end StateRefreshAfterCallToLocalVar
