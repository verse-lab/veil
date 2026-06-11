import Veil

/-!
# Regression: state binders are refreshed at branch entry of `if (← someProc) …`

When the condition of an `if` is a procedure call that writes a state field,
Lean lifts the call out and runs it BEFORE the `if`, so the branches must
observe the callee's writes. So in

```
if (← set_x) then    -- callee performs `x := true` and returns true
  y := x             -- must read x = true, hence y := true
```

the post-state must be `x = true, y = true`, and `x → y` is an invariant.

**History:** previously the `if`-statement case of `expandDoElemVeil`
(DoNotation.lean) passed the condition through and emitted no `getState`
refresh, so the `let mut x` binder stayed stale inside the branches and
`y := x` read the pre-call `false` (the self-acknowledged FIXME at
DoNotation.lean:104-109). Fixed 2026-06-11 by prepending a `getState` refresh to
each branch body when the condition runs a sub-computation
(`stmtRunsComputation`).

**Reference:** audit/02-action-dsl.md issue B2; audit/fix-plan-stale-binders.md.
**Source:** Veil/Frontend/DSL/Action/DoNotation.lean (`if`-statement case,
branch-entry `getState` refresh).

This file pins the CORRECT (post-fix) behavior, so it FAILS if the stale-branch
bug ever regresses.
-/

set_option linter.unusedVariables false
set_option veil.smt.trust false
set_option veil.printCounterexamples false

veil module StateRefreshInIfCondition

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

-- The previously-buggy form: the state-modifying call sits in the `if`
-- condition. The branch body now refreshes the binders, so `y := x` reads the
-- up-to-date `x = true`.
action call_in_if_condition {
  if (← set_x) then
    y := x
}

-- Control: the call is first bound to a local via `let c ← set_x` (the
-- generic-doElem path, which always refreshed). Both actions must behave
-- identically.
action control_if_condition {
  let c ← set_x
  if c then
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
  call_in_if_condition
    doesNotThrow ... ✅
    y_tracks_x ... ✅
  control_if_condition
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
  State 1 (via call_in_if_condition):
    x = true
    y = true
-/
#guard_msgs(info, drop warning) in
sat trace {
  call_in_if_condition
  assert (x ∧ y)
}

-- The stale outcome (`x ∧ ¬y`) is NOT reachable anymore.
/-- error: No satisfying trace exists -/
#guard_msgs(error, drop info, drop warning) in
sat trace {
  call_in_if_condition
  assert (x ∧ ¬ y)
}

end StateRefreshInIfCondition
