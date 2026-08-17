import Veil

/-!
# Regression: indexed updates use the current represented field after a call

In field-representation mode (the DEFAULT, `Module._useFieldRepTC := true`) each
field `f` is exposed through cached `let mut` binders `f_conc`/`f`. After a call
that may write field `r`, a subsequent partial update `r a := v` must apply to
the CURRENT value of `r` (including the callee's writes), not a stale snapshot.
So in

```
procedure set_all_r { r N := true; return true }     -- writes EVERY entry of r
action a (a : node) {
  w ← set_all_r     -- callee sets all entries of r to true
  r a := true       -- partial update of one entry
}
```

the post-state must have `∀ N, r N`, and `r N → r M` is an invariant.

The assignment compiler opens the state after the arrow RHS and bases
`FieldRepresentation.setSingle` on that current concrete field. This file
pins preservation of the callee's other writes.
-/

set_option linter.unusedVariables false
set_option veil.smt.trust false
set_option veil.printCounterexamples false

veil module FieldRepRefreshAfterCall

type node

-- Force field-representation mode explicitly (it is also the default).
veil_set_option useFieldRepTC true

relation r : node → Bool
individual w : Bool

#gen_state

after_init {
  r N := false
  w := false
}

-- A procedure that writes EVERY entry of `r` and RETURNS a value.
procedure set_all_r {
  r N := true
  return true
}

-- `w ← set_all_r` binds the result to a state component. The following
-- indexed update bases itself on the callee's all-true `r`.
action call_then_partial_update (a : node) {
  w ← set_all_r
  r a := true
}

-- Control: bind the result to a local variable; both forms behave identically.
action control_write_back (a : node) {
  let v ← set_all_r
  r a := true
}

-- Both actions leave `r` uniformly true, so `r N → r M` is an invariant.
invariant [r_uniform] r N → r M

#guard_msgs(drop warning) in
#gen_spec

-- Both actions preserve `r_uniform`.
/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  r_uniform ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  control_write_back
    doesNotThrow ... ✅
    r_uniform ... ✅
  call_then_partial_update
    doesNotThrow ... ✅
    r_uniform ... ✅
-/
#guard_msgs(info, drop warning) in
#check_invariants

-- The correct outcome (`∀ N, r N`, with at least two distinct nodes) is
-- reachable after the previously-buggy action (no error ⇒ trace found).
#guard_msgs(error, drop info, drop warning) in
sat trace {
  assert (∃ (N M : node), N ≠ M)
  call_then_partial_update
  assert (∀ N, r N)
}

-- The discarded-writes outcome (some entry still false) is NOT reachable.
/-- error: No satisfying trace exists -/
#guard_msgs(error, drop info, drop warning) in
sat trace {
  call_then_partial_update
  assert (∃ N M, r N ∧ ¬ r M)
}

end FieldRepRefreshAfterCall
