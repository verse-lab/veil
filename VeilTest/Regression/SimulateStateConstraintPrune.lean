import Veil

/-!
# `#simulate` applies state constraints while walking, not just to initial states

`SimulateEmptyFilteredInitStates` covers the case where the constraints leave no
initial state at all. Here the initial state is allowed but the only successor is
pruned, so the invariant becomes unreachable and no seed can produce a violation.
`SimulateStateConstraintPruneOff` is the same specification without the constraint,
where the single enabled action always violates the invariant.
-/

veil module SimulateStateConstraintPrune

individual b : Bool

#gen_state

after_init { b := false }

action set_b { b := true }

invariant [safe] ¬ b
state_constraint [keep_b_false] ¬ b

#gen_spec

/--
info: ✅ No violation in 4 traces
Trace depths: 0x4
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1) (maxTraces := 4) (maxSteps := 2)

end SimulateStateConstraintPrune


veil module SimulateStateConstraintPruneOff

individual b : Bool

#gen_state

after_init { b := false }

action set_b { b := true }

invariant [safe] ¬ b

#gen_spec

/--
error: ❌ Violation: safety_failure (violates: safe)
  State 0 (via init):
    b = false
  State 1 (via set_b):
    b = true
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1) (maxTraces := 4) (maxSteps := 2)

end SimulateStateConstraintPruneOff
