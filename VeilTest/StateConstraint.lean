import Veil

set_option linter.unusedVariables false

/-! # State Constraint Tests

These tests verify that `state_constraint` properly filters states during
model checking. State constraints silently skip states that don't satisfy
the constraint, reducing the explored state space.
-/

veil module StateConstraintTest

type node

relation active : node → Bool

#gen_state

after_init {
  active N := false
}

action activate (n : node) {
  active n := true
}

action deactivate (n : node) {
  active n := false
}

invariant true

-- Only explore states where at most one node is active
state_constraint [at_most_one_active] active M ∧ active N → M = N

#gen_spec

-- With Fin 3 and no constraint, there would be 2^3 = 8 states.
-- With the "at most 1 active" constraint, only 4 states are explored:
-- {000, 100, 010, 001}
/-- info: ✅ No violation (explored 4 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 3 } {}

end StateConstraintTest
