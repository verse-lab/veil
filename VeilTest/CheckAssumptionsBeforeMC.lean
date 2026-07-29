import Veil

set_option linter.unusedVariables false

/-! # Tests for checking assumptions before model checking

These tests verify that `#model_check` evaluates whether the provided theory
satisfies the module's assumptions before exploring states. The optional
`assumptions_hold_by` trailing clause is still accepted as an additional static
proof check.
-/

veil module CheckAssumptionsTest

type node

immutable relation leader : node → Bool

relation flag : node → Bool

#gen_state

assumption ∀ (n1 n2 : node), leader n1 ∧ leader n2 → n1 = n2

after_init {
  flag N := false
}

action do_something (n : node) {
  require leader n;
  flag n := true
}

invariant true

#gen_spec

-- Test 1: Valid theory without assumptions_hold_by
/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) }

-- Test 2: Invalid theory fails before exploring states
/-- error: ❌ Violation: assumption_failure (violates: assumption_0) -/
#guard_msgs in
#model_check interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) || n == (1 : Fin 3) }

-- Test 3: Valid theory with optional static proof tactic
/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) } assumptions_hold_by decide

end CheckAssumptionsTest

/-! ## Module with multiple assumptions requiring a custom tactic proof -/

veil module CheckAssumptionsCustomProof

type node

immutable function weight : node → Nat

relation active : node → Bool

#gen_state

assumption ∀ (n : node), 0 < weight n
assumption ∀ (n1 n2 : node), weight n1 = weight n2 → n1 = n2

after_init { active N := false }

action activate (n : node) {
  active n := true
}

invariant true

#gen_spec

-- Test 4: Valid theory proved with a custom multi-step tactic
/-- info: ✅ No violation (explored 8 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 3 } { weight := fun (n : Fin 3) => n.val + 1 }
assumptions_hold_by
  -- Assumptions is already unfolded by the prelude `dsimp`;
  -- just close each conjunct individually.
  constructor <;> decide

end CheckAssumptionsCustomProof
