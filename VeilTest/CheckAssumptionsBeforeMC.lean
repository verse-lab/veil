import Veil

set_option linter.unusedVariables false

/-! # Tests for `assumptions_hold_by` clause in `#model_check`

These tests verify that the `assumptions_hold_by` trailing clause correctly
checks whether the provided theory satisfies the module's assumptions.
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

-- Test 1: Valid theory with assumptions_hold_by (default tactic: native_decide)
/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) } assumptions_hold_by native_decide

-- Test 2: Invalid theory with assumptions_hold_by should fail
/--
error: Tactic `native_decide` evaluated that the proposition
  assumption_0 { leader := fun n => n == 0 || n == 1 }
is false
---
info: ✅ No violation (explored 4 states)
-/
#guard_msgs in
#model_check interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) || n == (1 : Fin 3) } assumptions_hold_by native_decide

-- Test 3: Invalid theory without assumptions_hold_by — no assumption error (backward compat)
#model_check interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) || n == (1 : Fin 3) }

-- Test 4: Valid theory with custom tactic
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

-- Test 5: Valid theory proved with a custom multi-step tactic
/-- info: ✅ No violation (explored 8 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 3 } { weight := fun (n : Fin 3) => n.val + 1 }
assumptions_hold_by
  -- Assumptions is already unfolded by the prelude `dsimp`;
  -- just close each conjunct individually.
  constructor <;> decide

end CheckAssumptionsCustomProof
