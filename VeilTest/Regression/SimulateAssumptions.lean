import Veil

set_option linter.unusedVariables false

veil module SimulateAssumptionsTest

type node

immutable relation leader : node → Bool
relation flag : node → Bool

#gen_state

assumption ∀ (n1 n2 : node), leader n1 ∧ leader n2 → n1 = n2

after_init {
  flag N := false
}

action do_something (n : node) {
  require leader n
  flag n := true
}

invariant true

#gen_spec

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) }
  (seed := 1) (maxTraces := 1) (maxSteps := 1)
  assumptions_hold_by native_decide

/--
error: Tactic `native_decide` evaluated that the proposition
  assumption_0 { leader := fun n => n == 0 || n == 1 }
is false
---
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) || n == (1 : Fin 3) }
  (seed := 1) (maxTraces := 1) (maxSteps := 1)
  assumptions_hold_by native_decide

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) || n == (1 : Fin 3) }
  (seed := 1) (maxTraces := 1) (maxSteps := 1)

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) }
  (seed := 1) (maxTraces := 1) (maxSteps := 1)
  assumptions_hold_by decide

#guard_msgs(drop info, drop warning) in
#simulate compiled { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) }
  (seed := 1) (maxTraces := 1) (maxSteps := 1)
  assumptions_hold_by native_decide

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) }
  (seed := 1) (maxTraces := 1) (maxSteps := 1)
  assumptions_hold_by native_decide

end SimulateAssumptionsTest

veil module SimulateAssumptionsCustomProof

type node

immutable function weight : node → Nat

relation active : node → Bool

#gen_state

assumption ∀ (n : node), 0 < weight n
assumption ∀ (n1 n2 : node), weight n1 = weight n2 → n1 = n2

after_init {
  active N := false
}

action activate (n : node) {
  active n := true
}

invariant true

#gen_spec

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted { node := Fin 3 } { weight := fun (n : Fin 3) => n.val + 1 }
  (seed := 1) (maxTraces := 1) (maxSteps := 1)
  assumptions_hold_by
    constructor <;> decide

end SimulateAssumptionsCustomProof
