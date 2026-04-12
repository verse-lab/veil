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

#guard_msgs(drop info, drop warning) in
set_option veil.violationIsError false in
#simulate interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) }
  (seed := 1) (maxTraces := 1) (maxSteps := 1)
  assumptions_hold_by native_decide

#guard_msgs(drop info, drop warning) in
set_option veil.violationIsError false in
#simulate interpreted { node := Fin 3 } { leader := fun n => n == (0 : Fin 3) }
  (seed := 1) (maxTraces := 1) (maxSteps := 1)
  assumptions_hold_by decide

end SimulateAssumptionsTest
