import Veil

/-!
# `#simulate` reports invariant violations that already hold in the initial state

`simulateOnce` checks the invariants on the randomly chosen initial state before
taking any step, and reports a zero-step trace. This module has a single initial
state which violates the invariant, so the reported result does not depend on any
random choice.
-/

veil module SimulateInitialStateViolation

individual flag : Bool

#gen_state

after_init { flag := true }

action clear { flag := false }

invariant [safe] ¬ flag

#gen_spec

/--
error: ❌ Violation: safety_failure (violates: safe)
  State 0 (via init):
    flag = true
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1) (maxTraces := 1) (maxSteps := 3)

end SimulateInitialStateViolation
