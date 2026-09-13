import Veil

/-!
Distinct simulation outcomes: safety and assertion failures, deadlock before and
after a step, normal termination, and state constraints on initial/successor
states. Fixed seeds and forced transitions keep the diagnostics reproducible.
-/

set_option linter.unusedVariables false

veil module SimulateViolationModes

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action set_flag {
  flag := true
}

invariant [safe_flag] ¬ flag

#gen_spec

/--
error: ❌ Violation: safety_failure (violates: safe_flag)
  State 0 (via init):
    flag = false
  State 1 (via set_flag):
    flag = true
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1) (numTraces := 1) (maxSteps := 1)

-- The same violation is informational when violationIsError is disabled.
/--
info: ❌ Violation: safety_failure (violates: safe_flag)
  State 0 (via init):
    flag = false
  State 1 (via set_flag):
    flag = true
Seed: 1
-/
#guard_msgs in
set_option veil.violationIsError false in
#simulate interpreted {} {} (seed := 1) (numTraces := 1) (maxSteps := 1)

end SimulateViolationModes

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
#simulate interpreted {} {} (seed := 1) (numTraces := 1) (maxSteps := 3)

end SimulateInitialStateViolation

veil module SimulateAssertionFailure

type node

relation pending : node -> node -> Bool

#gen_state

after_init {
  pending M N := false
}

action send (n next : node) {
  assert false
  pending n next := true
}

invariant true

/-- error: This assertion might fail when called from send -/
#guard_msgs in
#gen_spec

/--
error: ❌ Violation: assertion_failure
  State 0 (via init):
    pending = []
  State 1 (via send(n=0, next=0)):
    pending = []
Seed: 1
-/
#guard_msgs in
#simulate interpreted { node := Fin 2 } {} (seed := 1) (numTraces := 1) (maxSteps := 1)

end SimulateAssertionFailure

veil module SimulateDeadlock

individual stuck : Bool

#gen_state

after_init {
  stuck := true
}

invariant true
termination false = true

/--
warning: you have not defined any actions for this specification; did you forget?
-/
#guard_msgs in
#gen_spec

/--
error: ❌ Violation: deadlock
  State 0 (via init):
    stuck = true
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1) (numTraces := 1) (maxSteps := 1)

end SimulateDeadlock

/-!
The module above deadlocks in the initial state. This one only deadlocks after a
step: `arm` is the single enabled action initially and nothing is enabled once it
has run, so the reported trace is independent of the seed.
-/

veil module SimulateDeadlockAfterStep

individual armed : Bool

#gen_state

after_init { armed := false }

action arm {
  require !armed
  armed := true
}

invariant [safe] true
termination armed = false

#gen_spec

/--
error: ❌ Violation: deadlock
  State 0 (via init):
    armed = false
  State 1 (via arm):
    armed = true
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1) (numTraces := 1) (maxSteps := 3)

end SimulateDeadlockAfterStep

veil module SimulateEmptySpec

after_init {
  pure ()
}

invariant true

/--
warning: you have not defined any actions for this specification; did you forget?
-/
#guard_msgs in
#gen_spec

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted { } {} (seed := 1) (numTraces := 1) (maxSteps := 1)

end SimulateEmptySpec

veil module SimulateEmptyFilteredInitStates

after_init {
  pure ()
}

invariant true

state_constraint [no_initial_states] False

/--
warning: you have not defined any actions for this specification; did you forget?
-/
#guard_msgs in
#gen_spec

/--
info: ✅ No initial states available after applying state constraints
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1) (numTraces := 5) (maxSteps := 1)

end SimulateEmptyFilteredInitStates

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
#simulate interpreted {} {} (seed := 1) (numTraces := 4) (maxSteps := 2)

end SimulateStateConstraintPrune
