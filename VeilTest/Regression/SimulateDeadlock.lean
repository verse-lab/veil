import Veil

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
