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
#simulate interpreted {} {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

end SimulateDeadlock
