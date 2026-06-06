import Veil

open Veil.ModelChecker.Simulation

example :
  Veil.resolveSimulateTraceBounds
    { maxTraces := 10000, maxSteps := 100, seed := 0 }
    true true 7 3 = (10000, 100) := rfl

example :
  Veil.resolveSimulateTraceBounds
    { maxTraces := 10000, maxSteps := 100, seed := 0 }
    false false 7 3 = (7, 3) := rfl

example :
  Veil.resolveSimulateTraceBounds
    { maxTraces := 10000, maxSteps := 100, seed := 0 }
    true false 7 3 = (10000, 3) := rfl

example :
  Veil.resolveSimulateTraceBounds
    { maxTraces := 10000, maxSteps := 100, seed := 0 }
    false true 7 3 = (7, 100) := rfl

veil module SimulateConfigDefaults

individual flag : Bool
individual tripped : Bool

#gen_state

after_init {
  flag := false
  tripped := false
}

action set_flag {
  require !flag
  flag := true
}

action trip {
  require flag
  tripped := true
}

invariant [still_safe] ¬ tripped

#gen_spec

set_option veil.simulate.maxSteps 1 in
/--
error: ❌ Violation: safety_failure (violates: still_safe)
  State 0 (via init):
    flag = false
    tripped = false
  State 1 (via set_flag):
    flag = true
    tripped = false
  State 2 (via trip):
    flag = true
    tripped = true
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1) (maxTraces := 1) (maxSteps := 100)

set_option veil.simulate.maxSteps 1 in
/--
error: ❌ Violation: safety_failure (violates: still_safe)
  State 0 (via init):
    flag = false
    tripped = false
  State 1 (via set_flag):
    flag = true
    tripped = false
  State 2 (via trip):
    flag = true
    tripped = true
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (config := { maxTraces := 1, maxSteps := 100, seed := 1 })

end SimulateConfigDefaults
