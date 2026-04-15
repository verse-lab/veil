import Veil

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
#simulate interpreted {} {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

#guard_msgs(drop info, drop warning) in
set_option veil.violationIsError false in
#simulate compiled {} {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

/--
error: ❌ Violation: safety_failure (violates: safe_flag)
  State 0 (via init):
    flag = false
  State 1 (via set_flag):
    flag = true
Seed: 1
-/
#guard_msgs in
#simulate {} {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

end SimulateViolationModes
