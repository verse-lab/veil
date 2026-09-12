import Veil

/-! Both native entry points are checked here. Each `#guard_msgs` waits for its
command, so the nested Lake builds do not race over shared dependency artifacts. -/

veil module SimulateCompiledSmoke

immutable individual enabled : Bool
individual flag : Bool

#gen_state

assumption [enabled_theory] enabled

after_init {
  flag := false
}

action set_flag {
  flag := true
}

invariant [safe_flag] true

#gen_spec

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate compiled {} { enabled := true } (seed := 1) (numTraces := 1) (maxSteps := 1)

/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check compiled {} { enabled := true } (sequential := true)

/--
error: ❌ Violation: assumption_failure (violates: enabled_theory)
Seed: 1
-/
#guard_msgs in
#simulate compiled {} { enabled := false } (seed := 1) (numTraces := 1) (maxSteps := 1)

/-- error: ❌ Violation: assumption_failure (violates: enabled_theory) -/
#guard_msgs in
#model_check compiled {} { enabled := false } (sequential := true)

end SimulateCompiledSmoke
