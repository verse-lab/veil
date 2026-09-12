import Veil

/-! Both native entry points are checked here. Each `#guard_msgs` waits for its
command, so the nested Lake builds do not race over shared dependency artifacts. -/

veil module SimulateCompiledSmoke

individual flag : Bool

#gen_state

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
#simulate compiled {} {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check compiled {} {} (sequential := true)

end SimulateCompiledSmoke
