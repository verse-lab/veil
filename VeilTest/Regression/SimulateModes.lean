import Veil

veil module SimulateModes

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
#simulate interpreted {} {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

#guard_msgs(drop info, drop warning) in
#simulate compiled {} {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate {} {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

end SimulateModes
