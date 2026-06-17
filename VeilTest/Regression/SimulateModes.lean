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
#simulate interpreted {} {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

set_option veil.simulate.maxTraces 1 in
set_option veil.simulate.maxSteps 1 in
#guard_msgs(drop info, drop warning) in
#simulate interpreted {}

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

set_option veil.simulate.maxTraces 2 in
/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (config := { maxTraces := 1, maxSteps := 1, seed := 1 })

end SimulateModes
