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
#simulate interpreted {} {} (seed := 1) (numTraces := 1) (maxSteps := 1)

#guard_msgs(drop info, drop warning) in
#simulate interpreted {} {} (seed := 1) (numTraces := 1) (maxSteps := 1)

-- With no bound written in the command, both bounds come from the options.
-- The asserted trace count discriminates the option value from the structure default.
set_option veil.simulate.numTraces 3 in
set_option veil.simulate.maxSteps 1 in
/--
info: ✅ No violation in 3 traces
Trace depths: 1x3
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1)

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (seed := 1) (numTraces := 1) (maxSteps := 1)

set_option veil.simulate.numTraces 2 in
/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate interpreted {} {} (config := { numTraces := 1, maxSteps := 1, seed := 1 })

end SimulateModes
