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

invariant [safe_flag] ¬ flag

#gen_spec

#guard_msgs(drop info, drop warning) in
set_option veil.violationIsError false in
#simulate interpreted {} {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

#guard_msgs(drop info, drop warning) in
set_option veil.violationIsError false in
#simulate compiled {} {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

#guard_msgs(drop info, drop warning) in
set_option veil.violationIsError false in
#simulate {} {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

end SimulateModes
