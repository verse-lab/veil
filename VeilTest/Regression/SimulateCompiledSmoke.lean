import Veil

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

#guard_msgs(drop info, drop warning) in
#simulate compiled {} {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

end SimulateCompiledSmoke
