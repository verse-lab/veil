import Veil

veil module BmcSat

individual flag : Prop

#gen_state

after_init {
  flag := False
}

action set_flag = {
  flag := True;
}

invariant ¬ flag

#gen_spec

#guard_msgs(drop warning) in
sat trace { } by bmc_sat

#guard_msgs(drop warning, drop info) in
sat trace {
  set_flag
  set_flag
} by bmc_sat

/-- error: the goal is false -/
#guard_msgs in
sat trace {
  assert False
} by bmc_sat

end BmcSat
