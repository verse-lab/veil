import Veil

veil module BmcSat

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action set_flag {
  flag := true;
}

invariant ¬ flag

#gen_spec

/--
info: ✅ Satisfying trace found
  State 0 (via init):
    flag = false
-/
#guard_msgs in
sat trace { }

#guard_msgs(drop warning, drop info) in
sat trace {
  set_flag
  set_flag
}

/-- error: No satisfying trace exists -/
#guard_msgs in
sat trace {
  assert False
}

#guard_msgs(drop warning, drop info) in
sat trace {
  any 3 actions
}

end BmcSat
