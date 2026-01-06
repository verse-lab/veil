import Veil

veil module TraceFinalisesSpec

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action set_flag {
  flag := true;
}

invariant ¬ flag

/--
info: ✅ Satisfying trace found
  State 0 (via init):
    flag = false
-/
#guard_msgs in
sat trace { }

end TraceFinalisesSpec
