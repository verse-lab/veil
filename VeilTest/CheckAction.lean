import Veil

veil module CheckAction

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action keep_flag {
  pure ()
}

action break_flag {
  flag := true
}

invariant [flag_false] ¬ flag

#gen_spec

set_option veil.printCounterexamples false

/--
info: The following set of actions must preserve the invariant and successfully terminate:
  keep_flag
    doesNotThrow ... ✅
    flag_false ... ✅
-/
#guard_msgs in
#check_action keep_flag

/--
error: The following set of actions must preserve the invariant and successfully terminate:
  break_flag
    doesNotThrow ... ✅
    flag_false ... ❌
-/
#guard_msgs in
#check_action break_flag

/-- error: Unknown action missing for #check_action. Available actions: keep_flag, break_flag -/
#guard_msgs in
#check_action missing

end CheckAction
