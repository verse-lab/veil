import Veil

veil module VeilVarArbitrary

individual observed : Bool

#gen_state

after_init {
  observed := false
}

action copy_veil_var {
  veil_var x : Bool
  observed := x
}

invariant [observed_false] observed = false

#gen_spec

set_option veil.printCounterexamples false

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  observed_false ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  copy_veil_var
    doesNotThrow ... ✅
    observed_false ... ❌
-/
#guard_msgs in
#check_invariants

end VeilVarArbitrary

veil module VeilVarMutable

individual observed : Bool

#gen_state

after_init {
  observed := false
}

action overwrite_veil_var {
  veil_var x : Bool
  x := false
  observed := x
}

invariant [observed_false] observed = false

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  observed_false ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  overwrite_veil_var
    doesNotThrow ... ✅
    observed_false ... ✅
-/
#guard_msgs in
#check_invariants

end VeilVarMutable
