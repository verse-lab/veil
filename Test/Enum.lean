import Veil

veil module EnumTest
enum switch_state = {on, off}

type node

individual state : switch_state

-- FIXME: We do not currently define `switch_state.on` and `switch_state.off`
-- because I want them to be proper definitions, rather than notation
-- and I couldn't figure out how to make the type implicit.
-- local notation "switch_state.on" => @switch_state_Enum.on switch_state switch_state_isEnum
-- We can do this, but it seems this isn't usable within the module:
-- abbrev switch_state.on {switch_state : outParam Type} [self : switch_state_Enum switch_state] := @switch_state_Enum.on switch_state self

#gen_state

after_init {
  state := off
}

action random_switch = {
  let s ← pick switch_state
  state := s
}

invariant [all] state = on ∨ state = off
invariant [neq] on ≠ off

#gen_spec

set_option veil.smt.translator "lean-smt"

/--
info: Initialization must establish the invariant:
  all ... ✅
  neq ... ✅
The following set of actions must preserve the invariant:
  random_switch
    all ... ✅
    neq ... ✅
---
warning: Trusting the SMT solver for 4 theorems.
-/
#guard_msgs in
#check_invariants -- verifies

#guard_msgs(drop info, drop warning) in
sat trace {
  random_switch
} by bmc_sat

end EnumTest

-- #check EnumTest.switch_state_Enum.on
-- #check EnumTest.switch_state.on


veil module EnumTest2

enum one_elem = {a}
individual state : one_elem

#gen_state

after_init {
  state := a
}

action random_switch = {
  let s ← pick one_elem
  state := s
}

invariant [all] state = a

#gen_spec

set_option veil.smt.model.minimize true
/--
info:
(this model is minimized)
interpreted sort Bool
sort one_elem = #[one_elem0]
one_elem_isEnum.a = one_elem0
st0.state = one_elem0
-/
#guard_msgs(info, drop warning) in
sat trace {random_switch} by bmc_sat

end EnumTest2
