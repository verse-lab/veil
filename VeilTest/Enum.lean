import Veil

veil module EnumTest
enum switch_state = {on, off}
enum one_elem = {a}

type node

individual state : switch_state

#gen_state

after_init {
  state := off
}

action random_switch {
  let s ← pick switch_state
  state := s
}

invariant [all] state = on ∨ state = off
invariant [neq] on ≠ off

#gen_spec


/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  all ... ✅
  neq ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  random_switch
    doesNotThrow ... ✅
    all ... ✅
    neq ... ✅
-/
#guard_msgs in
#check_invariants -- verifies

#guard_msgs(drop info, drop warning) in
sat trace {
  random_switch
}

end EnumTest

-- We encountered a strange bug here with the instances. If we have enums in
-- different namespaces/modules, then basic synthesis of stuff like `#synth BEq
-- Nat` will fail. To fix this, we now use `scoped instance`s everywhere.

veil module EnumTest2

enum one_elem = {a}
individual state : one_elem

#gen_state

after_init {
  state := a
}

action random_switch {
  let s ← pick one_elem
  state := s
}

invariant [all] state = a

#gen_spec

end EnumTest2
