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

veil module EnumNamesInCTIs

-- Tests that CTIs refer to enum symbolic names, rather than the underlying
-- numeric values returned by the SMT solver.

enum EnumA = {nop}
enum EnumB = {a,b}

function req : EnumA → EnumB

after_init {
  pure ()
}

action foo {
  let x ← pick EnumA
  let y ← pick EnumB
  req x := y
}

invariant req T ≠ a

#gen_spec

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  inv_0 ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  foo
    doesNotThrow ... ✅
    inv_0 ... ❌
      Counterexample (WP):
        Pre-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.b]]
        Action: foo
      Counterexample (TR):
        Pre-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.b]]
        Action: foo
        Post-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.a]]
-/
#guard_msgs in
#check_invariants


end EnumNamesInCTIs
