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
  inv_0 ... ❌
      Counterexample (WP):
        Theory:
          EnumA_Enum.nop = EnumNamesInCTIs.EnumA_IndT.nop
          EnumB_Enum.a = EnumNamesInCTIs.EnumB_IndT.a
          EnumB_Enum.b = EnumNamesInCTIs.EnumB_IndT.b
        Pre-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.a]]
        Action: initializer
      Counterexample (TR):
        Theory:
          EnumA_Enum.nop = EnumNamesInCTIs.EnumA_IndT.nop
          EnumB_Enum.a = EnumNamesInCTIs.EnumB_IndT.a
          EnumB_Enum.b = EnumNamesInCTIs.EnumB_IndT.b
        Pre-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.a]]
        Action: initializer
        Post-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.a]]
The following set of actions must preserve the invariant and successfully terminate:
  foo
    doesNotThrow ... ✅
    inv_0 ... ❌
      Counterexample (WP):
        Theory:
          EnumA_Enum.nop = EnumNamesInCTIs.EnumA_IndT.nop
          EnumB_Enum.a = EnumNamesInCTIs.EnumB_IndT.a
          EnumB_Enum.b = EnumNamesInCTIs.EnumB_IndT.b
        Pre-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.b]]
        Action: foo
      Counterexample (TR):
        Theory:
          EnumA_Enum.nop = EnumNamesInCTIs.EnumA_IndT.nop
          EnumB_Enum.a = EnumNamesInCTIs.EnumB_IndT.a
          EnumB_Enum.b = EnumNamesInCTIs.EnumB_IndT.b
        Pre-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.b]]
        Action: foo
        Post-state:
          req = [[EnumNamesInCTIs.EnumA_IndT.nop, EnumNamesInCTIs.EnumB_IndT.a]]
-/
#guard_msgs in
#check_invariants

end EnumNamesInCTIs

veil module LargeEnumTest

-- Keep this test narrow: the 50-constructor distinctness axiom is the part
-- that used to expand aggressively before `distinctN`.

enum large_enum = {
  v00, v01, v02, v03, v04, v05, v06, v07, v08, v09,
  v10, v11, v12, v13, v14, v15, v16, v17, v18, v19,
  v20, v21, v22, v23, v24, v25, v26, v27, v28, v29,
  v30, v31, v32, v33, v34, v35, v36, v37, v38, v39,
  v40, v41, v42, v43, v44, v45, v46, v47, v48, v49
}

individual state : large_enum

#gen_state

after_init {
  state := v00
}

action set_last {
  state := v49
}

invariant [large_distinct] v00 ≠ v49

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  large_distinct ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  set_last
    doesNotThrow ... ✅
    large_distinct ... ✅
-/
#guard_msgs in
#check_invariants

end LargeEnumTest
