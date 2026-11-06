module

public import Veil

/-! Fields named `has` and `hinv`, the names of the binders the generated local obligations
put around a module's fields: state fields, and theory fields, which the transition-side
obligation also binds. -/

veil module FieldNamedHas

type node

relation has (n : node) : Bool
relation ok (n : node) : Bool

#gen_state

after_init {
  has N := false
  ok N := false
}

action get (n : node) {
  has n := true
  ok n := true
}

invariant [got_ok] has N → ok N

#guard_msgs in
#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  got_ok ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  get
    doesNotThrow ... ✅
    got_ok ... ✅
-/
#guard_msgs in
#check_invariants

end FieldNamedHas

veil module FieldNamedHinv

type node

relation hinv (n : node) : Bool
relation ok (n : node) : Bool

#gen_state

after_init {
  hinv N := false
  ok N := false
}

action get (n : node) {
  hinv n := true
  ok n := true
}

invariant [got_ok] hinv N → ok N

#guard_msgs in
#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  got_ok ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  get
    doesNotThrow ... ✅
    got_ok ... ✅
-/
#guard_msgs in
#check_invariants

end FieldNamedHinv

veil module TheoryFieldNamedHas

type node

immutable relation has (n : node) : Bool
relation ok (n : node) : Bool

#gen_state

after_init {
  ok N := false
}

action get (n : node) {
  require has n
  ok n := true
}

invariant [ok_has] ok N → has N

#guard_msgs in
#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  ok_has ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  get
    doesNotThrow ... ✅
    ok_has ... ✅
-/
#guard_msgs in
#check_invariants

end TheoryFieldNamedHas

veil module TheoryFieldNamedHinv

type node

immutable relation hinv (n : node) : Bool
relation ok (n : node) : Bool

#gen_state

after_init {
  ok N := false
}

action get (n : node) {
  require hinv n
  ok n := true
}

invariant [ok_hinv] ok N → hinv N

#guard_msgs in
#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  ok_hinv ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  get
    doesNotThrow ... ✅
    ok_hinv ... ✅
-/
#guard_msgs in
#check_invariants

end TheoryFieldNamedHinv
