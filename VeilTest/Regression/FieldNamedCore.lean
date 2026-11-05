module

public import Veil

/-! Fields named `core`, the name of the first field of the classes `LocalRProp` and
`LocalTheoryProp` that `#gen_state` declares for every module: a state field, read through a
ghost relation, and a theory field, read by an assumption. -/

veil module StateFieldNamedCore

type node

relation core (n : node) : Bool
relation ok (n : node) : Bool

#gen_state

ghost relation marked (n : node) := core n

after_init {
  core N := false
  ok N := false
}

action mark (n : node) {
  core n := true
  ok n := true
}

invariant [marked_ok] marked N → ok N

#guard_msgs in
#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  marked_ok ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  mark
    doesNotThrow ... ✅
    marked_ok ... ✅
-/
#guard_msgs in
#check_invariants

end StateFieldNamedCore

veil module TheoryFieldNamedCore

type node

immutable relation core (n : node) : Bool
relation ok (n : node) : Bool

#gen_state

assumption [core_unique] core N1 ∧ core N2 → N1 = N2

after_init {
  ok N := false
}

action mark (n : node) {
  require core n
  ok n := true
}

invariant [ok_core] ok N → core N
invariant [ok_unique] ok N1 ∧ ok N2 → N1 = N2

#guard_msgs in
#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  ok_core ... ✅
  ok_unique ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  mark
    doesNotThrow ... ✅
    ok_core ... ✅
    ok_unique ... ✅
-/
#guard_msgs in
#check_invariants

end TheoryFieldNamedCore
