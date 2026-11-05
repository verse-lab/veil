module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! Relations of three and four arguments. The solver's models give their tables, whose tuples
the decoder reads, in every counterexample to induction (safe modules) and in the counterexample
that `certify` rebuilds (unsafe modules, whose labels carry three or four arguments). -/

veil module Ternary

type node
relation r : node → node → node → Bool
individual bad : Bool

#gen_state

after_init {
  r X Y Z := false
  bad := false
}

action add (a b c : node) {
  require a ≠ b
  r a b c := true
}

action trip (a c : node) {
  require r a a c
  bad := true
}

safety [never_bad] ¬ bad

#gen_spec

/--
invariant [ic3_0] ∀ (x0 : node) (x1 : node), ¬ r x1 x1 x0
-/
#guard_msgs(info, substring := true) in
#synthesize_invariants (expect := invariant) certify

end Ternary

veil module TernaryBug

type node
relation r : node → node → node → Bool
individual bad : Bool

#gen_state

after_init {
  r X Y Z := false
  bad := false
}

action add (a b c : node) {
  require a ≠ c
  r a b c := true
}

action trip (a c : node) {
  require r a a c
  bad := true
}

safety [never_bad] ¬ bad

#gen_spec

/--
r: (1,1,0)
-/
#guard_msgs(info, substring := true) in
#synthesize_invariants (expect := unsafe) certify

end TernaryBug

veil module Quaternary

type node
relation r : node → node → node → node → Bool
individual bad : Bool

#gen_state

after_init {
  r X Y Z U := false
  bad := false
}

action add (a b c d : node) {
  require c ≠ d
  r a b c d := true
}

action trip (a b c : node) {
  require r a b c c
  bad := true
}

safety [never_bad] ¬ bad

#gen_spec

/--
invariant [ic3_0] ∀ (x0 : node) (x1 : node), ¬ r x1 x1 x0 x0
-/
#guard_msgs(info, substring := true) in
#synthesize_invariants (expect := invariant) certify

end Quaternary

veil module QuaternaryBug

type node
relation r : node → node → node → node → Bool
individual bad : Bool

#gen_state

after_init {
  r X Y Z U := false
  bad := false
}

action add (a b c d : node) {
  require a ≠ d
  r a b c d := true
}

action trip (a b c : node) {
  require r a b c c
  bad := true
}

safety [never_bad] ¬ bad

#gen_spec

/--
r: (1,0,0,0)
-/
#guard_msgs(info, substring := true) in
#synthesize_invariants (expect := unsafe) certify

end QuaternaryBug
