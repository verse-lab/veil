module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! Immutable components and typeclass symbols of three arguments. The decoder reads the theory's
relations from `theory` and the class symbols from `extraVals`, in every counterexample to
induction. -/

veil module ImmTernary

type node
immutable relation link : node → node → node → Bool
relation seen : node → node → Bool
individual bad : Bool

#gen_state

assumption [link_ends] ∀ x y, ¬ link x y x

after_init {
  seen X Y := false
  bad := false
}

action visit (a b c : node) {
  require link a b c
  seen a c := true
}

action trip (a : node) {
  require seen a a
  bad := true
}

safety [never_bad] ¬ bad

#gen_spec

/--
Certified: theorem ImmTernary.ic3_safe (strengthening ImmTernary.ic3_inv)
-/
#guard_msgs(info, substring := true) in
#updr (expect := invariant) certify

end ImmTernary

veil module ImmTernaryBug

type node
immutable relation link : node → node → node → Bool
relation seen : node → node → Bool
individual bad : Bool

#gen_state

after_init {
  seen X Y := false
  bad := false
}

action visit (a b c : node) {
  require link a b c ∧ a ≠ b
  seen a c := true
}

action trip (a : node) {
  require seen a a
  bad := true
}

safety [never_bad] ¬ bad

#gen_spec

/--
link: (0,0,0) (0,0,1) (0,1,0) (0,1,1) (1,0,0) (1,0,1) (1,1,0) (1,1,1)
-/
#guard_msgs(info, substring := true) in
#updr (expect := unsafe) certify

end ImmTernaryBug

veil module Btw

type node
instantiate btwn : Between node
open Between

relation mark : node → node → Bool
individual bad : Bool

#gen_state

after_init {
  mark X Y := false
  bad := false
}

action note (a b c : node) {
  require btw a b c
  mark a c := true
}

action trip (a : node) {
  require mark a a
  bad := true
}

safety [never_bad] ¬ bad

#gen_spec

/--
Certified: theorem Btw.ic3_safe (strengthening Btw.ic3_inv)
-/
#guard_msgs(info, substring := true) in
#updr (expect := invariant) certify

end Btw

veil module BtwBug

type node
instantiate btwn : Between node
open Between

relation mark : node → node → Bool
individual bad : Bool

#gen_state

after_init {
  mark X Y := false
  bad := false
}

action note (a b c : node) {
  require btw a b c
  mark a b := true
}

action trip (a b c : node) {
  require mark a b ∧ btw b c a
  bad := true
}

safety [never_bad] ¬ bad

#gen_spec

-- TODO: `certify` fails here: none of `decide`, `simp_all` and `grind` proves the `Between`
-- axioms of the instance built from the counterexample's `btw` table.
/--
btwn.btw: (0,2,1) (1,0,2) (2,1,0)
-/
#guard_msgs(info, substring := true) in
#updr (expect := unsafe)

end BtwBug
