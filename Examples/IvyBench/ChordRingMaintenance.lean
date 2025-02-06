import Veil
-- https://github.com/aman-goel/ivybench/blob/master/i4/ivy/chord_ring_maintenance.ivy


namespace ChordRing
open Classical

class RingTopology (t : Type) where
  -- relation
  btw (a b c : t) : Prop
  trans : ∀ (a b c : t), btw a b c ∧ btw a c d → btw a b d
  acyclic : ∀ (a b c : t), btw a b c → ¬ btw a c b
  total : ∀ (a b c : t), (a = b) ∨ (a = c) ∨ btw a b c ∨ btw a c b
  cyclic_perm : ∀ (a b c : t), (btw a b c ∧ a ≠ c)→ btw b c a

type node

instantiate ring : RingTopology node

relation a : node → Prop
relation s1 : node → node → Prop
relation in_s1 : node → Prop
relation s2 : node → node → Prop
relation in_s2 : node → Prop
relation p : node → node → Prop

immutable individual org : node
immutable individual other : node
relation reach : node → Prop
relation error : node → Prop

#gen_state

assumption other ≠ org

after_init {
  a X := X = org ∨ X = other;
  s1 X Y := (X = org ∧ Y = other) ∨ (X = other ∧ Y = org);
  in_s1 X := X = org ∨ X = other;
  s2 X Y := False;
  in_s2 X := False;
  p X Y := (X = org ∧ Y = other) ∨ (X = other ∧ Y = org);
  reach X := X = org;
  error X := False
}

action join (x : node) (y : node) = {
  require ¬ a x;
  require ∀ Y, a Y;
  require ¬ ring.btw x org y;
  a x := True;
  s1 x Y := y = Y;
  in_s1 x := True;
  s2 x Y := False;
  in_s2 x := False;
  p x Y := False
}

action stabilize (x : node) (y : node) (z : node) = {
  require a x;
  require s1 x y;
  require a y;
  require p y z;
  require ring.btw x z y;
  s1 x Z := Z = z;
  in_s1 x := True;
  s2 x Y := Y = y;
  in_s2 x := True
}

action notify (x : node) (y : node) (z : node) = {
  require a x;
  require s1 x y;
  require a y;
  require ∀ X, p y z ∨ ¬ p y X;
  require ring.btw z x y;
  p y X := X = x
}

action inherit (x : node) (y : node) (z : node) = {
  require a x;
  require s1 x y;
  require a y;
  require s1 y z;
  s2 x Z := Z = z;
  in_s2 x := True
}

action remove (x : node) (y : node) (z : node) = {
  require a x;
  require s1 x y;
  require ¬ a y;
  require s2 x z;
  s1 x Z := Z = z;
  in_s1 x := True;
  s2 x Y := False;
  in_s2 x := False
}

action fail (x : node) = {
  require a x;
  require x ≠ org;
  require ∀ Y, (s1 Y x → in_s2 Y);
  require ∀ Y Z, s1 Y x ∧ s2 Y Z → a Z;
  require ∀ X Y, s1 X Y ∧ s2 X x → (Y ≠ x ∧ a Y);
  a x := False;
  p x Y := False;
  s1 x Y := False;
  in_s1 x := False;
  s2 x Y := False;
  in_s2 x := False
}

action reach_org (x : node) (y : node) (z : node) = {
  require (s1 x y ∧ a y ∧ reach y) ∨ (s1 x y ∧ ¬ a y ∧ s2 x z ∧ a z ∧ reach z);
  reach x := True
}

action remove_org (x : node) (y : node) (z : node) = {
  require x ≠ org;
  require s1 x y;
  require ¬ a y ∨ ¬ reach y;
  require ∀ Z, (¬ a y) → (¬ s2 x Z ∨ s2 x z);
  require (¬ a y ∧ s2 x z) → (¬ a z ∨ ¬ reach z);
  reach x := False
}

action test (x : node) = {
  require ∀ X Y, (s1 X Y ∧ a Y ∧ reach Y) → reach X;
  require ∀ X Y Z, (s1 X Y ∧ ¬ a Y ∧ s2 X Z ∧ a Z ∧ reach Z) → reach X;
  require ∀ Y, (ring.btw x Y org ∧ a Y) → reach x;
  require a x;
  require ¬ reach x;
  require in_s1 x → ∃ y, s1 x y;
  require in_s2 x → ∃ y, s2 x y;
  error x := True
}

safety ¬ error N

#gen_spec

set_option sauto.smt.solver "cvc5" in
#check_invariants

end ChordRing
