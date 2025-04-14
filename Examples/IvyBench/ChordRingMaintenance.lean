import Veil
-- https://github.com/aman-goel/ivybench/blob/master/i4/ivy/chord_ring_maintenance.ivy


veil module ChordRing

class RingTopology (t : Type) where
  -- Y is on the acyclic path from X to Z
  btw : t → t → t → Prop

  -- Axioms defining the btw relation
  -- Note: anti-reflexivity not needed: btw X Y Z → X ≠ Y ∧ X ≠ Z ∧ Y ≠ Z
  trans : ∀ w x y z, btw w x y → btw w y z → btw w x z
  acyclic : ∀ w x y, btw w x y → ¬ btw w y x
  total : ∀ w x y, btw w x y ∨ btw w y x ∨ w = x ∨ x = y
  cyclic_perm : ∀ x y z, btw x y z ∧ x ≠ z → btw y z x

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

safety [no_error] ¬ error N

invariant [manual_1] s1 X Y → in_s1 X
invariant [manual_2] s2 X Y → in_s2 X
invariant [manual_3] reach org
invariant [manual_4] s1 X Y ∧ s1 X Z → Y = Z
invariant [manual_5] s2 X Y ∧ s2 X Z → Y = Z
invariant [manual_6] p X Y ∧ p X Z → Y = Z
invariant [manual_7] a X ∨ X ≠ org
invariant [manual_8] a X ∨ ¬ p Y X ∨ ¬ s1 X Y
invariant [manual_9] a X ∨ p Y X ∨ ¬ s1 X Y
invariant [manual_10] a X ∨ ¬ s2 X Y
invariant [manual_11] in_s1 X ∨ ¬ a X
invariant [manual_12] a Y ∨ a Z ∨ ¬ s1 X Y ∨ ¬ s2 X Z
invariant [manual_13] a Y ∨ in_s2 X ∨ ¬ a X ∨ ¬ s1 X Y
invariant [manual_14] p A B → a A
invariant [manual_15] a X ∧ p Y X ∧ s1 X Y → a Y
invariant [manual_16] ¬ ring.btw X org Y ∨ ¬ s1 X Y
invariant [manual_17] ¬ (s1 V0 V1 ∧ V1 ≠ org ∧ s2 V0 V2 ∧ ring.btw V0 org V2)

#gen_spec

#time #check_invariants

end ChordRing
