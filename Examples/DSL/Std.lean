import Veil.DSL
/-! # Axiomatizations of various structures -/

class TotalOrder (t : Type) where
  -- relation: total order
  le (x y : t) : Prop
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x


class TotalOrderWithNone (t : Type) where
  -- relation: total order
  le (x y : t) : Prop
  none : t
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x


-- https://github.com/markyuen/tlaplus-to-ivy/blob/main/ivy/total_order.ivy
class TotalOrderWithMinimum (t : Type) where
  -- relation: strict total order
  le (x y : t) : Prop
  -- axioms
  le_refl (x : t) : le x x
  le_trans (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total (x y : t) : le x y ∨ le y x

  -- relation: nonstrict total order
  lt (x y : t) : Prop
  le_lt (x y : t) : lt x y ↔ (le x y ∧ x ≠ y)

  -- successor
  next (x y : t) : Prop
  next_def (x y : t) : next x y ↔ (lt x y ∧ ∀ z, lt x z → le y z)

  zero : t
  zero_lt (x : t) : le zero x

-- @[actSimp, invSimp] def TotalOrderWithMinimum.lt [tot : TotalOrderWithMinimum t] (x y : t) : Prop := (tot.le x y ∧ x ≠ y)
-- @[actSimp, invSimp] def TotalOrderWithMinimum.next [tot : TotalOrderWithMinimum t] (x y : t) : Prop := (tot.lt x y ∧ ∀ z, tot.lt x z → tot.le y z)

class TotalOrderWithZero (t : Type) where
  -- relation: total order
  le (x y : t) : Prop

  -- zero
  zero : t
  zero_le (x : t) : le zero x

  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x


class Queue (α : Type) (queue : outParam Type) where
  member (x : α) (q : queue) : Prop

  is_empty (q : queue) :=
    ∀ (e : α), ¬ member e q
  enqueue (x : α) (q q' : queue) :=
    ∀ (e : α), member e q' ↔ (member e q ∨ e = x)
  --  this is not a multi-set
  dequeue (x : α) (q q' : queue) :=
    ∀ (e : α), member e q' ↔ (member e q ∧ e ≠ x)

/-- Ring topology -/
class Between (node : Type) where
  -- relation: btw represents a ring
  -- read: y is between x and z
  btw (x y z : node) : Prop
  -- axioms
  btw_ring    (x y z : node) : btw x y z → btw y z x
  btw_trans (w x y z : node) : btw w x y → btw w y z → btw w x z
  btw_side    (w x y : node) : btw w x y → ¬ btw w y x
  btw_total   (w x y : node) : btw w x y ∨ btw w y x ∨ w = x ∨ w = y ∨ x = y


/-- Quorum with quorum intersection -/
class Quorum (node : Type) (quorum : outParam Type) where
  -- relation
  member (a : node) (q : quorum) : Prop
  -- axioms
  quorum_intersection :
    ∀ (q1 q2 : quorum), ∃ (a : node), member a q1 ∧ member a q2


class ByzQuorum (node : Type) (is_byz : outParam (node → Prop)) (nset : outParam Type) where
  member (a : node) (s : nset) : Prop
  supermajority (s : nset) : Prop       -- 2f + 1 nodes

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 : nset), ∃ (a : node), member a s1 ∧ member a s2 ∧ ¬ is_byz a


/-- Sets of nodes with `f + 1` and `2f + 1` thresholds. Parametrized by
an `is_byz` oracle. -/
class NodeSet (node : Type) (is_byz : outParam (node → Prop)) (nset : outParam Type) where
  member (a : node) (s : nset) : Prop
  is_empty (s : nset) : Prop

  greater_than_third (s : nset) : Prop  -- f + 1 nodes
  supermajority (s : nset) : Prop       -- 2f + 1 nodes

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 : nset), ∃ (a : node), member a s1 ∧ member a s2 ∧ ¬ is_byz a
  greater_than_third_one_honest :
    ∀ (s : nset), greater_than_third s → ∃ (a : node), member a s ∧ ¬ is_byz a
  supermajority_greater_than_third :
    ∀ (s : nset), supermajority s → greater_than_third s
  greater_than_third_nonempty :
    ∀ (s : nset), greater_than_third s → ¬ is_empty s
