import Mathlib.Data.Fin.Basic
import Mathlib.Data.FinEnum

/-! # Axiomatizations of various structures -/

instance Fin.pos_then_inhabited {n : Nat} (h : 0 < n) : Inhabited (Fin n) where
  default := Fin.mk 0 h

instance : FinEnum Bool := FinEnum.ofNodupList [true, false] (by decide) (by decide)

/-! ## Total order -/

/-- The type `t` is a total order with an `le` relation. -/
class TotalOrder (t : Type) where
  -- relation: total order
  le (x y : t) : Prop
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x

/-! ### Instances -/

/-- `Nat` is a total order. -/
instance total_order_nat : TotalOrder Nat where
  le := Nat.le
  le_refl := by simp
  le_trans := by simp ; omega
  le_antisymm := by simp ; omega
  le_total := by simp ; omega

/-- Finite types are total orders. -/
instance total_order_fin (n : Nat) : TotalOrder (Fin n) where
  le := fun x y => x.val ≤ y.val
  le_refl := by simp
  le_trans := by simp ; omega
  le_antisymm := by simp ; omega
  le_total := by simp ; omega

/-- Finite enumerations are total orders. -/
instance total_order_fin_enum (t : Type) [fe : FinEnum t] : TotalOrder t where
  le := fun x y => (total_order_fin fe.card).le (fe.equiv.toFun x) (fe.equiv.toFun y)
  le_refl := by simp [(total_order_fin fe.card).le_refl]
  le_trans := by
    simp only [Equiv.toFun_as_coe]
    intros x y z hxy hyz
    apply @TotalOrder.le_trans _ (total_order_fin fe.card) _ _ _ hxy hyz
  le_antisymm := by
    simp only [Equiv.toFun_as_coe]
    intros x y hxy hyx
    have heq := @TotalOrder.le_antisymm _ (total_order_fin fe.card) _ _ hxy hyx
    simp only [EmbeddingLike.apply_eq_iff_eq] at heq
    apply heq
  le_total := by simp [(total_order_fin fe.card).le_total]

/-! ### Decidability -/

/-- Total orders on `Nat` are decidable. -/
instance total_order_nat_dec : ∀ a b, Decidable (TotalOrder.le (t := Nat) a b) := by
  dsimp [TotalOrder.le]; apply inferInstance

/-- Total orders on `Fin n` are decidable. -/
instance total_order_fin_dec (n : Nat) : ∀ a b, Decidable (TotalOrder.le (t := Fin n) a b) := by
  dsimp [TotalOrder.le]; apply inferInstance

/-- Total orders on `FinEnum t` are decidable. -/
instance total_order_fin_enum_dec (t : Type) [fe : FinEnum t] : ∀ a b, Decidable (TotalOrder.le (t := t) a b) := by
  dsimp [TotalOrder.le]; apply inferInstance

/-! ## Total order with zero -/

class TotalOrderWithZero (t : Type) where
  -- relation: total order
  le (x y : t) : Prop
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x
  -- zero
  zero : t
  zero_le (x : t) : le zero x

/-! ### Instances -/

/-- Non-empty finite types are total orders with zero. -/
instance total_order_with_zero_fin (n : Nat) [nz : NeZero n] : TotalOrderWithZero (Fin n) where
  le := fun x y => x.val ≤ y.val
  le_refl := by simp
  le_trans := by simp ; omega
  le_antisymm := by simp ; omega
  le_total := by simp ; omega
  zero := ⟨0, by cases nz; grind⟩
  zero_le := by simp

/-! ### Decidability -/

instance total_order_with_zero_fin_dec (n : Nat) [nz : NeZero n] : ∀ a b, Decidable (TotalOrderWithZero.le (t := Fin n) a b) := by
  dsimp [TotalOrderWithZero.le]; apply inferInstance

/-! ## Total order with minimum -/

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

/-! ### Instances -/

/-! ## Ring topology -/

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

/-! ### Instances -/

/-- One can obtain a ring topology from a finite set of IDs by connecting the
list of IDs in order. -/
instance between_fin (n : Nat) : Between (Fin n) where
  btw a b c := (a.val < b.val ∧ b.val < c.val) ∨ (c.val < a.val ∧ a.val < b.val) ∨ (b.val < c.val ∧ c.val < a.val)
  btw_ring a b c := by aesop
  btw_trans w x y z := by omega
  btw_side w x y := by omega
  btw_total w x y := by omega

/-- A rank-based ring topology, where each node is assigned with a
unique `Nat` rank, nodes are sorted by their rank, and the ring is
formed by connecting the sorted list of nodes. -/
instance ordered_ring (node : Type) (rank : node → Nat) (rank_inj : ∀ n1 n2, n1 ≠ n2 → rank n1 ≠ rank n2) : Between node where
  btw := fun a b c => (rank a < rank b ∧ rank b < rank c) ∨ (rank c < rank a ∧ rank a < rank b) ∨ (rank b < rank c ∧ rank c < rank a)
  btw_ring := by aesop
  btw_trans := by omega
  btw_side := by omega
  btw_total := by
    intro a b c
    by_cases h1 : a = b ; subst_vars ; simp
    by_cases h2 : a = c ; subst_vars ; simp
    by_cases h3 : b = c ; subst_vars ; simp
    have hh1 := rank_inj _ _ h1 ; have hh2 := rank_inj _ _ h2 ; have hh3 := rank_inj _ _ h3
    omega

/-! ### Decidability -/

/-- Between on `Fin n` is decidable. -/
instance between_fin_dec (n : Nat) : ∀ a b c, Decidable (Between.btw (node := Fin n) a b c) := by
  dsimp [Between.btw]; apply inferInstance

/-! ## Byzantine node set -/

class ByzNodeSet (node : Type) /- (is_byz : outParam (node → Bool)) -/ (nset : outParam Type) where
  is_byz : node → Prop
  member (a : node) (s : nset) : Prop
  is_empty (s : nset) : Prop

  greater_than_third (s : nset) : Prop  -- f + 1 nodes
  supermajority (s : nset) : Prop       -- 2f + 1 nodes

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 : nset), supermajority s1 → supermajority s2 →
      ∃ (a : node), member a s1 ∧ member a s2 ∧ ¬ is_byz a
  greater_than_third_one_honest :
    ∀ (s : nset), greater_than_third s → ∃ (a : node), member a s ∧ ¬ is_byz a
  supermajority_greater_than_third :
    ∀ (s : nset), supermajority s → greater_than_third s
  greater_than_third_nonempty :
    ∀ (s : nset), greater_than_third s → ¬ is_empty s
