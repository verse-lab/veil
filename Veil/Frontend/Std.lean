import Mathlib.Data.Fin.Basic
import Mathlib.Data.FinEnum
import Mathlib.Algebra.Ring.Parity
import Veil.Frontend.DSL.State.Types

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

/-- Form a total order from an injective mapping to `Nat`. This could be
used for enumerate types with `.ctorIdx`. -/
def total_order_by_inj_on_nat {t : Type} (f : t → Nat) (h : Function.Injective f)
  : TotalOrder t where
  le x y := (f x) ≤ (f y)
  le_refl _ := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans
  le_antisymm _ _ h1 h2 := Nat.le_antisymm h1 h2 |> h
  le_total x y := Nat.le_total (f x) (f y)

def total_order_by_inj_on_fin {t : Type} {n : Nat} (f : t → Fin n) (h : Function.Injective f)
  : TotalOrder t := total_order_by_inj_on_nat (fun x => (f x).val)
  (by whnf ; simp ; intro a1 a2 h ; aesop)

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

/-! ## Normal quorum -/

/-! ### Instances -/

-- NOTE: the original design is based on `Finset`, but the `Repr`
-- instance of `Finset` is marked as `unsafe`, so we use `List` instead
abbrev Quorum (n : Nat) : Type :=
  { fs : List (Fin n) // fs.Sorted (· < ·) ∧ (n / 2 + 1) ≤ fs.length }

theorem Quorum.quorum_intersection {n : Nat} (q1 q2 : Quorum n) :
  ∃ a, a ∈ q1.val ∧ a ∈ q2.val := by
  rcases q1 with ⟨q1, hq1, hq1'⟩ ; rcases q2 with ⟨q2, hq2, hq2'⟩ ; dsimp
  have htmp := Finset.card_inter (q1.toFinset) (q2.toFinset)
  have hnodup1 := List.Pairwise.nodup hq1 ; have hnodup2 := List.Pairwise.nodup hq2
  simp [List.toFinset_card_of_nodup hnodup1, List.toFinset_card_of_nodup hnodup2] at htmp
  have htmp2 := Finset.card_le_univ (q1.toFinset ∪ q2.toFinset) ; simp at htmp2
  have htmp3 : n / 2 + 1 + n / 2 + 1 - n ≤ (q1.toFinset ∩ q2.toFinset).card := by omega
  simp +arith only at htmp3
  rcases (Nat.even_or_odd' n) with ⟨k, (h | h)⟩ <;> subst n <;> simp at htmp3
  all_goals (have htmp4 : 1 ≤ (q1.toFinset ∩ q2.toFinset).card := by omega)
  all_goals (simp at htmp4 ; rcases htmp4 with ⟨a, ha⟩ ; simp at ha ; solve_by_elim)

instance (n : Nat) : Inhabited (Quorum n.succ) where
  default := ⟨List.ofFn id, by
    simp [StrictMono] ; constructor
    · rintro ⟨a, b⟩ ; simp [← Fin.val_fin_lt] ; omega
    · grind⟩

theorem Finset.List.ofFn_filter {n : Nat} (p : Finset (Fin n)) :
  letI l := List.ofFn (n := n) id |>.filter (fun i => i ∈ p)
  List.Sorted (· < ·) l ∧ l.length = p.card := by
  constructor
  · apply List.Pairwise.filter ; simp
  · induction p using Finset.induction_on with
    | empty => simp
    | insert a p hnotin ih =>
      simp [hnotin] ; have htmp : a ∈ List.ofFn (n := n) id := by simp
      rw [List.mem_iff_append] at htmp ; rcases htmp with ⟨l1, l2, htmp⟩ ; rw [htmp] at ih ⊢
      simp [List.filter] at ih ⊢ ; simp [decide_eq_false hnotin] at ih
      have htmp2 : List.Nodup (List.ofFn (n := n) id) := by apply List.Pairwise.nodup (r := (· < ·)) ; simp
      simp [htmp, List.nodup_middle, List.nodup_cons] at htmp2
      rw [← Nat.add_assoc, ← ih] ; congr! 3 <;> apply List.filter_congr <;> simp <;> aesop

def allQuorums (n : Nat) : List (Quorum n) :=
  let l := List.ofFn (n := n) id
  let res := FinEnum.Finset.enum l |>.filterMap (fun x =>
    if n / 2 + 1 ≤ x.card then .some (l.filter fun y => y ∈ x) else .none)
  res.attachWith _ (by
    intro x hmem ; unfold res l at hmem ; simp at hmem ; rcases hmem with ⟨fs, hcard, hmem⟩ ; subst x
    have ⟨h1, h2⟩ := Finset.List.ofFn_filter fs ; rw [h2] ; aesop)

theorem allQuorums_complete {n : Nat} : ∀ (q : Quorum n), q ∈ allQuorums n := by
  intro ⟨x, h1, h2⟩ ; dsimp [allQuorums] ; simp ; exists List.toFinset x
  have htmp := List.Pairwise.nodup h1 ; simp [List.toFinset_card_of_nodup htmp] ; refine And.intro h2 ?_
  apply List.Sorted.eq_of_mem_iff _ h1 ; simp ; apply List.Pairwise.filter ; simp

instance (n : Nat) : FinEnum (Quorum n) :=
  FinEnum.ofList (allQuorums n) allQuorums_complete

instance (n : Nat) : Veil.Enumeration (Quorum n) where
  allValues := allQuorums n
  complete := allQuorums_complete

/-! ### Decidability -/

/-- Membership test on `Quorum` is decidable. -/
instance quorum_mem_dec (n : Nat) : ∀ a (q : Quorum n), Decidable (a ∈ q.val) := by
  dsimp [Quorum] ; infer_instance

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
