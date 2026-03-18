import Std
import Mathlib.Data.Fin.Basic
import Mathlib.Data.FinEnum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.List.Sublists
import Veil.Frontend.DSL.State.Types
import Veil.Frontend.DSL.State.Instances
import Std.Data.ExtTreeSet.Lemmas
import Veil.Util.SortedList
import Veil.Util.SortedArray

open Std

def List.insertOrdered [inst : Ord α] := @List.orderedInsert _ (fun x y => inst.compare x y == Ordering.lt) inferInstance

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

instance (n : Nat): TotalOrderWithMinimum (Fin n.succ) where
  le := fun x y => x.val ≤ y.val
  le_refl := by simp
  le_trans := by simp ; omega
  le_antisymm := by simp ; omega
  le_total := by simp ; omega
  lt := fun x y => x.val < y.val
  le_lt := by intros; dsimp [TotalOrderWithMinimum.lt, TotalOrderWithMinimum.le]; omega
  next := fun x y => x.val + 1 = y.val
  next_def := by
    intros x y
    dsimp [TotalOrderWithMinimum.next, TotalOrderWithMinimum.lt, TotalOrderWithMinimum.le]
    apply Iff.intro
    · intros; constructor <;> omega
    · intro ⟨hlt, hmin⟩
      have h1 : x.val < x.val + 1 := by omega
      have h2 : y.val ≤ x.val + 1 := hmin ⟨x.val + 1, by omega⟩ h1
      omega
  zero := ⟨0, by simp⟩
  zero_lt := by simp ;

instance total_order_with_minimum_fin_dec (n : Nat) : ∀ a b, Decidable (TotalOrderWithMinimum.le (t := Fin n.succ) a b) := by
  dsimp [TotalOrderWithMinimum.le]; apply inferInstance

instance total_order_with_minimum_fin_lt_dec (n : Nat) : ∀ a b, Decidable (TotalOrderWithMinimum.lt (t := Fin n.succ) a b) := by
  dsimp [TotalOrderWithMinimum.lt]; apply inferInstance

instance total_order_with_minimum_fin_next_dec (n : Nat) : ∀ a b, Decidable (TotalOrderWithMinimum.next (t := Fin n.succ) a b) := by
  dsimp [TotalOrderWithMinimum.next]; apply inferInstance

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

/-- Convert a BitVec to the list of indices where bits are set -/
@[inline] def BitVec.toFinList (bv : BitVec n) : List (Fin n) :=
  List.finRange n |>.filter (bv[·])

/-- Count the number of set bits in a BitVec -/
@[inline] def BitVec.popCount (bv : BitVec n) : Nat := bv.toFinList.length

/-- Helper: convert a BitVec to a Finset of indices where bits are set -/
def BitVec.toFinset (bv : BitVec n) : Finset (Fin n) := bv.toFinList.toFinset

theorem BitVec.toFinset_card (bv : BitVec n) :
    bv.toFinset.card = bv.popCount := by
  simp only [toFinset, popCount]
  rw [List.toFinset_card_of_nodup]
  apply List.Nodup.filter
  exact List.nodup_finRange n

theorem BitVec.mem_toFinset (bv : BitVec n) (i : Fin n) : i ∈ bv.toFinset ↔ bv[i] = true := by simp [toFinset, toFinList]

/-- Enumerate all BitVecs of size n -/
def BitVec.allBitVecs (n : Nat) : List (BitVec n) :=
  List.finRange (2 ^ n) |>.map (BitVec.ofFin)

theorem BitVec.allBitVecs_complete {n : Nat} : ∀ (bv : BitVec n), bv ∈ BitVec.allBitVecs n := by
  intro bv
  simp only [BitVec.allBitVecs, List.mem_map, List.mem_finRange, true_and]
  exact ⟨bv.toFin, BitVec.ofFin_toFin bv⟩

-- NOTE: the original design is based on `Finset`, but the `Repr`
-- instance of `Finset` is marked as `unsafe`, so we use `BitVec` instead,
-- which saves space and also has `O(1)` membership test.
abbrev Quorum (n : Nat) : Type :=
  { fs : BitVec n // (n / 2 + 1) ≤ fs.popCount }

instance : Membership (Fin n) (Quorum n) where
  mem q a := q.val[a] = true

theorem Quorum.quorum_intersection {n : Nat} (q1 q2 : Quorum n) :
  ∃ a, a ∈ q1 ∧ a ∈ q2 := by
  rcases q1 with ⟨bv1, hq1⟩ ; rcases q2 with ⟨bv2, hq2⟩
  simp only [Membership.mem]
  -- Convert to Finset reasoning
  have hcard1 : n / 2 + 1 ≤ bv1.toFinset.card := by
    rw [BitVec.toFinset_card] ; exact hq1
  have hcard2 : n / 2 + 1 ≤ bv2.toFinset.card := by
    rw [BitVec.toFinset_card] ; exact hq2
  -- Use Finset intersection argument
  have hunion := Finset.card_le_univ (bv1.toFinset ∪ bv2.toFinset)
  have hinter := Finset.card_union_add_card_inter bv1.toFinset bv2.toFinset
  have hinter_size : 1 ≤ (bv1.toFinset ∩ bv2.toFinset).card := by
    have : (bv1.toFinset ∪ bv2.toFinset).card ≤ n := by
      calc (bv1.toFinset ∪ bv2.toFinset).card
        ≤ Finset.univ.card := Finset.card_le_univ _
        _ = n := Finset.card_fin n
    rcases (Nat.even_or_odd' n) with ⟨k, (h | h)⟩ <;> subst h <;> omega
  simp only [Finset.one_le_card] at hinter_size
  rcases hinter_size with ⟨a, ha⟩
  simp only [Finset.mem_inter, BitVec.mem_toFinset] at ha
  exact ⟨a, ha.1, ha.2⟩

instance (n : Nat) : Inhabited (Quorum n.succ) where
  default := ⟨BitVec.allOnes (n + 1), by
    have h : ∀ i : Fin (n + 1), (BitVec.allOnes (n + 1))[i] = true := by
      intro i ; simp [BitVec.allOnes, BitVec.getElem_eq_testBit_toNat]
    have hfilter : (List.filter (fun x => (BitVec.allOnes (n + 1))[x]) (List.finRange (n + 1))) =
                   List.finRange (n + 1) := by
      apply List.filter_eq_self.mpr
      intro i _
      exact h i
    simp only [Nat.succ_eq_add_one, BitVec.popCount, BitVec.toFinList, hfilter, List.length_finRange]
    omega⟩

def allQuorums (n : Nat) : List (Quorum n) :=
  let res := BitVec.allBitVecs n |>.filter (fun bv => n / 2 + 1 ≤ bv.popCount)
  res.attachWith _ (by
    intro bv hmem
    have h := (List.mem_filter.mp hmem).2
    simp only [BitVec.popCount, decide_eq_true_eq] at h
    exact h)

theorem allQuorums_complete {n : Nat} : ∀ (q : Quorum n), q ∈ allQuorums n := by
  intro ⟨bv, hbv⟩
  simp only [allQuorums, List.mem_attachWith, List.mem_filter, BitVec.popCount]
  exact ⟨BitVec.allBitVecs_complete bv, decide_eq_true hbv⟩

instance (n : Nat) : FinEnum (Quorum n) :=
  FinEnum.ofList (allQuorums n) allQuorums_complete

instance (n : Nat) : Veil.Enumeration (Quorum n) where
  allValues := allQuorums n
  complete := allQuorums_complete

instance (n : Nat) : Std.ReflOrd (Quorum n) where
  compare_self := by
    have tmp : Std.ReflOrd (BitVec n) := by infer_instance
    intros ; dsimp [compare] ; apply tmp.compare_self

instance (n : Nat) : Std.LawfulEqOrd (Quorum n) where
  eq_of_compare := by
    have tmp : Std.LawfulEqOrd (BitVec n) := by infer_instance
    intros ; dsimp [compare] at * ; ext1 ; apply tmp.eq_of_compare ; assumption

instance (n : Nat) : Std.OrientedOrd (Quorum n) where
  eq_swap := by
    have tmp : Std.OrientedOrd (BitVec n) := by infer_instance
    intros ; dsimp [compare] at * ; apply tmp.eq_swap

instance (n : Nat) : Std.TransOrd (Quorum n) where
  isLE_trans := by
    have tmp : Std.TransOrd (BitVec n) := by infer_instance
    intros ; dsimp [compare] at * ; apply tmp.isLE_trans <;> assumption

/-! ### Decidability -/

/-- Membership test on `Quorum` is decidable. -/
instance quorum_mem_dec (n : Nat) : ∀ a (q : Quorum n), Decidable (a ∈ q) :=
  fun a q => inferInstanceAs (Decidable (q.val[a] = true))

/-! ### Repr -/

/-- Display a Quorum as a set of numbers (the indices where bits are set) -/
instance (n : Nat) : Repr (Quorum n) where
  reprPrec q _ :=
    let indices := q.val.toFinList
    "{" ++ String.intercalate ", " (indices.map toString) ++ "}"

-- NOTE: It seems that because of `abbrev`, without this explicit instance,
-- Lean will get stuck when trying to find `Lean.ToJson (Quorum n)`.
instance (n : Nat) : Lean.ToJson (Quorum n) := Veil.jsonOfRepr

/-! ## Byzantine node set -/

class ByzNodeSet (node : Type) /- (is_byz : outParam (node → Bool)) -/ (nset : outParam Type) where
  is_byz : node → Bool
  member (a : node) (s : nset) : Bool
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

/-! ### Instances -/

theorem Finset.List.ofFn_filter {n : Nat} (p : Finset (Fin n)) :
  letI l := List.ofFn (n := n) id |>.filter (fun i => i ∈ p)
  List.Pairwise (· < ·) l ∧ l.length = p.card := by
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

/-- A sorted list of nodes, representing a set in Byzantine fault tolerance. -/
abbrev ByzNSet (n : Nat) : Type :=
  { fs : List (Fin n) // fs.Pairwise (· < ·) }

/-- All possible ByzNSets (all sorted sublists of [0..n-1]). -/
def allByzNSets (n : Nat) : List (ByzNSet n) :=
  let l := List.ofFn (n := n) id
  let res := FinEnum.Finset.enum l |>.map (fun x => l.filter fun y => y ∈ x)
  res.attachWith _ (by
    intro x hmem ; unfold res l at hmem ; simp at hmem ; rcases hmem with ⟨fs, hmem⟩ ; subst x
    exact (Finset.List.ofFn_filter fs).1)

theorem allByzNSets_complete {n : Nat} : ∀ (s : ByzNSet n), s ∈ allByzNSets n := by
  intro ⟨x, hx⟩ ; dsimp [allByzNSets] ; simp ; exists x.toFinset
  have hnodup := List.Pairwise.nodup hx
  apply List.Pairwise.eq_of_mem_iff _ hx ; simp ; apply List.Pairwise.filter ; simp

instance (n : Nat) : FinEnum (ByzNSet n) :=
  FinEnum.ofList (allByzNSets n) allByzNSets_complete

instance (n : Nat) : Veil.Enumeration (ByzNSet n) where
  allValues := allByzNSets n
  complete := allByzNSets_complete

instance (n : Nat) : Inhabited (ByzNSet n) where
  default := ⟨[], List.Pairwise.nil⟩

instance (n : Nat) : @Std.ReflCmp (ByzNSet n) compare where
  compare_self := List.instReflCmpCompareLex.compare_self

instance (n : Nat) : @Std.LawfulEqCmp (ByzNSet n) compare where
  eq_of_compare h := Subtype.ext <| List.instLawfulEqCmpCompareLex.eq_of_compare h

instance (n : Nat) : @Std.OrientedCmp (ByzNSet n) compare where
  eq_swap := List.instOrientedCmpCompareLex.eq_swap

instance (n : Nat) : @Std.TransCmp (ByzNSet n) compare where
  isLE_trans := List.instTransCmpCompareLex.isLE_trans

section

variable (n f : Nat) (hf : n = 3 * f + 1)
  (is_byz : Fin n → Prop) [DecidablePred is_byz]
  (hbyz : (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length ≤ f)

include hbyz

/-- ByzNodeSet instance for `Fin n` with at most `f` Byzantine nodes.
    Assumes `n = 3 * f + 1` (standard Byzantine fault tolerance assumption). -/
def byzNodeSetFin : ByzNodeSet (Fin n) (ByzNSet n) where
  is_byz := is_byz
  member a s := a ∈ s.val
  is_empty s := s.val = []
  supermajority s := 2 * f + 1 ≤ s.val.length
  greater_than_third s := f + 1 ≤ s.val.length
  supermajorities_intersect_in_honest := by
    intro ⟨s1, hs1_sorted⟩ ⟨s2, hs2_sorted⟩ hsup1 hsup2
    simp only at hsup1 hsup2
    -- Two supermajorities of size ≥ 2f+1 in universe of size n = 3f+1
    -- intersect in ≥ 2(2f+1) - (3f+1) = f+1 elements
    -- Since ≤ f are Byzantine, ≥ 1 honest in intersection
    have hnodup1 := List.Pairwise.nodup hs1_sorted
    have hnodup2 := List.Pairwise.nodup hs2_sorted
    have hcard1 : s1.toFinset.card = s1.length := List.toFinset_card_of_nodup hnodup1
    have hcard2 : s2.toFinset.card = s2.length := List.toFinset_card_of_nodup hnodup2
    have hinter := Finset.card_inter (s1.toFinset) (s2.toFinset)
    have hunion := Finset.card_le_univ (s1.toFinset ∪ s2.toFinset) ; simp at hunion
    have hinter_size : f + 1 ≤ (s1.toFinset ∩ s2.toFinset).card := by omega
    -- The intersection contains at least f+1 nodes, and at most f are Byzantine
    by_contra h ; push_neg at h
    have hall_byz : ∀ a ∈ s1.toFinset ∩ s2.toFinset, is_byz a := by
      intro a ha ; simp at h ha
      have := h a ha.1 ha.2 ; tauto
    have hbyz_count : (s1.toFinset ∩ s2.toFinset).card ≤ f := by
      calc (s1.toFinset ∩ s2.toFinset).card
          ≤ ((List.ofFn (n := n) id).filter (fun i => decide (is_byz i))).toFinset.card := by
            apply Finset.card_le_card
            intro a ha ; simp at ha ⊢ ; exact hall_byz a (by simp [ha])
          _ ≤ (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length := by
            apply List.toFinset_card_le
          _ ≤ f := hbyz
    omega
  greater_than_third_one_honest := by
    intro ⟨s, hs_sorted⟩ hgt
    simp only at hgt
    -- s has ≥ f+1 elements, ≤ f are Byzantine, so ≥ 1 honest
    by_contra h ; push_neg at h
    have hall_byz : ∀ a ∈ s, is_byz a := by
      intro a ha ; simp at h ; have := h a ha ; tauto
    have hnodup := List.Pairwise.nodup hs_sorted
    have hbyz_count : s.length ≤ f := by
      calc s.length
          = s.toFinset.card := by simp [List.toFinset_card_of_nodup hnodup]
          _ ≤ ((List.ofFn (n := n) id).filter (fun i => decide (is_byz i))).toFinset.card := by
            apply Finset.card_le_card
            intro a ha ; simp at ha ⊢ ; exact hall_byz a ha
          _ ≤ (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length := by
            apply List.toFinset_card_le
          _ ≤ f := hbyz
    omega
  supermajority_greater_than_third := by
    intro _ hs ; omega
  greater_than_third_nonempty := by
    intro s hs heq ; simp_all

-- These instances are required, even after setting `byzNodeSetFin` to be `abbrev`
instance byzNodeSetFin_is_byz_dec :
  ∀ a, Decidable (ByzNodeSet.is_byz (self := byzNodeSetFin n f hf is_byz hbyz) a) := by
  dsimp [byzNodeSetFin] ; intros ; infer_instance

instance byzNodeSetFin_member_dec :
  ∀ a b, Decidable (ByzNodeSet.member (self := byzNodeSetFin n f hf is_byz hbyz) a b) := by
  dsimp [byzNodeSetFin] ; intros ; infer_instance

instance byzNodeSetFin_supermajority_dec :
  ∀ a, Decidable (ByzNodeSet.supermajority _ (self := byzNodeSetFin n f hf is_byz hbyz) a) := by
  dsimp [byzNodeSetFin] ; intros ; infer_instance

instance byzNodeSetFin_greater_than_third_dec :
  ∀ a, Decidable (ByzNodeSet.greater_than_third _ (self := byzNodeSetFin n f hf is_byz hbyz) a) := by
  dsimp [byzNodeSetFin] ; intros ; infer_instance

end

/-- A simple case of ByzNodeSet for `Fin (3 * f + 1)` with exactly `f`
Byzantine nodes, whose indices are in `[0, f)`. Note that when using
this instance, `f` must be given explicitly (e.g., write
`#synth ByzNodeSet (Fin (3 * 1 + 1)) (ByzNSet (3 * 1 + 1))` instead of
`#synth ByzNodeSet (Fin 4) (ByzNSet 4)`. -/
instance insByzNodeSetFinSimple : ByzNodeSet (Fin (3 * f + 1)) (ByzNSet (3 * f + 1)) :=
  byzNodeSetFin (3 * f + 1) f rfl (fun i => i.val < f) (by
    dsimp ; apply Nat.le_of_eq
    rw [← List.take_append_drop f (List.ofFn id), List.filter_append, List.length_append]
    conv => rhs ; rw [← Nat.add_zero f]
    congr
    · trans ; rw [List.length_filter_eq_length_iff]
      · simp only [List.mem_iff_getElem?, List.getElem?_take, List.getElem?_ofFn]
        simp
        rintro ⟨a, ha⟩ ; simp ; intros ; omega
      · simp ; omega
    · simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff, decide_eq_true_eq, _root_.not_lt]
      simp only [List.mem_iff_getElem?, List.getElem?_drop, List.getElem?_ofFn]
      simp
      rintro ⟨a, ha⟩ ; simp ; intros ; omega
    )

/-! ## Set -/

class TSet (α : outParam (Type u)) (κ : Type v) where
  count : κ → Nat
  contains : α → κ → Bool
  empty : κ
  isEmpty : κ → Bool
  insert : α → κ → κ
  remove : α → κ → κ
  ofList : List α → κ
  toList : κ → List α
  filter : κ → (α → Bool) → κ
  union : κ → κ → κ
  diff : κ → κ → κ
  intersection : κ → κ → κ
  subsets : κ → List κ

  empty_count : count empty = 0
  empty_contains (elem : α) : contains elem empty = false
  isEmpty_iff_count_zero (s : κ) : isEmpty s = true ↔ count s = 0
  contains_insert_self (elem : α) (s : κ) :
    contains elem (insert elem s) = true
  contains_insert_other (elem₁ elem₂ : α) (s : κ) (h : elem₁ ≠ elem₂) :
    contains elem₁ (insert elem₂ s) = contains elem₁ s
  insert_idempotent (elem : α) (s : κ) :
    toList (insert elem (insert elem s)) = toList (insert elem s)
  count_insert (elem : α) (s : κ) :
    count (insert elem s) =
      if contains elem s then count s else count s + 1
  contains_remove_self (elem : α) (s : κ) :
    contains elem (remove elem s) = false
  contains_remove_other (elem₁ elem₂ : α) (s : κ) (h : elem₁ ≠ elem₂) :
    contains elem₁ (remove elem₂ s) = contains elem₁ s
  count_remove (elem : α) (s : κ) :
    count (remove elem s) = if contains elem s then count s - 1 else count s
  contains_union (elem : α) (s1 s2 : κ) :
    contains elem (union s1 s2) = (contains elem s1 || contains elem s2)
  contains_diff (elem : α) (s1 s2 : κ) :
    contains elem (diff s1 s2) = (contains elem s1 && not (contains elem s2))
  toList_contains_iff (elem : α) (s : κ) :
    contains elem s = true ↔ elem ∈ toList s
  subsets_iff (s1 s2 : κ) :
    s1 ∈ subsets s2 ↔ (∀ elem, contains elem s1 = true → contains elem s2 = true)

@[inline]
instance [TSet α κ] : Membership α κ where
  mem s a := TSet.contains a s = true

@[inline]
instance [TSet α κ] (a : α) (k : κ) : Decidable (a ∈ k) := instDecidableEqBool _ _

instance instEnumerationTSetContains [TSet α κ] (k : κ) : Veil.Enumeration ({ a : α // TSet.contains a k }) where
  allValues := TSet.toList k |>.attachWith _ (fun x => TSet.toList_contains_iff _ _ |>.mpr)
  complete := by simp [TSet.toList_contains_iff]

def TSet.isSubset [TSet α κ] (s1 s2 : κ) : Prop :=
  ∀ elem, TSet.contains elem s1 = true → TSet.contains elem s2 = true

instance [TSet α κ] (s1 s2 : κ) : Decidable (TSet.isSubset s1 s2) :=
  if h : (TSet.toList s1).all (fun elem => TSet.contains elem s2 = true) then
    isTrue (fun elem hmem => by simp [← TSet.toList_contains_iff] at h ; exact h _ hmem)
  else
    isFalse (by simp [← TSet.toList_contains_iff] at h ; simp [TSet.isSubset] ; exact h)

instance (priority := high) instEnumerationTSetSubset [TSet α κ] (superSet : κ) : Veil.Enumeration ({ s : κ // TSet.isSubset s superSet }) where
  allValues := TSet.subsets superSet |>.attachWith _ (fun x => TSet.subsets_iff x superSet |>.mp)
  complete := by simp [TSet.isSubset, TSet.subsets_iff]

instance [TSet α κ] (k : κ) : Veil.Enumeration ({ a : α // a ∈ k }) := instEnumerationTSetContains k

-- NOTE: This doesn't look very straightforward since it is defined between two `TSet` instances ...
-- Is there any way to improve?
def TSet.map [origin_set : TSet α κ] [target_set : TSet β l] (s1 : κ) (f : α → β) : l :=
  target_set.ofList <| (origin_set.toList s1 |>.map f)

def TSet.filterMap [origin_set : TSet α κ] [target_set : TSet β l] (s1 : κ) (f : α → Option β) : l :=
  target_set.ofList <| (origin_set.toList s1 |>.filterMap f)

theorem extTreeSet_contains_filter_not [Ord α] [TransOrd α] [LawfulEqOrd α]
    {s1 s2 : ExtTreeSet α compare} {elem : α} :
    (s1.filter (!s2.contains ·)).contains elem = (s1.contains elem && !s2.contains elem) := by
  cases h1 : s1.contains elem <;> cases h2 : s2.contains elem <;> simp [h2]
  all_goals
    by_contra
    have : elem ∈ s1.filter (!s2.contains ·) := by rw [← Std.ExtTreeSet.contains_iff_mem]; grind
    try rw [mem_filter] at this
    simp [h2] at this
    try grind

@[grind =]
theorem list_foldl_insert [Ord α] [TransOrd α] [LawfulEqOrd α] [DecidableEq α]
  (l : List α) (s : ExtTreeSet α compare) (elem : α) :
  (l.foldl (fun acc a => acc.insert a) s).contains elem = (s.contains elem || l.contains elem) := by
  induction l generalizing s with
  | nil => grind
  | cons head tail ih =>
    rw [List.foldl_cons, ih]
    simp only [List.contains_cons]
    by_cases h : head = elem
    · rw [h]
      have : (s.insert elem).contains elem = true := by grind
      simp [this]
    · have h1 : (s.insert head).contains elem = s.contains elem := by grind
      have h2 : (elem == head) = false := by grind
      simp [h1, h2, Bool.false_or]


theorem extTreeSet_fold_insert
  [Ord α] [TransOrd α] [LawfulEqOrd α] [DecidableEq α]
  (elem : α) (s1 s2 : ExtTreeSet α compare) :
  (ExtTreeSet.foldl (fun acc a => acc.insert a) s2 s1).contains elem = (s1.contains elem || s2.contains elem) := by
  rw [ExtTreeSet.foldl_eq_foldl_toList]
  grind


-- https://github.com/leanprover-community/mathlib4/blob/v4.19.0/Mathlib/Tactic/Linarith/Oracle/FourierMotzkin.lean#L41
instance [Ord α] [TransOrd α] [LawfulEqOrd α] [DecidableEq α]
  : TSet α (ExtTreeSet α) where
  count := ExtTreeSet.size
  contains := fun a s => s.contains a
  empty := ExtTreeSet.empty
  isEmpty := fun s => s.isEmpty
  insert := fun a s => s.insert a
  remove := fun a s => s.erase a
  ofList := fun l => Std.ExtTreeSet.ofList l
  toList := fun s => s.toList
  filter := fun s p => s.filter p
  union := fun s1 s2 => s1.foldl .insert s2
  diff := fun s1 s2 => s1.filter (!s2.contains ·)
  intersection := fun s1 s2 => s1.filter (s2.contains ·)
  subsets := fun s => s.toList.sublists.map (Std.ExtTreeSet.ofList · compare)
  empty_count := by grind
  empty_contains := by grind
  isEmpty_iff_count_zero := by intro s ; rw [Std.ExtTreeSet.isEmpty_eq_size_beq_zero] ; grind
  contains_insert_self := by intros; grind
  contains_insert_other := by intro elem₁ elem₂ s h; grind
  count_insert := by grind
  contains_remove_self := by grind
  contains_remove_other := by intro elem₁ elem₂ s h; grind
  count_remove := by grind
  insert_idempotent := by
    intros elem s;
    congr 1
    apply ExtTreeSet.ext_mem
    grind
  contains_union := by
    intros elem s1 s2
    exact extTreeSet_fold_insert elem s1 s2
  contains_diff := by
    intros elem s1 s2
    exact extTreeSet_contains_filter_not
  toList_contains_iff := by
    intros elem s
    simp [Std.ExtTreeSet.contains_iff_mem]
  subsets_iff := by
    intros s1 s2
    simp [Std.ExtTreeSet.contains_iff_mem, Std.ExtTreeSet.ext_mem_iff]
    simp only [← Std.ExtTreeSet.mem_toList (t := s2)]
    constructor
    · grind
    · intro h ; exists s2.toList.filter (fun a => s1.contains a) ; simp at h ⊢ ; grind

open OrdList in
instance [Ord α] [TransOrd α] [LawfulEqOrd α] [DecidableEq α]
  : TSet α (OrdList α) where
  count := fun s => s.val.length
  contains := fun a s => sortedContains a s.val
  empty := OrdList.empty
  isEmpty := fun s => s.val.isEmpty
  insert := fun a s => ⟨sortedInsertNoDup a s.val, sortedInsertNoDup_sorted a s.val s.property⟩
  remove := fun a s => ⟨sortedRemove a s.val, sortedRemove_sorted a s.val s.property⟩
  ofList := OrdList.ofList
  toList := fun s => s.val
  filter := fun s p => ⟨s.val.filter p, sorted_filter s.val p s.property⟩
  union := fun s1 s2 => ⟨sortedMergeNoDup s1.val s2.val,
    sortedMergeNoDup_sorted s1.val s2.val s1.property s2.property⟩
  diff := fun s1 s2 => ⟨sortedDiffNoDup s1.val s2.val,
    sortedDiffNoDup_sorted s1.val s2.val s1.property s2.property⟩
  intersection := fun s1 s2 => ⟨sortedIntersectNoDup s1.val s2.val,
    sortedIntersectNoDup_sorted s1.val s2.val s1.property s2.property⟩
  subsets := OrdList.sublists
  empty_count := by simp [OrdList.empty]
  empty_contains := by intro ; rfl
  isEmpty_iff_count_zero := by simp
  contains_insert_self := fun a s =>
    sortedInsertNoDup_contains_self a s.val s.property
  contains_insert_other := fun a₁ a₂ s h =>
    sortedInsertNoDup_contains_other a₁ a₂ s.val h s.property
  insert_idempotent := fun a s => by
    show (sortedInsertNoDup a (sortedInsertNoDup a s.val)) =
         (sortedInsertNoDup a s.val)
    exact sortedInsertNoDup_idempotent a s.val s.property
  count_insert := fun a s => by
    show (sortedInsertNoDup a s.val).length = _
    exact sortedInsertNoDup_length a s.val s.property
  contains_remove_self := fun a s =>
    sortedRemove_contains_self a s.val s.property
  contains_remove_other := fun a₁ a₂ s h =>
    sortedRemove_contains_other a₁ a₂ s.val h s.property
  count_remove := fun a s => by
    show (sortedRemove a s.val).length = _
    exact sortedRemove_length a s.val s.property
  contains_union := fun a s1 s2 => by
    show sortedContains a (sortedMergeNoDup s1.val s2.val) = _
    exact sortedMergeNoDup_contains a s1.val s2.val s1.property s2.property
  contains_diff := fun a s1 s2 =>
    sortedDiffNoDup_contains a s1.val s2.val s1.property s2.property
  toList_contains_iff := fun a s => sortedContains_iff a s.val s.property
  subsets_iff := by
    simp ; intro l1 hl1 l2 hl2 ; simp [sortedContains_iff _ _ hl1, sortedContains_iff _ _ hl2, sublists]
    constructor
    · grind
    · apply OrdList.mem_contains_then_is_sublist <;> assumption

open OrdList OrdArray in
instance [Ord α] [TransOrd α] [LawfulEqOrd α] [DecidableEq α]
  : TSet α (OrdArray α) where
  count := fun s => s.val.size
  contains := fun a s => sortedContains a s.val.toList
  empty := OrdArray.empty
  isEmpty := fun s => s.val.isEmpty
  insert := fun a s => ⟨ordArrayInsert a s.val,
    ordArrayInsert_sorted a s.val s.property⟩
  remove := fun a s => ⟨ordArrayRemove a s.val,
    ordArrayRemove_sorted a s.val s.property⟩
  ofList := OrdArray.ofList
  toList := fun s => s.val.toList
  filter := fun s p => ⟨s.val.filter p, array_filter_sorted s.val p s.property⟩
  union := fun s1 s2 => ⟨Array.mergeDedup s1.val s2.val,
    mergeDedup_sorted s1.val s2.val s1.property s2.property⟩
  diff := fun s1 s2 => ⟨ordArrayDiff s1.val s2.val,
    ordArrayDiff_sorted s1.val s2.val s1.property s2.property⟩
  intersection := fun s1 s2 => ⟨ordArrayIntersect s1.val s2.val,
    ordArrayIntersect_sorted s1.val s2.val s1.property s2.property⟩
  subsets := OrdArray.subarrays
  -- Proofs: reduce to sorted list lemmas via bridge lemmas
  empty_count := by simp [OrdArray.empty]
  empty_contains := by intro ; rfl
  isEmpty_iff_count_zero := by simp [Array.isEmpty]
  contains_insert_self := fun a s => by
    show sortedContains a (ordArrayInsert a s.val).toList = true
    rw [ordArrayInsert_toList a s.val s.property]
    exact sortedInsertNoDup_contains_self a s.val.toList s.property
  contains_insert_other := fun a₁ a₂ s h => by
    show sortedContains a₁ (ordArrayInsert a₂ s.val).toList = sortedContains a₁ s.val.toList
    rw [ordArrayInsert_toList a₂ s.val s.property]
    exact sortedInsertNoDup_contains_other a₁ a₂ s.val.toList h s.property
  insert_idempotent := fun a s => by
    show (ordArrayInsert a (ordArrayInsert a s.val)).toList =
         (ordArrayInsert a s.val).toList
    rw [ordArrayInsert_toList a (ordArrayInsert a s.val)
          (ordArrayInsert_sorted a s.val s.property),
        ordArrayInsert_toList a s.val s.property]
    exact sortedInsertNoDup_idempotent a s.val.toList s.property
  count_insert := fun a s => by
    show (ordArrayInsert a s.val).size =
      if sortedContains a s.val.toList then s.val.size else s.val.size + 1
    rw [Array.size_eq_length_toList, ordArrayInsert_toList a s.val s.property]
    simp [sortedInsertNoDup_length a s.val.toList s.property]
  contains_remove_self := fun a s => by
    show sortedContains a (ordArrayRemove a s.val).toList = false
    rw [ordArrayRemove_toList a s.val s.property]
    exact sortedRemove_contains_self a s.val.toList s.property
  contains_remove_other := fun a₁ a₂ s h => by
    show sortedContains a₁ (ordArrayRemove a₂ s.val).toList = sortedContains a₁ s.val.toList
    rw [ordArrayRemove_toList a₂ s.val s.property]
    exact sortedRemove_contains_other a₁ a₂ s.val.toList h s.property
  count_remove := fun a s => by
    show (ordArrayRemove a s.val).size =
      if sortedContains a s.val.toList then s.val.size - 1 else s.val.size
    rw [Array.size_eq_length_toList, ordArrayRemove_toList a s.val s.property]
    simp [sortedRemove_length a s.val.toList s.property]
  contains_union := fun a s1 s2 => by
    show sortedContains a (Array.mergeDedup s1.val s2.val).toList =
      (sortedContains a s1.val.toList || sortedContains a s2.val.toList)
    rw [mergeDedup_toList s1.val s2.val s1.property s2.property]
    exact sortedMergeNoDup_contains a s1.val.toList s2.val.toList s1.property s2.property
  contains_diff := fun a s1 s2 => by
    show sortedContains a (ordArrayDiff s1.val s2.val).toList =
      (sortedContains a s1.val.toList && !sortedContains a s2.val.toList)
    rw [ordArrayDiff_toList s1.val s2.val]
    exact sortedDiffNoDup_contains a s1.val.toList s2.val.toList s1.property s2.property
  toList_contains_iff := fun a s => sortedContains_iff a s.val.toList s.property
  subsets_iff := by
    simp ; intro l1 hl1 l2 hl2 ; simp [sortedContains_iff _ _ hl1, sortedContains_iff _ _ hl2, subarrays, sublists, toOrdList, ofOrdList]
    constructor
    · grind
    · intro h ; exists l1.toList ; simp ; apply OrdList.mem_contains_then_is_sublist <;> try assumption
      simp ; assumption

class TMultiset (α : outParam (Type u)) (κ : Type v) where
  empty : κ
  insert : α → κ → κ
  remove : α → κ → κ
  contains : α → κ → Bool
  count : α → κ → Nat
  size : κ → Nat
  toList : κ → List α
  empty_size : size empty = 0
  empty_count (elem : α) : count elem empty = 0
  empty_contains (elem : α) : contains elem empty = false
  toList_contains_iff (elem : α) (s : κ) :
    contains elem s = true ↔ elem ∈ toList s
  -- contains_def (elem : α) (s : κ) :
  --   contains elem s = (count elem s > 0)
  -- count_insert_self (elem : α) (s : κ) :
  --   count elem (insert elem s) = count elem s + 1
  -- count_insert_other (elem₁ elem₂ : α) (s : κ) (h : elem₁ ≠ elem₂) :
  --   count elem₁ (insert elem₂ s) = count elem₁ s
  -- size_insert (elem : α) (s : κ)  :
  --   size (insert elem s) = size s + 1
  -- count_remove_self (elem : α) (s : κ) :
  --   count elem (remove elem s) = if count elem s > 0 then count elem s - 1 else 0
  -- count_remove_other (elem₁ elem₂ : α) (s : κ) (h : elem₁ ≠ elem₂) :
  --   count elem₁ (remove elem₂ s) = count elem₁ s
  -- size_remove (elem : α) (s : κ) :
  --   size (remove elem s) = if contains elem s then size s - 1 else size s

instance [TMultiset α κ] : Membership α κ where
  mem s a := TMultiset.contains a s = true

instance instEnumerationTMultisetContains [TMultiset α κ] (k : κ) : Veil.Enumeration ({ a : α // TMultiset.contains a k }) where
  allValues := TMultiset.toList k |>.attachWith _ (by simp [TMultiset.toList_contains_iff])
  complete := by simp [TMultiset.toList_contains_iff]

instance [TMultiset α κ] (k : κ) : Veil.Enumeration ({ a : α // a ∈ k }) := instEnumerationTMultisetContains k

/-- When implementing `Multiset`, a key is mapped to its multiplicity
*minus 1*. -/
abbrev TMapMultiset (α : Type) [Ord α] := Std.ExtTreeMap α Nat

instance [Ord α] : Inhabited (TMapMultiset α) := ⟨Std.ExtTreeMap.empty⟩

instance [Ord α] [TransOrd α] : Ord (TMapMultiset α) where
  compare m₁ m₂ := compare m₁.toList m₂.toList


open Std.ExtDTreeMap

instance instTMultiSetWithExtTreeMap [Ord α] [TransOrd α]
  [LawfulEqOrd α] : TMultiset α (TMapMultiset α) where
  empty := Std.ExtTreeMap.empty
  insert elem s :=
    s.alter elem fun
      | some n => some n.succ
      | none   => some 0

  remove elem s :=
    s.alter elem fun
      | some n => if h : n > 0 then some n.pred else none
      | none   => none

  count elem s := match s.get? elem with
    | some n => n.succ
    | none => 0

  contains elem s := s.contains elem
  size s := s.foldl (fun acc _ count => acc + count.succ) 0
  toList s := s.foldl (fun acc elem count => acc ++ List.replicate count.succ elem) []
  empty_size := by simp [Std.ExtTreeMap.empty]; rfl
  empty_count elem := by grind
  empty_contains elem := by grind
  toList_contains_iff := by
    intros elem s
    simp [Std.ExtTreeMap.contains_iff_mem, Std.ExtTreeMap.foldl_eq_foldl_toList,
      Std.ExtTreeMap.getElem?_eq_some_iff]

instance instTMultisetForFin (n : Nat) : TMultiset (Fin n) (TMapMultiset (Fin n)) :=
  instTMultiSetWithExtTreeMap


class TMap (α : Type) (β : Type) (κ : Type) where
  count : κ → Nat
  contains : α → κ → Bool
  lookup : α → κ → Option β
  empty : κ
  insert : α → β → κ → κ
  remove : α → κ → κ
  toList : κ → List (α × β)
  keys : κ → List α
  values : κ → List β
  filter : κ → (α → β → Bool) → κ
  equal : κ → κ → Bool


instance [BEq α] [BEq β] [Ord α] [TransOrd α] [LawfulEqOrd α]
  : TMap α β (ExtTreeMap α β) where
  count := fun m => m.inner.size
  contains := fun k m => m.inner.contains k
  lookup := fun k m => get? m.inner k
  empty := ExtTreeMap.empty
  insert := fun k v m => ⟨m.inner.insert k v⟩
  remove := fun k m => ⟨m.inner.erase k⟩
  toList := fun m => m.toList
  keys := fun m => m.toList.map Prod.fst
  values := fun m => m.toList.map Prod.snd
  filter := fun m p => ⟨m.inner.filter p⟩
  equal := fun m1 m2 => m1.toList == m2.toList
