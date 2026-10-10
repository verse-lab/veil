module

public import Veil.Frontend.DSL.State.Types

@[expose] public section

/-!
# Finite subsets as bit vectors

`Veil.BitVecAsFinset α` stores a subset of the finitely encodable type `α` as a bit vector of
width `FinEncodable.card α`: bit `FinEncodable.equiv a` is set iff `a` is in the set.
Membership is a bit test, and `Repr` shows the elements as `{a, b}`. It is a field
representation for relations (`veil_set_field_representation relation Veil.BitVecAsFinset`,
instances in `Concrete.lean`) and the carrier of `Quorum`, `MinQuorum` and `ByzNSet`
(`Veil/Frontend/Std.lean`).
-/

open Veil

/-! ## `BitVec` -/

/-- Number of set bits. -/
def BitVec.popCount (bv : BitVec n) : Nat := bv.cpopNatRec n 0

/-- `x.getLsbD i` with `Nat.testBit` unfolded. `Nat.testBit` is an ordinary function of `Init`, so
`x[i]` and `x.getLsbD i` compile to a call into the runtime library for every test; the shift, mask
and comparison here are compiler primitives that the C backend inlines. -/
@[inline] def BitVec.getLsbInline (x : BitVec w) (i : Nat) : Bool := 1 &&& (x.toNat >>> i) != 0

@[simp] theorem BitVec.getLsbInline_eq_getLsbD (x : BitVec w) (i : Nat) :
    x.getLsbInline i = x.getLsbD i := rfl

/-- The bit vector of width `n` whose lowest `k` bits are set. -/
def BitVec.lowOnes (n k : Nat) : BitVec n := BitVec.setWidth n (BitVec.allOnes k)

theorem BitVec.popCount_allOnes (n : Nat) : (BitVec.allOnes n).popCount = n := by simp [BitVec.popCount]

theorem BitVec.popCount_lowOnes {n k : Nat} (h : k ≤ n) : (BitVec.lowOnes n k).popCount = k := by
  unfold BitVec.popCount BitVec.lowOnes
  rw [← BitVec.toNat_cpop, BitVec.toNat_cpop_setWidth_eq_of_le h]
  simp

/-- Two bit vectors share at least `x.popCount + y.popCount - n` set bits. -/
theorem BitVec.popCount_add_popCount_le (x y : BitVec n) :
    x.popCount + y.popCount ≤ n + (x &&& y).popCount := by
  unfold BitVec.popCount
  have h : ∀ k, x.cpopNatRec k 0 + y.cpopNatRec k 0 ≤ k + (x &&& y).cpopNatRec k 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [BitVec.cpopNatRec_succ, BitVec.cpopNatRec_add, BitVec.getLsbD_and]
      cases x.getLsbD k <;> cases y.getLsbD k <;> simp_all <;> omega
  exact h n

theorem BitVec.cpopNatRec_zero_eq_countP (x : BitVec w) (k : Nat) :
    x.cpopNatRec k 0 = (List.range k).countP (x.getLsbD ·) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BitVec.cpopNatRec_succ, BitVec.cpopNatRec_add, ih, List.range_succ, List.countP_append]
    simp only [List.countP_cons, List.countP_nil]
    cases x.getLsbD k <;> simp

theorem BitVec.popCount_eq_countP (x : BitVec n) :
    x.popCount = (List.range n).countP (x.getLsbD ·) :=
  BitVec.cpopNatRec_zero_eq_countP x n

theorem BitVec.exists_getLsbD_of_popCount_pos (x : BitVec n) (h : 0 < x.popCount) :
    ∃ i, i < n ∧ x.getLsbD i = true := by
  rw [BitVec.popCount_eq_countP] at h
  obtain ⟨i, hi, hx⟩ := List.countP_pos_iff.mp h
  exact ⟨i, List.mem_range.mp hi, hx⟩

theorem BitVec.popCount_le_popCount {x y : BitVec n}
    (h : ∀ i, i < n → x.getLsbD i = true → y.getLsbD i = true) : x.popCount ≤ y.popCount := by
  rw [BitVec.popCount_eq_countP, BitVec.popCount_eq_countP]
  exact List.countP_mono_left fun i hi => h i (List.mem_range.mp hi)

namespace Veil

/-! ## `BitVecAsFinset` -/

/-- A subset of the finitely encodable type `α`, stored as a bit vector of width
`FinEncodable.card α`: bit `FinEncodable.equiv a` is set iff `a` is in the set. -/
@[ext]
structure BitVecAsFinset (α : Type u) [FinEncodable α] where
  bits : BitVec (FinEncodable.card α)
deriving DecidableEq, Hashable

namespace BitVecAsFinset

variable {α : Type u} [inst : FinEncodable α]

instance : Membership α (BitVecAsFinset α) where
  mem s a := s.bits[inst.equiv a]

theorem mem_def {a : α} {s : BitVecAsFinset α} : a ∈ s ↔ s.bits[inst.equiv a] = true := Iff.rfl

theorem mem_iff_getLsbD {a : α} {s : BitVecAsFinset α} :
    a ∈ s ↔ s.bits.getLsbD (inst.equiv a).val = true := by
  rw [mem_def, Fin.getElem_fin, BitVec.getLsbD_eq_getElem]

-- `decide (a ∈ s)` must compile to the bit test itself, inside the caller's loop:
-- * `macro_inline`: an instance is never inlined by the compiler, and otherwise the `FinEncodable`
--   dictionary is passed at run time and `equiv` is a closure call;
-- * `getLsbInline` rather than `s.bits[_]`, which is a call to `Nat.testBit`;
-- * the term itself (`a ∈ s` is definitionally `s.bits.getLsbInline _ = true`): `inferInstanceAs`
--   puts the body into an auxiliary definition that is not inlined, and `decidable_of_iff` leaves a
--   redundant branch.
@[macro_inline] instance instDecidableMem (a : α) (s : BitVecAsFinset α) : Decidable (a ∈ s) :=
  instDecidableEqBool (s.bits.getLsbInline (inst.equiv a).val) true

/-- Number of elements. -/
def card (s : BitVecAsFinset α) : Nat := s.bits.popCount

/-- The elements, in encoding order. -/
def toList (s : BitVecAsFinset α) : List α :=
  (List.finRange inst.card).filterMap fun i => if s.bits[i] then some (inst.equiv.symm i) else none

def empty : BitVecAsFinset α := ⟨0⟩
/-- The full set containing all elements of `α`. -/
def full : BitVecAsFinset α := ⟨BitVec.allOnes _⟩
def insert (a : α) (s : BitVecAsFinset α) : BitVecAsFinset α :=
  ⟨s.bits ||| BitVec.twoPow _ (inst.equiv a)⟩
def erase (a : α) (s : BitVecAsFinset α) : BitVecAsFinset α :=
  ⟨s.bits &&& ~~~BitVec.twoPow _ (inst.equiv a)⟩
def inter (s t : BitVecAsFinset α) : BitVecAsFinset α := ⟨s.bits &&& t.bits⟩
def union (s t : BitVecAsFinset α) : BitVecAsFinset α := ⟨s.bits ||| t.bits⟩
def ofList (l : List α) : BitVecAsFinset α := l.foldl (fun s a => s.insert a) empty

instance : Inhabited (BitVecAsFinset α) := ⟨empty⟩
instance : EmptyCollection (BitVecAsFinset α) := ⟨empty⟩

theorem mem_inter {a : α} {s t : BitVecAsFinset α} : a ∈ s.inter t ↔ a ∈ s ∧ a ∈ t := by
  simp only [mem_iff_getLsbD, inter, BitVec.getLsbD_and, Bool.and_eq_true]

theorem card_add_card_le (s t : BitVecAsFinset α) :
    s.card + t.card ≤ inst.card + (s.inter t).card :=
  BitVec.popCount_add_popCount_le s.bits t.bits

theorem card_full : (full : BitVecAsFinset α).card = inst.card := BitVec.popCount_allOnes _

theorem exists_mem_of_card_pos (s : BitVecAsFinset α) (h : 0 < s.card) : ∃ a, a ∈ s := by
  obtain ⟨i, hi, hs⟩ := BitVec.exists_getLsbD_of_popCount_pos s.bits h
  refine ⟨inst.equiv.symm ⟨i, hi⟩, ?_⟩
  rw [mem_iff_getLsbD, Equiv.apply_symm_apply]
  exact hs

theorem exists_mem_of_card_lt_add (s t : BitVecAsFinset α) (h : inst.card < s.card + t.card) :
    ∃ a, a ∈ s ∧ a ∈ t := by
  have := card_add_card_le s t
  obtain ⟨a, ha⟩ := exists_mem_of_card_pos (s.inter t) (by omega)
  exact ⟨a, mem_inter.mp ha⟩

theorem card_le_card {s t : BitVecAsFinset α} (h : ∀ a, a ∈ s → a ∈ t) : s.card ≤ t.card := by
  show s.bits.popCount ≤ t.bits.popCount
  apply BitVec.popCount_le_popCount
  intro i hi hs
  have := h (inst.equiv.symm ⟨i, hi⟩)
  rw [mem_iff_getLsbD, mem_iff_getLsbD, Equiv.apply_symm_apply] at this
  exact this hs

instance [Repr α] : Repr (BitVecAsFinset α) where
  reprPrec s _ :=
    Std.Format.bracket "{" (Std.Format.joinSep (s.toList.map repr) ("," ++ Std.Format.line)) "}"

instance [Repr α] : Lean.ToJson (BitVecAsFinset α) where
  toJson s := Lean.Json.str (toString (repr s))

instance : Ord (BitVecAsFinset α) where
  compare s t := compare s.bits t.bits

instance : Std.ReflOrd (BitVecAsFinset α) where
  compare_self := by
    have tmp : Std.ReflOrd (BitVec inst.card) := inferInstance
    intros ; dsimp [compare] ; apply tmp.compare_self

instance : Std.LawfulEqOrd (BitVecAsFinset α) where
  eq_of_compare := by
    have tmp : Std.LawfulEqOrd (BitVec inst.card) := inferInstance
    intros ; dsimp [compare] at * ; ext1 ; apply tmp.eq_of_compare ; assumption

instance : Std.OrientedOrd (BitVecAsFinset α) where
  eq_swap := by
    have tmp : Std.OrientedOrd (BitVec inst.card) := inferInstance
    intros ; dsimp [compare] at * ; apply tmp.eq_swap

instance : Std.TransOrd (BitVecAsFinset α) where
  isLE_trans := by
    have tmp : Std.TransOrd (BitVec inst.card) := inferInstance
    intros ; dsimp [compare] at * ; apply tmp.isLE_trans <;> assumption

instance : Enumeration (BitVecAsFinset α) where
  allValues := (Enumeration.allValues (α := BitVec inst.card)).map BitVecAsFinset.mk
  complete := fun s => List.mem_map.mpr ⟨s.bits, Enumeration.complete _, rfl⟩

/-- Encoded by its bits (`BitVec.toFin`), the same order as its `Enumeration`. -/
@[always_inline]
instance : FinEncodable (BitVecAsFinset α) where
  card := 2 ^ inst.card
  equiv := { toFun := fun s => s.bits.toFin
             invFun := fun i => ⟨BitVec.ofFin i⟩
             left_inv := fun _ => rfl
             right_inv := fun _ => rfl }

/-! ## Subsets -/

/-- The subsets of `α` whose number of elements satisfies `p`. `Quorum` and `MinQuorum`
(`Veil/Frontend/Std.lean`) are instances of it.

As an `abbrev` of `Subtype`, it takes `DecidableEq`, `Hashable`, `Ord` with its laws (`Std.TransOrd`,
`Std.LawfulEqOrd`, ...), `Repr`, `ToJson` and `Enumeration` from the generic `Subtype` instances,
which act on `.val`. -/
abbrev Sized (α : Type u) [FinEncodable α] (p : Nat → Prop) := { s : BitVecAsFinset α // p s.card }

/-! Membership, which has no generic `Subtype` counterpart, is stated for every subtype of
`BitVecAsFinset α`, not for `Sized α p`: type class resolution may see the type fully unfolded
(`#model_check` reduces `__veil_inst.quorum` to `{ s // (fun k => …) s.card }`), which
`Sized ?α ?p` does not unify with (`?p s.card` is not a pattern), while `Subtype ?P` does. -/

section Subtype

variable {P : BitVecAsFinset α → Prop}

instance instMembershipSubtype : Membership α { s : BitVecAsFinset α // P s } where
  mem q a := a ∈ q.val

theorem mem_val {a : α} {q : { s : BitVecAsFinset α // P s }} : a ∈ q ↔ a ∈ q.val := Iff.rfl

@[macro_inline] instance instDecidableMemSubtype (a : α) (q : { s : BitVecAsFinset α // P s }) :
    Decidable (a ∈ q) :=
  instDecidableMem a q.val

end Subtype

end BitVecAsFinset

end Veil
