import Std
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Destutter
import Veil.Frontend.DSL.State.Types
import Veil.Frontend.DSL.State.Instances

/-! # Sorted List -/

/-! ## Sorting relation -/

abbrev OrdList.cmpLt [Ord α] (a b : α) : Prop := compare a b = Ordering.lt

/-- A strictly sorted list, used as a set representation. -/
abbrev OrdList (α : Type u) [Ord α] : Type u :=
  { l : List α // l.Pairwise (OrdList.cmpLt (α := α)) }

namespace OrdList

open Std

/-! ## Helper functions on raw lists -/

section Defs
variable {α : Type u} [Ord α]

@[inline]
def empty : OrdList α := ⟨[], List.Pairwise.nil⟩

def ofList.inner [TransOrd α] (l : List α) : List α :=
  (l.mergeSort (fun a b => compare a b != .gt)).destutter cmpLt

private theorem mem_destutter'_of_weakly_sorted [TransOrd α] [LawfulEqOrd α]
    (a : α) (l : List α)
    (hsorted : (a :: l).Pairwise (fun p q => (compare p q != .gt) = true))
    (x : α) (hmem : x ∈ a :: l) :
    x ∈ l.destutter' (cmpLt (α := α)) a := by
  induction l generalizing a with
  | nil => simp [List.destutter'] ; simp at hmem ; exact hmem
  | cons b t ih =>
    rw [List.destutter'_cons]
    have hab : (compare a b != .gt) = true :=
      List.rel_of_pairwise_cons hsorted (by simp)
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · -- x = a
      split_ifs with h
      · simp
      · exact List.mem_destutter' _ _ _
    · -- x ∈ b :: t
      split_ifs with h
      · -- cmpLt a b, result = a :: destutter' cmpLt b t
        exact List.mem_cons.mpr (Or.inr
          (ih b (List.Pairwise.of_cons hsorted) hmem'))
      · -- ¬ cmpLt a b, and compare a b ≠ .gt, so compare a b = .eq
        have heq : compare a b = .eq := by
          rcases h' : compare a b with _ | _ | _ <;> simp_all [cmpLt]
        have hab_eq : a = b := LawfulEqOrd.eq_of_compare heq
        subst hab_eq
        -- result = destutter' cmpLt a t, and x ∈ a :: t
        have hsorted' : (a :: t).Pairwise (fun p q => (compare p q != .gt) = true) :=
          hsorted.sublist ((List.sublist_cons_self a t).cons₂ a)
        exact ih a hsorted' (by rcases List.mem_cons.mp hmem' with rfl | h <;> simp_all)

-- TODO check these proofs later?

private abbrev le_fn (α : Type u) [Ord α] : α → α → Bool :=
  fun a b => compare a b != .gt

private theorem isLE_of_ne_gt {o : Ordering} (h : o ≠ .gt) : o.isLE = true := by
  cases o <;> simp_all

private theorem ne_gt_of_isLE {o : Ordering} (h : o.isLE = true) : o ≠ .gt := by
  cases o <;> simp_all

private theorem mergeSort_pairwise_le [TransOrd α] [OrientedOrd α] (l : List α) :
    (l.mergeSort (le_fn α)).Pairwise (fun a b => (le_fn α a b) = true) := by
  apply List.pairwise_mergeSort
  · intro a b c hab hbc
    simp only [le_fn, bne_iff_ne, ne_eq] at hab hbc ⊢
    exact ne_gt_of_isLE (TransOrd.isLE_trans (isLE_of_ne_gt hab) (isLE_of_ne_gt hbc))
  · intro a b
    simp only [le_fn, Bool.or_eq_true, bne_iff_ne, ne_eq]
    by_contra h ; push_neg at h
    have h1 := h.1 ; have h2 := h.2
    have := OrientedCmp.eq_swap (cmp := compare) (a := a) (b := b)
    cases ha : compare a b <;> simp_all

theorem ofList.inner_spec [TransOrd α] [LawfulEqOrd α] (l : List α) :
    (ofList.inner l).Pairwise (cmpLt (α := α)) ∧
    ∀ x, x ∈ ofList.inner l ↔ x ∈ l := by
  have hle : (fun a b : α => compare a b != .gt) = le_fn α := rfl
  constructor
  · have : Trans (cmpLt (α := α)) cmpLt cmpLt := ⟨TransCmp.lt_trans⟩
    apply List.isChain_iff_pairwise.mp (List.isChain_destutter _ _)
  · intro x
    simp only [ofList.inner, hle]
    constructor
    · -- forward: x ∈ destutter ... → x ∈ l
      intro hmem
      have hsub := List.destutter_sublist (cmpLt (α := α)) (l.mergeSort (le_fn α))
      exact (List.mergeSort_perm l (le_fn α)).mem_iff.mp (hsub.mem hmem)
    · -- backward: x ∈ l → x ∈ destutter ...
      intro hmem
      have hmem_sorted := (List.mergeSort_perm l (le_fn α)).mem_iff.mpr hmem
      have hsorted := mergeSort_pairwise_le (α := α) l
      cases hl : l.mergeSort (le_fn α) with
      | nil => simp_all
      | cons a t =>
        rw [hl] at hmem_sorted hsorted
        rw [List.destutter_cons']
        exact mem_destutter'_of_weakly_sorted a t hsorted x hmem_sorted

/-- Build an `OrdList` from an arbitrary list by sorting and removing duplicates. -/
@[inline]
def ofList [TransOrd α] [LawfulEqOrd α] (l : List α) : OrdList α :=
  ⟨ofList.inner l, (ofList.inner_spec l).left⟩

/-- O(n) membership test on a sorted list with early termination. -/
def sortedContains (a : α) : List α → Bool
  | [] => false
  | h :: t =>
    match compare a h with
    | .lt => false
    | .eq => true
    | .gt => sortedContains a t

/-- Insert `a` into a sorted list maintaining order; duplicates are not inserted. -/
def sortedInsertNoDup (a : α) : List α → List α
  | [] => [a]
  | h :: t =>
    match compare a h with
    | .lt => a :: h :: t
    | .eq => h :: t
    | .gt => h :: sortedInsertNoDup a t

/-- Remove `a` from a sorted list, exploiting sortedness to stop early. -/
def sortedRemove (a : α) : List α → List α
  | [] => []
  | h :: t =>
    match compare a h with
    | .lt => h :: t
    | .eq => t
    | .gt => h :: sortedRemove a t

/-- This is only for proving -/
private def sortedMergeGeneral (keepl? keepr? keepboth? : Bool) : List α → List α → List α
  | [], r => if keepr? then r else []
  | l, [] => if keepl? then l else []
  | a :: l', b :: r' =>
    match compare a b with
    | .lt =>
      let res := sortedMergeGeneral keepl? keepr? keepboth? l' (b :: r')
      if keepl? then a :: res else res
    | .eq =>
      let res := sortedMergeGeneral keepl? keepr? keepboth? l' r'
      if keepboth? then a :: res else res
    | .gt =>
      let res := sortedMergeGeneral keepl? keepr? keepboth? (a :: l') r'
      if keepr? then b :: res else res
termination_by l r => l.length + r.length

/-- Merge two sorted-no-dup lists into one (set union), O(n + m). -/
def sortedMergeNoDup : List α → List α → List α
  | [], r => r
  | l, [] => l
  | a :: l', b :: r' =>
    match compare a b with
    | .lt => a :: sortedMergeNoDup l' (b :: r')
    | .eq => a :: sortedMergeNoDup l' r'
    | .gt => b :: sortedMergeNoDup (a :: l') r'
termination_by l r => l.length + r.length

/-- Set difference of two sorted lists, O(n + m). -/
def sortedDiffNoDup : List α → List α → List α
  | [], _ => []
  | l, [] => l
  | a :: l', b :: r' =>
    match compare a b with
    | .lt => a :: sortedDiffNoDup l' (b :: r')
    | .eq => sortedDiffNoDup l' r'
    | .gt => sortedDiffNoDup (a :: l') r'
termination_by l r => l.length + r.length

/-- Intersection of two sorted lists, O(n + m). -/
def sortedIntersectNoDup : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | a :: l', b :: r' =>
    match compare a b with
    | .lt => sortedIntersectNoDup l' (b :: r')
    | .eq => a :: sortedIntersectNoDup l' r'
    | .gt => sortedIntersectNoDup (a :: l') r'
termination_by l r => l.length + r.length

private theorem sortedMergeNoDup_eq_general (l₁ l₂ : List α) :
    sortedMergeNoDup l₁ l₂ = sortedMergeGeneral true true true l₁ l₂ := by
  induction l₁, l₂ using sortedMergeNoDup.induct (α := α) with
  | case1 r => simp [sortedMergeNoDup, sortedMergeGeneral]
  | case2 l hl => simp [sortedMergeNoDup, sortedMergeGeneral]
  | case3 a l' b r' hlt ih => simp [sortedMergeNoDup, sortedMergeGeneral, hlt, ih]
  | case4 a l' b r' heq ih => simp [sortedMergeNoDup, sortedMergeGeneral, heq, ih]
  | case5 a l' b r' hgt ih => simp [sortedMergeNoDup, sortedMergeGeneral, hgt, ih]

private theorem sortedDiffNoDup_eq_general (l₁ l₂ : List α) :
    sortedDiffNoDup l₁ l₂ = sortedMergeGeneral true false false l₁ l₂ := by
  induction l₁, l₂ using sortedDiffNoDup.induct (α := α) with
  | case1 r => simp [sortedDiffNoDup, sortedMergeGeneral]
  | case2 l hl => simp [sortedDiffNoDup, sortedMergeGeneral]
  | case3 a l' b r' hlt ih => simp [sortedDiffNoDup, sortedMergeGeneral, hlt, ih]
  | case4 a l' b r' heq ih => simp [sortedDiffNoDup, sortedMergeGeneral, heq, ih]
  | case5 a l' b r' hgt ih => simp [sortedDiffNoDup, sortedMergeGeneral, hgt, ih]

private theorem sortedIntersectNoDup_eq_general (l₁ l₂ : List α) :
    sortedIntersectNoDup l₁ l₂ = sortedMergeGeneral false false true l₁ l₂ := by
  induction l₁, l₂ using sortedIntersectNoDup.induct (α := α) with
  | case1 r => simp [sortedIntersectNoDup, sortedMergeGeneral]
  | case2 l hl => simp [sortedIntersectNoDup, sortedMergeGeneral]
  | case3 a l' b r' hlt ih => simp [sortedIntersectNoDup, sortedMergeGeneral, hlt, ih]
  | case4 a l' b r' heq ih => simp [sortedIntersectNoDup, sortedMergeGeneral, heq, ih]
  | case5 a l' b r' hgt ih => simp [sortedIntersectNoDup, sortedMergeGeneral, hgt, ih]

private theorem sortedMergeGeneral_sub (x : α) (kl kr kb : Bool) (l₁ l₂ : List α) :
    x ∈ sortedMergeGeneral kl kr kb l₁ l₂ → x ∈ l₁ ∨ x ∈ l₂ := by
  induction l₁, l₂ using sortedMergeGeneral.induct (keepl? := kl) (keepr? := kr) (keepboth? := kb) with
  | x_1 => exact inferInstance
  | case1 | case2 | case3 | case4 => simp_all [sortedMergeGeneral]
  | case5 _ _ _ _ hcmp hk ih | case7 _ _ _ _ hcmp hk ih | case9 _ _ _ _ hcmp hk ih =>
    subst hk; simp_all [sortedMergeGeneral, List.mem_cons]; tauto
  | case6 _ _ _ _ hcmp hk ih | case8 _ _ _ _ hcmp hk ih | case10 _ _ _ _ hcmp hk ih =>
    simp only [Bool.not_eq_true] at hk; subst hk; simp_all [sortedMergeGeneral, List.mem_cons]; tauto

private theorem sortedMergeGeneral_sorted [TransOrd α] [LawfulEqOrd α]
    (kl kr kb : Bool) (l₁ l₂ : List α)
    (hs₁ : l₁.Pairwise (cmpLt (α := α))) (hs₂ : l₂.Pairwise (cmpLt (α := α))) :
    (sortedMergeGeneral kl kr kb l₁ l₂).Pairwise (cmpLt (α := α)) := by
  induction l₁, l₂ using sortedMergeGeneral.induct (keepl? := kl) (keepr? := kr) (keepboth? := kb) with
  | x_1 => exact inferInstance
  | case1 | case2 | case3 | case4 => simp_all [sortedMergeGeneral]
  | case5 _ _ _ _ hcmp hk ih =>
    subst hk; unfold sortedMergeGeneral; simp [hcmp]
    refine ⟨fun x hx => ?_, ih (List.Pairwise.of_cons hs₁) hs₂⟩
    rcases sortedMergeGeneral_sub x _ _ _ _ _ hx with hm | hm
    · exact List.rel_of_pairwise_cons hs₁ hm
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact hcmp
      · exact TransCmp.lt_trans hcmp (List.rel_of_pairwise_cons hs₂ hm)
  | case6 _ _ _ _ hcmp hk ih =>
    simp only [Bool.not_eq_true] at hk; subst hk; unfold sortedMergeGeneral; simp [hcmp]
    exact ih (List.Pairwise.of_cons hs₁) hs₂
  | case7 _ _ _ _ hcmp hk ih =>
    subst hk; unfold sortedMergeGeneral; simp [hcmp]
    have hab := LawfulEqOrd.eq_of_compare hcmp
    refine ⟨fun x hx => ?_, ih (List.Pairwise.of_cons hs₁) (List.Pairwise.of_cons hs₂)⟩
    rcases sortedMergeGeneral_sub x _ _ _ _ _ hx with hm | hm
    · exact List.rel_of_pairwise_cons hs₁ hm
    · rw [hab]; exact List.rel_of_pairwise_cons hs₂ hm
  | case8 _ _ _ _ hcmp hk ih =>
    simp only [Bool.not_eq_true] at hk; subst hk; unfold sortedMergeGeneral; simp [hcmp]
    exact ih (List.Pairwise.of_cons hs₁) (List.Pairwise.of_cons hs₂)
  | case9 _ _ _ _ hcmp hk ih =>
    subst hk; unfold sortedMergeGeneral; simp [hcmp]
    refine ⟨fun x hx => ?_, ih hs₁ (List.Pairwise.of_cons hs₂)⟩
    rcases sortedMergeGeneral_sub x _ _ _ _ _ hx with hm | hm
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact OrientedCmp.lt_of_gt hcmp
      · exact TransCmp.lt_trans (OrientedCmp.lt_of_gt hcmp) (List.rel_of_pairwise_cons hs₁ hm)
    · exact List.rel_of_pairwise_cons hs₂ hm
  | case10 _ _ _ _ hcmp hk ih =>
    simp only [Bool.not_eq_true] at hk; subst hk; unfold sortedMergeGeneral; simp [hcmp]
    exact ih hs₁ (List.Pairwise.of_cons hs₂)

@[simp] theorem sortedMergeNoDup_nil_right (l : List α) :
    sortedMergeNoDup l [] = l := by
  cases l with | nil => simp [sortedMergeNoDup] | cons _ _ => simp [sortedMergeNoDup]

@[simp] theorem sortedDiffNoDup_nil_right (l : List α) :
    sortedDiffNoDup l [] = l := by
  cases l with | nil => simp [sortedDiffNoDup] | cons _ _ => simp [sortedDiffNoDup]

@[simp] theorem sortedIntersectNoDup_nil_right (l : List α) :
    sortedIntersectNoDup l [] = [] := by
  cases l with | nil => simp [sortedIntersectNoDup] | cons _ _ => simp [sortedIntersectNoDup]

end Defs

/-! ## Sorted list lemmas -/

section SortedLemmas
variable {α : Type u} [Ord α]

/-! ### Sortedness contradiction helpers -/

private theorem not_mem_of_cmpLt_cons [TransOrd α] [LawfulEqOrd α]
    {a b : α} {l : List α}
    (hab : compare a b = .lt) (hs : (b :: l).Pairwise (cmpLt (α := α))) :
    a ∉ b :: l := by
  intro hmem ; rcases List.mem_cons.mp hmem with rfl | h
  · simp [ReflOrd.compare_self] at hab
  · have := TransCmp.lt_trans hab (List.rel_of_pairwise_cons hs h)
    simp [ReflOrd.compare_self] at this

private theorem not_mem_of_cmpGt_cons [TransOrd α] [LawfulEqOrd α]
    {a b : α} {l : List α}
    (hab : compare a b = .gt) (hs : (a :: l).Pairwise (cmpLt (α := α))) :
    b ∉ a :: l := by
  intro hmem ; rcases List.mem_cons.mp hmem with rfl | h
  · simp [ReflOrd.compare_self] at hab
  · exact absurd (List.rel_of_pairwise_cons hs h) (by simp [cmpLt, hab])

/-
private theorem sortedMergeGeneral_mem [TransOrd α] [LawfulEqOrd α]
    (x : α) (kl kr kb : Bool) (l₁ l₂ : List α)
    (hs₁ : l₁.Pairwise (cmpLt (α := α))) (hs₂ : l₂.Pairwise (cmpLt (α := α))) :
    x ∈ sortedMergeGeneral kl kr kb l₁ l₂ ↔
      (kl = true ∧ x ∈ l₁ ∧ x ∉ l₂) ∨ (kr = true ∧ x ∈ l₂ ∧ x ∉ l₁) ∨
      (kb = true ∧ x ∈ l₁ ∧ x ∈ l₂) := by
  induction l₁, l₂ using sortedMergeGeneral.induct (keepl? := kl) (keepr? := kr) (keepboth? := kb) with
  | x_1 => exact inferInstance
  | case1 | case2 | case3 | case4 => simp_all [sortedMergeGeneral]
  | case5 a l' b r' hcmp hk ih =>
    subst hk
    have hunf : sortedMergeGeneral true kr kb (a :: l') (b :: r') =
      a :: sortedMergeGeneral true kr kb l' (b :: r') := by simp [sortedMergeGeneral, hcmp]
    rw [hunf, List.mem_cons, ih (List.Pairwise.of_cons hs₁) hs₂]
    have := not_mem_of_cmpLt_cons hcmp hs₂
    simp only [List.mem_cons, not_or] at *; tauto
  | case6 a l' b r' hcmp hk ih =>
    simp only [Bool.not_eq_true] at hk; subst hk
    have hunf : sortedMergeGeneral false kr kb (a :: l') (b :: r') =
      sortedMergeGeneral false kr kb l' (b :: r') := by simp [sortedMergeGeneral, hcmp]
    rw [hunf, ih (List.Pairwise.of_cons hs₁) hs₂]
    have := not_mem_of_cmpLt_cons hcmp hs₂
    simp only [List.mem_cons, not_or] at *; tauto
  | case7 a l' b r' hcmp hk ih =>
    subst hk; have hab := LawfulEqOrd.eq_of_compare hcmp; subst hab
    have hunf : sortedMergeGeneral kl kr true (a :: l') (a :: r') =
      a :: sortedMergeGeneral kl kr true l' r' := by simp [sortedMergeGeneral, ReflOrd.compare_self]
    rw [hunf, List.mem_cons, ih (List.Pairwise.of_cons hs₁) (List.Pairwise.of_cons hs₂)]
    have : a ∉ l' := fun h => by
      have := List.rel_of_pairwise_cons hs₁ h; simp [cmpLt, ReflOrd.compare_self] at this
    have : a ∉ r' := fun h => by
      have := List.rel_of_pairwise_cons hs₂ h; simp [cmpLt, ReflOrd.compare_self] at this
    simp only [List.mem_cons, not_or] at *; tauto
  | case8 a l' b r' hcmp hk ih =>
    simp only [Bool.not_eq_true] at hk; subst hk
    have hab := LawfulEqOrd.eq_of_compare hcmp; subst hab
    have hunf : sortedMergeGeneral kl kr false (a :: l') (a :: r') =
      sortedMergeGeneral kl kr false l' r' := by simp [sortedMergeGeneral, ReflOrd.compare_self]
    rw [hunf, ih (List.Pairwise.of_cons hs₁) (List.Pairwise.of_cons hs₂)]
    have : a ∉ l' := fun h => by
      have := List.rel_of_pairwise_cons hs₁ h; simp [cmpLt, ReflOrd.compare_self] at this
    have : a ∉ r' := fun h => by
      have := List.rel_of_pairwise_cons hs₂ h; simp [cmpLt, ReflOrd.compare_self] at this
    simp only [List.mem_cons, not_or] at *; tauto
  | case9 a l' b r' hcmp hk ih =>
    subst hk
    have hunf : sortedMergeGeneral kl true kb (a :: l') (b :: r') =
      b :: sortedMergeGeneral kl true kb (a :: l') r' := by simp [sortedMergeGeneral, hcmp]
    rw [hunf, List.mem_cons, ih hs₁ (List.Pairwise.of_cons hs₂)]
    have := not_mem_of_cmpGt_cons hcmp hs₁
    simp only [List.mem_cons, not_or] at *; tauto
  | case10 a l' b r' hcmp hk ih =>
    simp only [Bool.not_eq_true] at hk; subst hk
    have hunf : sortedMergeGeneral kl false kb (a :: l') (b :: r') =
      sortedMergeGeneral kl false kb (a :: l') r' := by simp [sortedMergeGeneral, hcmp]
    rw [hunf, ih hs₁ (List.Pairwise.of_cons hs₂)]
    have := not_mem_of_cmpGt_cons hcmp hs₁
    simp only [List.mem_cons, not_or] at *; tauto
-/

/-! ### Uniqueness of sorted lists -/

theorem sorted_nodup [TransOrd α] {l : List α} (hs : l.Pairwise (cmpLt (α := α))) : l.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  revert hs ; apply List.Pairwise.imp ; grind

theorem sorted_unique [TransOrd α] {l₁ l₂ : List α}
    (hs₁ : l₁.Pairwise (cmpLt (α := α)))
    (hs₂ : l₂.Pairwise (cmpLt (α := α)))
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    l₁ = l₂ := by
  apply List.Perm.eq_of_pairwise <;> try assumption
  on_goal 1=> intro a b _ _ h1 h2 ; whnf at h1 h2 ; have := OrientedCmp.gt_of_lt h1 ; grind
  rw [List.perm_ext_iff_of_nodup] ; assumption
  all_goals grind [sorted_nodup]

/-! ### `sortedContains` -/

theorem sortedContains_iff [TransOrd α] [LawfulEqOrd α] (a : α) (l : List α)
    (hs : l.Pairwise (cmpLt (α := α))) :
    sortedContains a l = true ↔ a ∈ l := by
  induction l with
  | nil => simp [sortedContains]
  | cons h t ih =>
    specialize ih (List.Pairwise.of_cons hs)
    simp only [sortedContains, List.mem_cons]
    constructor
    · grind
    · intro hm ; rcases hm with hm | hm
      · grind
      · have hm' := hm ; rw [← ih] at hm' ; rw [hm'] ; clear hm'
        have hha := OrientedCmp.gt_of_lt <| List.rel_of_pairwise_cons hs hm
        rw [hha]

/-! ### `sortedInsertNoDup` -/

-- The main two

theorem sortedInsertNoDup_intact_if_in [TransOrd α] {a : α} {l : List α} (hs : l.Pairwise (cmpLt (α := α)))
    (hmem : a ∈ l) :
    sortedInsertNoDup a l = l := by
  induction l with
  | nil => grind
  | cons h t ih =>
    specialize ih (List.Pairwise.of_cons hs)
    simp at hmem ; rcases hmem with hmem | hmem
    · subst h ; simp [sortedInsertNoDup]
    · simp only [sortedInsertNoDup, ih hmem]
      rw [List.pairwise_cons] at hs ; have := OrientedCmp.gt_of_lt (hs.left _ hmem) ; grind

theorem sortedInsertNoDup_new_in [TransOrd α] [LawfulEqOrd α] {a : α} {l : List α} (hs : l.Pairwise (cmpLt (α := α)))
    (hmem : a ∉ l) :
  ∃ pre suf, l = pre ++ suf ∧ sortedInsertNoDup a l = pre ++ (a :: suf) ∧
    (∀ x ∈ pre, cmpLt x a) ∧ (∀ x ∈ suf, cmpLt a x) := by
  induction l with
  | nil => simp [sortedInsertNoDup]
  | cons h t ih =>
    simp at hmem ; rcases hmem with ⟨hneq, hmem⟩
    specialize ih (List.Pairwise.of_cons hs) hmem
    rcases ih with ⟨pre, suf, heq, heq', hpre, hsuf⟩
    dsimp only [sortedInsertNoDup] ; split <;> rename_i hh
    · exists [], h :: t, rfl, rfl ; simp
      constructor
      · exact hh
      · rw [List.pairwise_cons] at hs
        have := fun c h' => TransCmp.lt_trans (c := c) hh h' ; grind
    · grind   -- impossible
    · exists (h :: pre), suf ; subst heq ; simp [heq']
      split_ands <;> try assumption
      exact OrientedCmp.lt_of_gt hh

theorem sortedInsertNoDup_mem [LawfulEqOrd α] (a x : α) (l : List α) :
    x ∈ sortedInsertNoDup a l ↔ x = a ∨ x ∈ l := by
  induction l with
  | nil => simp [sortedInsertNoDup]
  | cons h t ih => simp only [sortedInsertNoDup] ; grind

theorem sortedInsertNoDup_sorted [TransOrd α] [LawfulEqOrd α] (a : α) (l : List α)
    (hs : l.Pairwise (cmpLt (α := α))) :
    (sortedInsertNoDup a l).Pairwise (cmpLt (α := α)) := by
  by_cases h : a ∈ l
  · rw [sortedInsertNoDup_intact_if_in hs h] ; assumption
  · have htmp := sortedInsertNoDup_new_in hs h ; rcases htmp with ⟨pre, suf, heq, heq', hpre, hsuf⟩
    subst l ; rw [heq'] ; clear heq'
    rw [List.pairwise_append] at hs ⊢ ; simp [List.pairwise_cons]
    grind

theorem sortedInsertNoDup_contains_self [TransOrd α] [LawfulEqOrd α] (a : α) (l : List α)
    (hs : l.Pairwise (cmpLt (α := α))) :
    sortedContains a (sortedInsertNoDup a l) = true :=
  (sortedContains_iff _ _ (sortedInsertNoDup_sorted a l hs)).mpr
    ((sortedInsertNoDup_mem a a l).mpr (Or.inl rfl))

theorem sortedInsertNoDup_contains_other [TransOrd α] [LawfulEqOrd α] (a b : α) (l : List α)
    (hne : a ≠ b) (hs : l.Pairwise (cmpLt (α := α))) :
    sortedContains a (sortedInsertNoDup b l) = sortedContains a l := by
  rw [Bool.eq_iff_iff, sortedContains_iff, sortedContains_iff, sortedInsertNoDup_mem]
  all_goals try grind
  apply sortedInsertNoDup_sorted ; assumption

theorem sortedInsertNoDup_idempotent [TransOrd α] [LawfulEqOrd α] (a : α) (l : List α)
    (hs : l.Pairwise (cmpLt (α := α))) :
    sortedInsertNoDup a (sortedInsertNoDup a l) = sortedInsertNoDup a l := by
  apply sorted_unique <;> try solve | grind [sortedInsertNoDup_sorted]
  simp [sortedInsertNoDup_mem]

theorem sortedInsertNoDup_length [TransOrd α] [LawfulEqOrd α] (a : α) (l : List α)
    (hs : l.Pairwise (cmpLt (α := α))) :
    (sortedInsertNoDup a l).length = if sortedContains a l then l.length else l.length + 1 := by
  split_ifs with h
  all_goals rw [sortedContains_iff _ _ hs] at h
  · grind [sortedInsertNoDup_intact_if_in]
  · have htmp := sortedInsertNoDup_new_in hs h ; grind

/-! ### `sortedRemove` -/

theorem sortedRemove_intact_if_notin [TransOrd α] [LawfulEqOrd α] {a : α} {l : List α} (hs : l.Pairwise (cmpLt (α := α)))
    (hmem : a ∉ l) :
    sortedRemove a l = l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp at hmem ; rcases hmem with ⟨hneq, hmem⟩
    specialize ih (List.Pairwise.of_cons hs) hmem
    simp only [sortedRemove, ih] ; grind

theorem sortedRemove_remove [TransOrd α] [LawfulEqOrd α] {a : α} {l : List α} (hs : l.Pairwise (cmpLt (α := α)))
    (hmem : a ∈ l) :
    ∃ pre suf, l = pre ++ (a :: suf) ∧ sortedRemove a l = pre ++ suf := by
  induction l with
  | nil => simp at *
  | cons h t ih =>
    simp at hmem ; rcases hmem with hmem | hmem
    · subst h ; exists [], t ; simp [sortedRemove]
    · specialize ih (List.Pairwise.of_cons hs) hmem ; rcases ih with ⟨pre, suf, heq, heq'⟩
      subst t ; exists (h :: pre) , suf ; simp [sortedRemove, heq']
      rw [List.pairwise_cons] at hs ; have := OrientedCmp.gt_of_lt (hs.left _ hmem) ; grind

theorem sortedRemove_sorted [TransOrd α] [LawfulEqOrd α] (a : α) (l : List α)
    (hs : l.Pairwise (cmpLt (α := α))) :
    (sortedRemove a l).Pairwise (cmpLt (α := α)) := by
  by_cases h : a ∈ l
  · have htmp := sortedRemove_remove hs h ; rcases htmp with ⟨pre, suf, heq, heq'⟩
    grind
  · grind [sortedRemove_intact_if_notin]

theorem sortedRemove_contains_self [TransOrd α] [LawfulEqOrd α] (a : α) (l : List α)
    (hs : l.Pairwise (cmpLt (α := α))) :
    sortedContains a (sortedRemove a l) = false := by
  simp only [Bool.eq_false_iff, Ne] ; rw [sortedContains_iff _ _ (sortedRemove_sorted a l hs)]
  by_cases h : a ∈ l
  · have htmp := sortedRemove_remove hs h ; rcases htmp with ⟨pre, suf, heq, heq'⟩
    have := sorted_nodup hs ; grind
  · grind [sortedRemove_intact_if_notin]

-- theorem sortedRemove_mem_ne [TransOrd α] [LawfulEqOrd α] (a b : α) (l : List α)
--     (hne : a ≠ b) (hmem : a ∈ l) :
--     a ∈ sortedRemove b l := by
--   by_cases h : b ∈ l
--   · have htmp := sortedRemove_remove hs h ; rcases htmp with ⟨pre, suf, heq, heq'⟩
--     subst l ; simp [heq']
--     rw [List.pairwise_append] at hs ; simp at hs
--     have := OrientedCmp.gt_of_lt (hs.left _ h) ; grind

theorem sortedRemove_contains_other [TransOrd α] [LawfulEqOrd α] (a b : α) (l : List α)
    (hne : a ≠ b) (hs : l.Pairwise (cmpLt (α := α))) :
    sortedContains a (sortedRemove b l) = sortedContains a l := by
  rw [Bool.eq_iff_iff, sortedContains_iff _ _ (sortedRemove_sorted b l hs), sortedContains_iff _ _ hs]
  by_cases h : b ∈ l
  · have ⟨pre, suf, heq, heq'⟩ := sortedRemove_remove hs h
    have := sorted_nodup hs ; subst l ; grind
  · grind [sortedRemove_intact_if_notin]

theorem sortedRemove_length [TransOrd α] [LawfulEqOrd α] (a : α) (l : List α)
    (hs : l.Pairwise (cmpLt (α := α))) :
    (sortedRemove a l).length =
      if sortedContains a l then l.length - 1 else l.length := by
  split_ifs with h
  all_goals rw [sortedContains_iff _ _ hs] at h
  · have ⟨pre, suf, heq, heq'⟩ := sortedRemove_remove hs h ; grind
  · grind [sortedRemove_intact_if_notin]

/-! ### `sortedMergeNoDup` -/

theorem sortedMergeNoDup_mem [TransOrd α] [LawfulEqOrd α] (x : α) (l₁ l₂ : List α) :
    x ∈ sortedMergeNoDup l₁ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂ := by
  induction l₁, l₂ using sortedMergeNoDup.induct (α := α) with
  | case1 r => simp [sortedMergeNoDup]
  | case2 l hl => simp [sortedMergeNoDup_nil_right]
  | case3 a l' b r' hlt ih =>
    simp only [sortedMergeNoDup, hlt, List.mem_cons, ih] ; tauto
  | case4 a l' b r' heq ih =>
    simp only [sortedMergeNoDup, heq, List.mem_cons, ih]
    have := LawfulEqOrd.eq_of_compare heq ; subst this ; tauto
  | case5 a l' b r' hgt ih =>
    simp only [sortedMergeNoDup, hgt, List.mem_cons, ih] ; tauto

theorem sortedMergeNoDup_sorted [TransOrd α] [LawfulEqOrd α] (l₁ l₂ : List α)
    (hs₁ : l₁.Pairwise (cmpLt (α := α))) (hs₂ : l₂.Pairwise (cmpLt (α := α))) :
    (sortedMergeNoDup l₁ l₂).Pairwise (cmpLt (α := α)) := by
  induction l₁, l₂ using sortedMergeNoDup.induct (α := α) with
  | case1 r => simp only [sortedMergeNoDup] ; exact hs₂
  | case2 l hl => rwa [sortedMergeNoDup_nil_right]
  | case3 a l' b r' hlt ih =>
    simp only [sortedMergeNoDup, hlt]
    exact List.pairwise_cons.mpr ⟨fun x hx => by
      rw [sortedMergeNoDup_mem] at hx
      cases hx with
      | inl hx => exact List.rel_of_pairwise_cons hs₁ hx
      | inr hx =>
        cases List.mem_cons.mp hx with
        | inl heq =>
          subst heq ; exact hlt
        | inr hmem =>
          exact TransCmp.lt_trans hlt (List.rel_of_pairwise_cons hs₂ hmem),
      ih (List.Pairwise.of_cons hs₁) hs₂⟩
  | case4 a l' b r' heq ih =>
    simp only [sortedMergeNoDup, heq]
    have hab := LawfulEqOrd.eq_of_compare heq
    exact List.pairwise_cons.mpr ⟨fun x hx => by
      rw [sortedMergeNoDup_mem] at hx
      cases hx with
      | inl hx => exact List.rel_of_pairwise_cons hs₁ hx
      | inr hx =>
        rw [hab] ; exact List.rel_of_pairwise_cons hs₂ hx,
      ih (List.Pairwise.of_cons hs₁) (List.Pairwise.of_cons hs₂)⟩
  | case5 a l' b r' hgt ih =>
    simp only [sortedMergeNoDup, hgt]
    exact List.pairwise_cons.mpr ⟨fun x hx => by
      rw [sortedMergeNoDup_mem] at hx
      cases hx with
      | inl hx =>
        cases List.mem_cons.mp hx with
        | inl heq =>
          subst heq ; exact OrientedCmp.lt_of_gt hgt
        | inr hmem =>
          exact TransCmp.lt_trans (OrientedCmp.lt_of_gt hgt) (List.rel_of_pairwise_cons hs₁ hmem)
      | inr hx => exact List.rel_of_pairwise_cons hs₂ hx,
      ih hs₁ (List.Pairwise.of_cons hs₂)⟩

theorem sortedMergeNoDup_contains [TransOrd α] [LawfulEqOrd α] (a : α) (l₁ l₂ : List α)
    (hs₁ : l₁.Pairwise (cmpLt (α := α))) (hs₂ : l₂.Pairwise (cmpLt (α := α))) :
    sortedContains a (sortedMergeNoDup l₁ l₂) =
      (sortedContains a l₁ || sortedContains a l₂) := by
  have hs := sortedMergeNoDup_sorted l₁ l₂ hs₁ hs₂
  cases h1 : sortedContains a l₁ <;> cases h2 : sortedContains a l₂ <;> simp
  · rw [Bool.eq_false_iff]
    intro hr
    rw [sortedContains_iff _ _ hs, sortedMergeNoDup_mem] at hr
    cases hr with
    | inl h => exact absurd ((sortedContains_iff _ _ hs₁).mpr h) (by rw [h1] ; decide)
    | inr h => exact absurd ((sortedContains_iff _ _ hs₂).mpr h) (by rw [h2] ; decide)
  · exact (sortedContains_iff _ _ hs).mpr
      ((sortedMergeNoDup_mem _ _ _).mpr (Or.inr ((sortedContains_iff _ _ hs₂).mp h2)))
  · exact (sortedContains_iff _ _ hs).mpr
      ((sortedMergeNoDup_mem _ _ _).mpr (Or.inl ((sortedContains_iff _ _ hs₁).mp h1)))
  · exact (sortedContains_iff _ _ hs).mpr
      ((sortedMergeNoDup_mem _ _ _).mpr (Or.inl ((sortedContains_iff _ _ hs₁).mp h1)))

/-! ### `sortedDiffNoDup` -/

theorem sortedDiffNoDup_sub (x : α) (l₁ l₂ : List α) :
    x ∈ sortedDiffNoDup l₁ l₂ → x ∈ l₁ := by
  induction l₁, l₂ using sortedDiffNoDup.induct (α := α) with
  | case1 r => simp [sortedDiffNoDup]
  | case2 l hl => simp [sortedDiffNoDup_nil_right]
  | case3 a l' b r' hlt ih =>
    simp only [sortedDiffNoDup, hlt, List.mem_cons] ; tauto
  | case4 a l' b r' heq ih =>
    simp only [sortedDiffNoDup, heq, List.mem_cons] ; tauto
  | case5 a l' b r' hgt ih =>
    simp only [sortedDiffNoDup, hgt] ; exact ih

theorem sortedDiffNoDup_sorted [TransOrd α] [LawfulEqOrd α] (l₁ l₂ : List α)
    (hs₁ : l₁.Pairwise (cmpLt (α := α))) (hs₂ : l₂.Pairwise (cmpLt (α := α))) :
    (sortedDiffNoDup l₁ l₂).Pairwise (cmpLt (α := α)) := by
  induction l₁, l₂ using sortedDiffNoDup.induct (α := α) with
  | case1 r => simp [sortedDiffNoDup]
  | case2 l hl => rwa [sortedDiffNoDup_nil_right]
  | case3 a l' b r' hlt ih =>
    simp only [sortedDiffNoDup, hlt]
    exact List.pairwise_cons.mpr ⟨fun x hx =>
      List.rel_of_pairwise_cons hs₁ (sortedDiffNoDup_sub x l' (b :: r') hx),
      ih (List.Pairwise.of_cons hs₁) hs₂⟩
  | case4 a l' b r' heq ih =>
    simp only [sortedDiffNoDup, heq]
    exact ih (List.Pairwise.of_cons hs₁) (List.Pairwise.of_cons hs₂)
  | case5 a l' b r' hgt ih =>
    simp only [sortedDiffNoDup, hgt]
    exact ih hs₁ (List.Pairwise.of_cons hs₂)

theorem sortedDiffNoDup_mem [TransOrd α] [LawfulEqOrd α] (x : α) (l₁ l₂ : List α)
    (hs₁ : l₁.Pairwise (cmpLt (α := α))) (hs₂ : l₂.Pairwise (cmpLt (α := α))) :
    x ∈ sortedDiffNoDup l₁ l₂ ↔ x ∈ l₁ ∧ x ∉ l₂ := by
  induction l₁, l₂ using sortedDiffNoDup.induct (α := α) with
  | case1 r => simp [sortedDiffNoDup]
  | case2 l hl => simp [sortedDiffNoDup_nil_right]
  | case3 a l' b r' hlt ih =>
    simp only [sortedDiffNoDup, hlt, List.mem_cons,
      ih (List.Pairwise.of_cons hs₁) hs₂]
    have ha := mt List.mem_cons.mpr (not_mem_of_cmpLt_cons hlt hs₂)
    constructor
    · rintro (rfl | ⟨hm, hn⟩)
      · exact ⟨.inl rfl, ha⟩
      · exact ⟨.inr hm, hn⟩
    · rintro ⟨rfl | hm, hn⟩
      · exact .inl rfl
      · exact .inr ⟨hm, hn⟩
  | case4 a l' b r' heq ih =>
    simp only [sortedDiffNoDup, heq, List.mem_cons,
      ih (List.Pairwise.of_cons hs₁) (List.Pairwise.of_cons hs₂)]
    have hab := LawfulEqOrd.eq_of_compare heq ; subst hab
    constructor
    · intro ⟨hm, hn⟩ ; refine ⟨.inr hm, fun h => ?_⟩ ; rcases h with rfl | h
      · exact absurd (List.rel_of_pairwise_cons hs₁ hm) (by simp [cmpLt, ReflOrd.compare_self])
      · exact hn h
    · intro ⟨hm, hn⟩
      exact ⟨hm.resolve_left (fun h => hn (.inl h)), fun h => hn (.inr h)⟩
  | case5 a l' b r' hgt ih =>
    simp only [sortedDiffNoDup, hgt, List.mem_cons,
      ih hs₁ (List.Pairwise.of_cons hs₂)]
    have hb := mt List.mem_cons.mpr (not_mem_of_cmpGt_cons hgt hs₁)
    constructor
    · intro ⟨hm, hn⟩ ; refine ⟨hm, fun h => ?_⟩ ; rcases h with rfl | h
      · exact hb hm
      · exact hn h
    · intro ⟨hm, hn⟩ ; exact ⟨hm, fun h => hn (.inr h)⟩

theorem sortedDiffNoDup_contains [TransOrd α] [LawfulEqOrd α] (a : α) (l₁ l₂ : List α)
    (hs₁ : l₁.Pairwise (cmpLt (α := α))) (hs₂ : l₂.Pairwise (cmpLt (α := α))) :
    sortedContains a (sortedDiffNoDup l₁ l₂) =
      (sortedContains a l₁ && !sortedContains a l₂) := by
  have hs := sortedDiffNoDup_sorted l₁ l₂ hs₁ hs₂
  cases h1 : sortedContains a l₁ <;> cases h2 : sortedContains a l₂ <;> simp
  · rw [Bool.eq_false_iff] ; intro hr
    rw [sortedContains_iff _ _ hs, sortedDiffNoDup_mem _ _ _ hs₁ hs₂] at hr
    exact absurd ((sortedContains_iff _ _ hs₁).mpr hr.1) (by rw [h1] ; decide)
  · rw [Bool.eq_false_iff] ; intro hr
    rw [sortedContains_iff _ _ hs, sortedDiffNoDup_mem _ _ _ hs₁ hs₂] at hr
    exact absurd ((sortedContains_iff _ _ hs₁).mpr hr.1) (by rw [h1] ; decide)
  · exact (sortedContains_iff _ _ hs).mpr
      ((sortedDiffNoDup_mem _ _ _ hs₁ hs₂).mpr
        ⟨(sortedContains_iff _ _ hs₁).mp h1,
         fun hm => absurd ((sortedContains_iff _ _ hs₂).mpr hm) (by rw [h2] ; decide)⟩)
  · rw [Bool.eq_false_iff] ; intro hr
    rw [sortedContains_iff _ _ hs, sortedDiffNoDup_mem _ _ _ hs₁ hs₂] at hr
    exact hr.2 ((sortedContains_iff _ _ hs₂).mp h2)

/-! ### `sortedIntersectNoDup` -/

theorem sortedIntersectNoDup_sub (x : α) (l₁ l₂ : List α) :
    x ∈ sortedIntersectNoDup l₁ l₂ → x ∈ l₁ := by
  induction l₁, l₂ using sortedIntersectNoDup.induct (α := α) with
  | case1 r => simp [sortedIntersectNoDup]
  | case2 l hl => simp [sortedIntersectNoDup_nil_right]
  | case3 a l' b r' hlt ih =>
    simp only [sortedIntersectNoDup, hlt, List.mem_cons] ; tauto
  | case4 a l' b r' heq ih =>
    simp only [sortedIntersectNoDup, heq, List.mem_cons] ; tauto
  | case5 a l' b r' hgt ih =>
    simp only [sortedIntersectNoDup, hgt] ; exact ih

theorem sortedIntersectNoDup_sorted [TransOrd α] [LawfulEqOrd α] (l₁ l₂ : List α)
    (hs₁ : l₁.Pairwise (cmpLt (α := α))) (hs₂ : l₂.Pairwise (cmpLt (α := α))) :
    (sortedIntersectNoDup l₁ l₂).Pairwise (cmpLt (α := α)) := by
  induction l₁, l₂ using sortedIntersectNoDup.induct (α := α) with
  | case1 r => simp [sortedIntersectNoDup]
  | case2 l hl => rw [sortedIntersectNoDup_nil_right] ; exact List.Pairwise.nil
  | case3 a l' b r' hlt ih =>
    simp only [sortedIntersectNoDup, hlt]
    exact ih (List.Pairwise.of_cons hs₁) hs₂
  | case4 a l' b r' heq ih =>
    simp only [sortedIntersectNoDup, heq]
    exact List.pairwise_cons.mpr ⟨fun x hx =>
      List.rel_of_pairwise_cons hs₁ (sortedIntersectNoDup_sub x l' r' hx),
      ih (List.Pairwise.of_cons hs₁) (List.Pairwise.of_cons hs₂)⟩
  | case5 a l' b r' hgt ih =>
    simp only [sortedIntersectNoDup, hgt]
    exact ih hs₁ (List.Pairwise.of_cons hs₂)

theorem sortedIntersectNoDup_mem [TransOrd α] [LawfulEqOrd α] (x : α) (l₁ l₂ : List α)
    (hs₁ : l₁.Pairwise (cmpLt (α := α))) (hs₂ : l₂.Pairwise (cmpLt (α := α))) :
    x ∈ sortedIntersectNoDup l₁ l₂ ↔ x ∈ l₁ ∧ x ∈ l₂ := by
  induction l₁, l₂ using sortedIntersectNoDup.induct (α := α) with
  | case1 r => simp [sortedIntersectNoDup]
  | case2 l hl => simp [sortedIntersectNoDup_nil_right]
  | case3 a l' b r' hlt ih =>
    simp only [sortedIntersectNoDup, hlt]
    have hs₁' := List.Pairwise.of_cons hs₁
    constructor
    · intro hm
      have ⟨hm₁, hm₂⟩ := (ih hs₁' hs₂).mp hm
      exact ⟨List.mem_cons.mpr (Or.inr hm₁), hm₂⟩
    · intro ⟨hm₁, hm₂⟩
      cases List.mem_cons.mp hm₁ with
      | inl h =>
        subst h ; exfalso
        cases List.mem_cons.mp hm₂ with
        | inl h => rw [h] at hlt ; simp [ReflOrd.compare_self] at hlt
        | inr h =>
          have := List.rel_of_pairwise_cons hs₂ h
          have := OrientedCmp.gt_of_lt hlt
          simp_all
      | inr h => exact (ih hs₁' hs₂).mpr ⟨h, hm₂⟩
  | case4 a l' b r' heq ih =>
    simp only [sortedIntersectNoDup, heq]
    have hab := LawfulEqOrd.eq_of_compare heq
    have hs₁' := List.Pairwise.of_cons hs₁
    have hs₂' := List.Pairwise.of_cons hs₂
    constructor
    · intro hm
      cases List.mem_cons.mp hm with
      | inl h =>
        subst h ; exact ⟨List.mem_cons.mpr (Or.inl rfl), List.mem_cons.mpr (Or.inl hab)⟩
      | inr h =>
        have ⟨hm₁, hm₂⟩ := (ih hs₁' hs₂').mp h
        exact ⟨List.mem_cons.mpr (Or.inr hm₁), List.mem_cons.mpr (Or.inr hm₂)⟩
    · intro ⟨hm₁, hm₂⟩
      cases List.mem_cons.mp hm₁ with
      | inl h =>
        subst h ; exact List.mem_cons.mpr (Or.inl rfl)
      | inr h₁ =>
        cases List.mem_cons.mp hm₂ with
        | inl h₂ =>
          subst h₂ ; rw [← hab] at h₁
          exact absurd (List.rel_of_pairwise_cons hs₁ h₁) (by simp [cmpLt, ReflOrd.compare_self])
        | inr h₂ => exact List.mem_cons.mpr (Or.inr ((ih hs₁' hs₂').mpr ⟨h₁, h₂⟩))
  | case5 a l' b r' hgt ih =>
    simp only [sortedIntersectNoDup, hgt]
    have hs₂' := List.Pairwise.of_cons hs₂
    constructor
    · intro hm
      have ⟨hm₁, hm₂⟩ := (ih hs₁ hs₂').mp hm
      exact ⟨hm₁, List.mem_cons.mpr (Or.inr hm₂)⟩
    · intro ⟨hm₁, hm₂⟩
      cases List.mem_cons.mp hm₂ with
      | inl h =>
        subst h ; exfalso
        cases List.mem_cons.mp hm₁ with
        | inl h => rw [h] at hgt ; simp [ReflOrd.compare_self] at hgt
        | inr h =>
          have := List.rel_of_pairwise_cons hs₁ h
          simp [this] at hgt
      | inr h => exact (ih hs₁ hs₂').mpr ⟨hm₁, h⟩

theorem sortedIntersectNoDup_contains [TransOrd α] [LawfulEqOrd α] (a : α) (l₁ l₂ : List α)
    (hs₁ : l₁.Pairwise (cmpLt (α := α))) (hs₂ : l₂.Pairwise (cmpLt (α := α))) :
    sortedContains a (sortedIntersectNoDup l₁ l₂) =
      (sortedContains a l₁ && sortedContains a l₂) := by
  have hs := sortedIntersectNoDup_sorted l₁ l₂ hs₁ hs₂
  cases h1 : sortedContains a l₁ <;> cases h2 : sortedContains a l₂ <;> simp
  · rw [Bool.eq_false_iff] ; intro hr
    rw [sortedContains_iff _ _ hs, sortedIntersectNoDup_mem _ _ _ hs₁ hs₂] at hr
    exact absurd ((sortedContains_iff _ _ hs₁).mpr hr.1) (by rw [h1] ; decide)
  · rw [Bool.eq_false_iff] ; intro hr
    rw [sortedContains_iff _ _ hs, sortedIntersectNoDup_mem _ _ _ hs₁ hs₂] at hr
    exact absurd ((sortedContains_iff _ _ hs₁).mpr hr.1) (by rw [h1] ; decide)
  · rw [Bool.eq_false_iff] ; intro hr
    rw [sortedContains_iff _ _ hs, sortedIntersectNoDup_mem _ _ _ hs₁ hs₂] at hr
    exact absurd ((sortedContains_iff _ _ hs₂).mpr hr.2) (by rw [h2] ; decide)
  · exact (sortedContains_iff _ _ hs).mpr
      ((sortedIntersectNoDup_mem _ _ _ hs₁ hs₂).mpr
        ⟨(sortedContains_iff _ _ hs₁).mp h1, (sortedContains_iff _ _ hs₂).mp h2⟩)

/-! ### Filter lemmas -/

theorem sorted_filter (l : List α) (p : α → Bool)
    (hs : l.Pairwise (cmpLt (α := α))) :
    (l.filter p).Pairwise (cmpLt (α := α)) :=
  List.Pairwise.filter _ hs

theorem filter_sortedContains_diff [TransOrd α] [LawfulEqOrd α] (a : α) (l₁ l₂ : List α)
    (hs₁ : l₁.Pairwise (cmpLt (α := α))) (_hs₂ : l₂.Pairwise (cmpLt (α := α))) :
    sortedContains a (l₁.filter (fun x => !sortedContains x l₂)) =
      (sortedContains a l₁ && !sortedContains a l₂) := by
  have hsf := sorted_filter l₁ (fun x => !sortedContains x l₂) hs₁
  cases h1 : sortedContains a l₁ <;> cases h2 : sortedContains a l₂ <;> simp
  · rw [Bool.eq_false_iff] ; intro hr
    rw [sortedContains_iff _ _ hsf, List.mem_filter] at hr
    exact absurd ((sortedContains_iff _ _ hs₁).mpr hr.1) (by rw [h1] ; decide)
  · rw [Bool.eq_false_iff] ; intro hr
    rw [sortedContains_iff _ _ hsf, List.mem_filter] at hr
    exact absurd ((sortedContains_iff _ _ hs₁).mpr hr.1) (by rw [h1] ; decide)
  · rw [sortedContains_iff _ _ hsf, List.mem_filter]
    exact ⟨(sortedContains_iff _ _ hs₁).mp h1, by rw [h2] ; decide⟩
  · rw [Bool.eq_false_iff] ; intro hr
    rw [sortedContains_iff _ _ hsf, List.mem_filter] at hr
    exact absurd hr.2 (by simp [h2])

theorem filter_sortedContains_inter [TransOrd α] [LawfulEqOrd α] (a : α) (l₁ l₂ : List α)
    (hs₁ : l₁.Pairwise (cmpLt (α := α))) (_hs₂ : l₂.Pairwise (cmpLt (α := α))) :
    sortedContains a (l₁.filter (fun x => sortedContains x l₂)) =
      (sortedContains a l₁ && sortedContains a l₂) := by
  have hsf := sorted_filter l₁ (fun x => sortedContains x l₂) hs₁
  cases h1 : sortedContains a l₁ <;> cases h2 : sortedContains a l₂ <;> simp
  · rw [Bool.eq_false_iff] ; intro hr
    rw [sortedContains_iff _ _ hsf, List.mem_filter] at hr
    exact absurd ((sortedContains_iff _ _ hs₁).mpr hr.1) (by rw [h1] ; decide)
  · rw [Bool.eq_false_iff] ; intro hr
    rw [sortedContains_iff _ _ hsf, List.mem_filter] at hr
    exact absurd ((sortedContains_iff _ _ hs₁).mpr hr.1) (by rw [h1] ; decide)
  · rw [Bool.eq_false_iff] ; intro hr
    rw [sortedContains_iff _ _ hsf, List.mem_filter] at hr
    exact absurd hr.2 (by rw [h2] ; decide)
  · rw [sortedContains_iff _ _ hsf, List.mem_filter]
    exact ⟨(sortedContains_iff _ _ hs₁).mp h1, h2⟩

/-! ### Sublists lemmas -/

private theorem sublists_all_sorted [TransOrd α] [LawfulEqOrd α] (l : List α) (hs : l.Pairwise (cmpLt (α := α))) :
  ∀ sl ∈ l.sublists, sl.Pairwise (cmpLt (α := α)) := by intro sl hin ; simp at hin ; apply hs.sublist hin

@[inline]
def sublists [TransOrd α] [LawfulEqOrd α] (l : OrdList α) : List (OrdList α) :=
  l.val.sublists.attachWith _ (sublists_all_sorted l.val l.property)

-- TODO check these instances later?

scoped instance cmpLt_irrefl [TransOrd α] [OrientedOrd α] :
    Std.Irrefl (cmpLt (α := α)) where
  irrefl a h := by simp [cmpLt, ReflOrd.compare_self] at h

scoped instance cmpLt_antisymm [TransOrd α] [OrientedOrd α] :
    Std.Antisymm (cmpLt (α := α)) where
  antisymm {a} {b} hab hba := by
    exact absurd (TransCmp.lt_trans hab hba) (by simp [ReflOrd.compare_self])

theorem mem_contains_then_is_sublist [TransOrd α] [LawfulEqOrd α] (l1 l2 : List α)
  (hs1 : l1.Pairwise (cmpLt (α := α))) (hs2 : l2.Pairwise (cmpLt (α := α)))
  (h : ∀ x, x ∈ l1 → x ∈ l2) : l1.Sublist l2 := by
  apply @List.sublist_of_subperm_of_pairwise _ _ (cmpLt_antisymm (α := α))
  · apply List.subperm_of_subset (sorted_nodup hs1)
    grind
  · grind
  · grind

/-
/-! ### Foldl insert lemmas -/

theorem foldl_sortedInsertNoDup_sorted [TransOrd α] [LawfulEqOrd α]
    (l : List α) (acc : List α) (hacc : acc.Pairwise (cmpLt (α := α))) :
    (l.foldl (fun acc a => sortedInsertNoDup a acc) acc).Pairwise (cmpLt (α := α)) := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons h t ih =>
    simp only [List.foldl_cons]
    exact ih (sortedInsertNoDup h acc) (sortedInsertNoDup_sorted h acc hacc)

theorem foldl_sortedInsertNoDup_mem [TransOrd α] [LawfulEqOrd α]
    (l : List α) (acc : List α) (x : α) :
    x ∈ l.foldl (fun acc a => sortedInsertNoDup a acc) acc ↔ x ∈ acc ∨ x ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, ih, sortedInsertNoDup_mem, List.mem_cons] ; tauto
-/

end SortedLemmas

/-! ## Type definitions and instances -/

section Instances

variable {α : Type u} [Ord α]

/-! ### Inhabited -/

instance : Inhabited (OrdList α) where
  default := ⟨[], List.Pairwise.nil⟩

/-! ### Repr and ToJson -/

instance [Repr α] : Repr (OrdList α) where
  reprPrec s p := reprPrec s.val p

instance [Repr α] : Lean.ToJson (OrdList α) where
  toJson s := Lean.ToJson.toJson s.val

/-! ### Ordering instances -/

instance [Std.ReflOrd α] : Std.ReflOrd (OrdList α) where
  compare_self := Std.ReflOrd.compare_self (α := List α)

instance [Std.LawfulEqOrd α] : Std.LawfulEqOrd (OrdList α) where
  eq_of_compare h := Subtype.ext (Std.LawfulEqOrd.eq_of_compare (α := List α) h)

instance [Std.OrientedOrd α] : Std.OrientedOrd (OrdList α) where
  eq_swap := Std.OrientedOrd.eq_swap (α := List α)

instance [Std.TransOrd α] : Std.TransOrd (OrdList α) where
  isLE_trans h1 h2 := Std.TransOrd.isLE_trans (α := List α) h1 h2

/-! ### Enumeration -/

instance instEnumerationOrdList [TransOrd α] [LawfulEqOrd α] [DecidableEq α] [Veil.Enumeration α]
    : Veil.Enumeration (OrdList α) where
  allValues :=
    OrdList.ofList (Veil.Enumeration.allValues (α := α)) |>.sublists
  complete := by
    intro ⟨l, hl⟩
    simp [OrdList.ofList, OrdList.sublists, List.mem_attachWith]
    have h_sorted : (ofList.inner (Veil.Enumeration.allValues (α := α))).Pairwise (cmpLt (α := α)) :=
      (ofList.inner_spec _).left
    apply mem_contains_then_is_sublist <;> try assumption
    intros ; simp [ofList.inner_spec, Veil.Enumeration.complete]

end Instances
