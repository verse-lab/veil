import Std
import Batteries.Data.Array.Merge
import Batteries.Data.Array.Pairwise
import Veil.Frontend.DSL.State.Types
import Veil.Frontend.DSL.State.Instances
import Veil.Util.SortedList

/-! # Sorted Array

This file provides `OrdArray`, a sorted array container backed by `Array`,
together with efficient operations and the lemmas required to instantiate `TSet`.
-/

namespace Array

section binSearchAuxProofs

variable {α : Type u} {β : Type v} {lt : α → α → Bool} {as : Array α} {k : α}
  {lo : Fin (as.size + 1)} {hi : Fin as.size} {h : lo.1 ≤ hi.1}

set_option maxHeartbeats 800000 in
include h in
theorem binSearchAux_found_continuation :
  as.binSearchAux lt found k lo hi h = found (as.binSearchAux lt id k lo hi h) := by
  induction lo, hi, h using binSearchAux.induct lt as k with
  | case1 lo hi h _m _a hlt hm _ ih =>
    show binSearchAux lt found as k lo hi h = _
    rw [binSearchAux.eq_1]; rw [if_pos hlt, dif_pos hm]
    show binSearchAux lt found as k ⟨_m + 1, _⟩ hi hm = found (binSearchAux lt id as k lo hi h)
    rw [show binSearchAux lt id as k lo hi h = binSearchAux lt id as k ⟨_m + 1, _⟩ hi hm from by
      rw [binSearchAux.eq_1]; rw [if_pos hlt, dif_pos hm]]
    exact ih
  | case2 lo hi h _m _a hlt hm _ =>
    show binSearchAux lt found as k lo hi h = _
    rw [binSearchAux.eq_1]; rw [if_pos hlt, dif_neg hm]
    show found none = found (binSearchAux lt id as k lo hi h)
    congr 1; rw [binSearchAux.eq_1]; simp only [id_eq]; rw [if_pos hlt, dif_neg hm]
  | case3 lo hi h _m _a hlt hltk hm _ =>
    show binSearchAux lt found as k lo hi h = _
    rw [binSearchAux.eq_1]; rw [if_neg hlt, if_pos hltk, dif_pos hm]
    show found none = found (binSearchAux lt id as k lo hi h)
    congr 1; rw [binSearchAux.eq_1]; simp only [id_eq]; rw [if_neg hlt, if_pos hltk, dif_pos hm]
  | case4 lo hi h _m _a hlt hltk hm _ ih =>
    show binSearchAux lt found as k lo hi h = _
    rw [binSearchAux.eq_1]; rw [if_neg hlt, if_pos hltk, dif_neg hm]
    show binSearchAux lt found as k lo ⟨_m - 1, _⟩ _ = found (binSearchAux lt id as k lo hi h)
    rw [show binSearchAux lt id as k lo hi h = binSearchAux lt id as k lo ⟨_m - 1, _⟩ _ from by
      rw [binSearchAux.eq_1]; rw [if_neg hlt, if_pos hltk, dif_neg hm]]
    exact ih
  | case5 lo hi h _m _a hlt hltk _ =>
    show binSearchAux lt found as k lo hi h = _
    rw [binSearchAux.eq_1]; rw [if_neg hlt, if_neg hltk]
    show found (some _a) = found (binSearchAux lt id as k lo hi h)
    congr 1; rw [binSearchAux.eq_1]; simp only [id_eq]; rw [if_neg hlt, if_neg hltk]

set_option maxHeartbeats 1600000 in
include h in
theorem binSearchAux_some_then_found :
  as.binSearchAux lt id k lo hi h = some a →
    ∃ i : Fin as.size, lo.val ≤ i.val ∧ i ≤ hi ∧ as[i] = a ∧ lt k a = false ∧ lt a k = false := by
  induction lo, hi, h using binSearchAux.induct lt as k with
  | case1 lo hi h _m _a hlt hm _ ih =>
    show binSearchAux lt id as k lo hi h = some a → _
    rw [binSearchAux.eq_1, id_eq, if_pos hlt, dif_pos hm]
    intro heq
    obtain ⟨i, hli, hri, heqi, hltk, hlta⟩ := ih heq
    refine ⟨i, ?_, hri, heqi, hltk, hlta⟩
    show lo.val ≤ i.val
    have hm_def : _m = (lo.val + hi.val) / 2 := rfl
    have hli_nat : _m + 1 ≤ i.val := hli
    omega
  | case2 lo hi h _m _a hlt hm _ =>
    show binSearchAux lt id as k lo hi h = some a → _
    rw [binSearchAux.eq_1, id_eq, if_pos hlt, dif_neg hm]
    intro heq; exact absurd heq (by simp)
  | case3 lo hi h _m _a hlt hltk hm _ =>
    show binSearchAux lt id as k lo hi h = some a → _
    rw [binSearchAux.eq_1, id_eq, if_neg hlt, if_pos hltk, dif_pos hm]
    intro heq; exact absurd heq (by simp)
  | case4 lo hi h _m _a hlt hltk hm _ ih =>
    show binSearchAux lt id as k lo hi h = some a → _
    rw [binSearchAux.eq_1, id_eq, if_neg hlt, if_pos hltk, dif_neg hm]
    intro heq
    obtain ⟨i, hli, hri, heqi, hltk', hlta⟩ := ih heq
    refine ⟨i, hli, ?_, heqi, hltk', hlta⟩
    show i.val ≤ hi.val
    have hm_def : _m = (lo.val + hi.val) / 2 := rfl
    have hri_nat : i.val ≤ _m - 1 := hri
    omega
  | case5 lo hi h _m _a hlt hltk _ =>
    show binSearchAux lt id as k lo hi h = some a → _
    rw [binSearchAux.eq_1, id_eq, if_neg hlt, if_neg hltk]
    intro heq
    have := Option.some.inj heq; subst this
    have hm_lt : _m < as.size := by omega
    refine ⟨⟨_m, hm_lt⟩, ?_, ?_, rfl, Bool.eq_false_iff.mpr hltk, Bool.eq_false_iff.mpr hlt⟩
    · dsimp ; omega
    · cases hi ; simp ; grind

set_option maxHeartbeats 1600000 in
include h in
theorem binSearchAux_none_then_not_found
    (htr : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hs : as.Pairwise (fun x y => lt x y = true)) :
  as.binSearchAux lt id k lo hi h = none →
    ∀ i : Fin as.size, lo.val ≤ i.val → i ≤ hi → lt (as[i]) k ∨ lt k (as[i]) := by
  have hpw := Array.pairwise_iff_getElem.mp hs
  induction lo, hi, h using binSearchAux.induct lt as k with
  | case1 lo hi h _m _a hlt hm _ ih =>
    show binSearchAux lt id as k lo hi h = none → _
    rw [binSearchAux.eq_1, id_eq, if_pos hlt, dif_pos hm]
    intro heq i hli hri
    by_cases hle : _m + 1 ≤ i.val
    · exact ih heq i hle hri
    · left
      show lt as[i.val] k = true
      by_cases hieqm : i.val = _m
      · simp only [hieqm]; exact hlt
      · have : i.val < _m := by omega
        exact htr _ _ _ (hpw i.val _m i.isLt (by omega) this) hlt
  | case2 lo hi h _m _a hlt hm _ =>
    intro _ i hli hri
    left; show lt as[i.val] k = true
    have : i.val = _m := by omega
    simp only [this]; exact hlt
  | case3 lo hi h _m _a hlt hltk hm _ =>
    intro _ i hli hri
    right; show lt k as[i.val] = true
    by_cases hieqm : i.val = _m
    · simp only [hieqm]; exact hltk
    · have : _m < i.val := by omega
      exact htr _ _ _ hltk (hpw _m i.val (by omega) i.isLt this)
  | case4 lo hi h _m _a hlt hltk hm _ ih =>
    show binSearchAux lt id as k lo hi h = none → _
    rw [binSearchAux.eq_1, id_eq, if_neg hlt, if_pos hltk, dif_neg hm]
    intro heq i hli hri
    by_cases hle : i.val ≤ _m - 1
    · exact ih heq i hli hle
    · right; show lt k as[i.val] = true
      by_cases hieqm : i.val = _m
      · simp only [hieqm]; exact hltk
      · have : _m < i.val := by omega
        exact htr _ _ _ hltk (hpw _m i.val (by omega) i.isLt this)
  | case5 lo hi h _m _a hlt hltk _ =>
    show binSearchAux lt id as k lo hi h = none → _
    rw [binSearchAux.eq_1, id_eq, if_neg hlt, if_neg hltk]
    intro heq; exact absurd heq (by simp)

end binSearchAuxProofs

section binSearchIdxProofs

/-- Just `binSearchContains` with `α` universe polymorphic. -/
@[inline] def binSearchContainsUP {α : Type u} (as : Array α) (k : α) (lt : α → α → Bool) (lo := 0) (hi := as.size - 1) : Bool :=
  if h : lo < as.size then
    let hi := if hi < as.size then hi else as.size - 1
    if w : lo ≤ hi then
      binSearchAux lt Option.isSome as k ⟨lo, by omega⟩ ⟨hi, by simp [hi]; split <;> omega⟩ (by simp [hi]; omega)
    else
      false
  else
    false

/-- Binary search returning the index of the found element, if any. -/
@[specialize] def binSearchIdxAux {α : Type u} (lt : α → α → Bool) (as : Array α) (k : α) :
    (lo : Fin (as.size + 1)) → (hi : Fin as.size) → (lo.1 ≤ hi.1) → Option (Fin as.size)
  | lo, hi, h =>
    let m := (lo.1 + hi.1) / 2
    let a := as[m]
    if lt a k then
      if h' : m + 1 ≤ hi.1 then
        binSearchIdxAux lt as k ⟨m+1, by omega⟩ hi h'
      else none
    else if lt k a then
      if h' : m = 0 ∨ m - 1 < lo.1 then none
      else binSearchIdxAux lt as k lo ⟨m-1, by omega⟩ (by simp; omega)
    else some ⟨m, by omega⟩
termination_by lo hi => hi.1 - lo.1

/-- O(log n) binary search returning the index. -/
@[inline] def binSearchIdx {α : Type u} (as : Array α) (k : α) (lt : α → α → Bool) :
    Option (Fin as.size) :=
  if h : 0 < as.size then
    binSearchIdxAux lt as k ⟨0, by omega⟩ ⟨as.size - 1, by omega⟩ (Nat.zero_le _)
  else none

variable {α : Type u} {lt : α → α → Bool} {as : Array α} {k : α}
  {lo : Fin (as.size + 1)} {hi : Fin as.size} {h : lo.1 ≤ hi.1}

set_option maxHeartbeats 800000 in
include h in
theorem binSearchIdxAux_some :
    binSearchIdxAux lt as k lo hi h = some i →
    lo.1 ≤ i.1 ∧ i.1 ≤ hi.1 ∧ lt as[i] k = false ∧ lt k as[i] = false := by
  induction lo, hi, h using binSearchIdxAux.induct lt as k with
  | case1 lo hi h _m _a hlt hm _ ih =>
    show binSearchIdxAux lt as k lo hi h = some i → _
    rw [binSearchIdxAux.eq_1, if_pos hlt, dif_pos hm]
    intro heq; obtain ⟨h1, h2, h3, h4⟩ := ih heq
    refine ⟨?_, h2, h3, h4⟩; show lo.1 ≤ i.1
    have hm_def : _m = (lo.1 + hi.1) / 2 := rfl
    have h1' : _m + 1 ≤ i.1 := h1; omega
  | case2 lo hi h _m _a hlt hm =>
    show binSearchIdxAux lt as k lo hi h = some i → _
    rw [binSearchIdxAux.eq_1, if_pos hlt, dif_neg hm]
    intro heq; exact absurd heq (by simp)
  | case3 lo hi h _m _a hlt hltk hm =>
    show binSearchIdxAux lt as k lo hi h = some i → _
    rw [binSearchIdxAux.eq_1, if_neg hlt, if_pos hltk, dif_pos hm]
    intro heq; exact absurd heq (by simp)
  | case4 lo hi h _m _a hlt hltk hm _ ih =>
    show binSearchIdxAux lt as k lo hi h = some i → _
    rw [binSearchIdxAux.eq_1, if_neg hlt, if_pos hltk, dif_neg hm]
    intro heq; obtain ⟨h1, h2, h3, h4⟩ := ih heq
    refine ⟨h1, ?_, h3, h4⟩; show i.1 ≤ hi.1
    have hm_def : _m = (lo.1 + hi.1) / 2 := rfl
    have h2' : i.1 ≤ _m - 1 := h2; omega
  | case5 lo hi h _m _a hlt hltk =>
    show binSearchIdxAux lt as k lo hi h = some i → _
    rw [binSearchIdxAux.eq_1, if_neg hlt, if_neg hltk]
    intro heq; have := Option.some.inj heq; subst this
    have hm_def : _m = (lo.1 + hi.1) / 2 := rfl
    refine ⟨?_, ?_, Bool.eq_false_iff.mpr hlt, Bool.eq_false_iff.mpr hltk⟩
    · show lo.1 ≤ _m; omega
    · show _m ≤ hi.1; omega

set_option maxHeartbeats 1600000 in
include h in
theorem binSearchIdxAux_none
    (htr : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hs : as.Pairwise (fun x y => lt x y = true)) :
    binSearchIdxAux lt as k lo hi h = none →
    ∀ i : Fin as.size, lo.1 ≤ i.1 → i.1 ≤ hi.1 → lt as[i] k ∨ lt k as[i] := by
  have hpw := Array.pairwise_iff_getElem.mp hs
  induction lo, hi, h using binSearchIdxAux.induct lt as k with
  | case1 lo hi h _m _a hlt hm _ ih =>
    show binSearchIdxAux lt as k lo hi h = none → _
    rw [binSearchIdxAux.eq_1, if_pos hlt, dif_pos hm]
    intro heq i hli hri
    by_cases hle : _m + 1 ≤ i.1
    · exact ih heq i hle hri
    · left; show lt as[i.1] k = true
      by_cases hieqm : i.1 = _m
      · simp only [hieqm]; exact hlt
      · exact htr _ _ _ (hpw i.1 _m i.isLt (by omega) (by omega)) hlt
  | case2 lo hi h _m _a hlt hm =>
    intro _ i hli hri
    left; show lt as[i.1] k = true
    have : i.1 = _m := by omega
    simp only [this]; exact hlt
  | case3 lo hi h _m _a hlt hltk hm =>
    intro _ i hli hri
    right; show lt k as[i.1] = true
    by_cases hieqm : i.1 = _m
    · simp only [hieqm]; exact hltk
    · have : _m < i.1 := by omega
      exact htr _ _ _ hltk (hpw _m i.1 (by omega) i.isLt this)
  | case4 lo hi h _m _a hlt hltk hm _ ih =>
    show binSearchIdxAux lt as k lo hi h = none → _
    rw [binSearchIdxAux.eq_1, if_neg hlt, if_pos hltk, dif_neg hm]
    intro heq i hli hri
    by_cases hle : i.1 ≤ _m - 1
    · exact ih heq i hli hle
    · right; show lt k as[i.1] = true
      by_cases hieqm : i.1 = _m
      · simp only [hieqm]; exact hltk
      · exact htr _ _ _ hltk (hpw _m i.1 (by omega) i.isLt (by omega))
  | case5 lo hi h _m _a hlt hltk =>
    show binSearchIdxAux lt as k lo hi h = none → _
    rw [binSearchIdxAux.eq_1, if_neg hlt, if_neg hltk]
    intro heq; exact absurd heq (by simp)

end binSearchIdxProofs

theorem binSearchIdx_some_spec {α : Type u} {lt : α → α → Bool} {as : Array α} {k : α}
    {i : Fin as.size} (h : binSearchIdx as k lt = some i) :
    lt as[i] k = false ∧ lt k as[i] = false := by
  unfold binSearchIdx at h; split at h
  · have ⟨_, _, h3, h4⟩ := binSearchIdxAux_some h; exact ⟨h3, h4⟩
  · exact absurd h (by simp)

theorem binSearchIdx_none_spec {α : Type u} {lt : α → α → Bool} {as : Array α} {k : α}
    (htr : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hs : as.Pairwise (fun x y => lt x y = true))
    (h : binSearchIdx as k lt = none) :
    ∀ i : Fin as.size, lt as[i] k ∨ lt k as[i] := by
  unfold binSearchIdx at h; split at h
  · intro i; exact binSearchIdxAux_none htr hs h i (by simp) (by simp; omega)
  · intro i; exact absurd i.isLt (by omega)

/-- `O(|xs| + |ys|)`. Set difference of sorted arrays `xs` and `ys` with no duplicates. -/
def mergeDiff [ord : Ord α] (xs ys : Array α) : Array α :=
  go (Array.mkEmpty xs.size) 0 0
where
  /-- Auxiliary definition for `mergeDiff`. -/
  go (acc : Array α) (i j : Nat) : Array α :=
    if hi : i ≥ xs.size then
      acc
    else if hj : j ≥ ys.size then
      acc ++ xs[i:]
    else
      let x := xs[i]
      let y := ys[j]
      match compare x y with
      | .lt => go (acc.push x) (i + 1) j
      | .gt => go acc i (j + 1)
      | .eq => go acc (i + 1) (j + 1)
  termination_by xs.size + ys.size - (i + j)

/-- `O(|xs| + |ys|)`. Intersection of sorted arrays `xs` and `ys` with no duplicates. -/
def mergeIntersect [ord : Ord α] (xs ys : Array α) : Array α :=
  go (Array.mkEmpty (min xs.size ys.size)) 0 0
where
  /-- Auxiliary definition for `mergeIntersect`. -/
  go (acc : Array α) (i j : Nat) : Array α :=
    if hi : i ≥ xs.size then
      acc
    else if hj : j ≥ ys.size then
      acc
    else
      let x := xs[i]
      let y := ys[j]
      match compare x y with
      | .lt => go acc (i + 1) j
      | .gt => go acc i (j + 1)
      | .eq => go (acc.push x) (i + 1) (j + 1)
  termination_by xs.size + ys.size - (i + j)

end Array

/-! ## Type definition -/

/-- A strictly sorted array, used as a set representation. -/
abbrev OrdArray (α : Type u) [Ord α] : Type u :=
  { a : Array α // a.toList.Pairwise (OrdList.cmpLt (α := α)) }

namespace OrdArray

open Std OrdList

/-! ## Comparison helper -/

/-- Boolean "less than" for binary search APIs that expect `α → α → Bool`. -/
@[inline] abbrev cmpLtBool [Ord α] (a b : α) : Bool := compare a b == .lt

/-! ## Efficient operations -/

section Operations
variable {α : Type u} [Ord α]

/-- O(log n) membership test using binary search on a sorted array. -/
@[inline] def ordArrayContains (a : α) (arr : Array α) : Bool :=
  arr.binSearchContainsUP a cmpLtBool

/-- Insert `a` into a sorted array. Uses linear insertion for small arrays,
    binary insert for large arrays. -/
@[inline] def ordArrayInsert (a : α) (arr : Array α)
  -- (threshold : Nat := 8)
   : Array α :=
  -- if arr.size < threshold then
  --   (sortedInsertNoDup a arr.toList).toArray
  -- else
    arr.binInsert cmpLtBool a

/-- Remove `a` from a sorted array using binary search. -/
@[inline] def ordArrayRemove (a : α) (arr : Array α) : Array α :=
  match arr.binSearchIdx a cmpLtBool with
  | some idx => arr.eraseIdx idx
  | none => arr

end Operations

/-! ## Bridging lemmas -/

section Bridge
variable {α : Type u} [Ord α] [TransOrd α] [LawfulEqOrd α]

theorem ordArrayContains_iff (a : α) (arr : Array α)
    (hs : arr.Pairwise (cmpLt (α := α))) :
    ordArrayContains a arr = true ↔ a ∈ arr := by
  unfold ordArrayContains Array.binSearchContainsUP
  split
  on_goal 2=> grind
  simp ; rw [Array.binSearchAux_found_continuation]
  constructor
  · intro h ; rw [Option.isSome_iff_exists] at h ; rcases h with ⟨a, h⟩
    obtain ⟨i, hli, hri, heq, hlt, hgt⟩ := Array.binSearchAux_some_then_found h
    simp [cmpLtBool, Ordering.ne_lt_iff_isGE] at hlt hgt ; subst a
    rw [Std.OrientedCmp.isGE_iff_isLE] at hlt
    have := Ordering.eq_eq_of_isLE_of_isGE hlt hgt ; grind
  · intro hin ; rw [Option.isSome_iff_ne_none] ; intro h
    have htmp := Array.binSearchAux_none_then_not_found
      (fun a b c hab hbc => by simp [cmpLtBool] at hab hbc ⊢; exact Std.TransCmp.lt_trans hab hbc)
      (by simp ; apply hs) h
    rw [Array.mem_iff_getElem] at hin ; rcases hin with ⟨i, hlt, heq⟩
    specialize htmp ⟨i, hlt⟩ (by simp) (by simp ; omega)
    simp [cmpLtBool] at htmp ; grind

/-! ### Helpers for `binInsertAux` proofs -/

omit [Ord α] [TransOrd α] [LawfulEqOrd α] in
private theorem cmpLt_of_cmpLtBool' [Ord α] {a b : α}
    (h : cmpLtBool a b = true) : cmpLt (α := α) a b := by
  simp [cmpLtBool, beq_iff_eq] at h; exact h

omit [LawfulEqOrd α] in
private theorem cmpLt_irrefl' (a : α) : ¬cmpLt (α := α) a a := by
  simp [cmpLt, ReflOrd.compare_self]

omit [LawfulEqOrd α] in
private theorem cmpLt_asymm' {a b : α} (h1 : cmpLt (α := α) a b) : ¬cmpLt (α := α) b a := by
  intro h2; simp [cmpLt] at h1 h2
  have : compare b a = .gt := OrientedCmp.gt_of_lt h1
  rw [this] at h2; exact absurd h2 (by decide)

omit [LawfulEqOrd α] in
private theorem cmpLt_trans' {a b c : α}
    (h1 : cmpLt (α := α) a b) (h2 : cmpLt (α := α) b c) : cmpLt (α := α) a c := by
  simp [cmpLt] at *; exact TransCmp.lt_trans h1 h2

private theorem eq_of_not_cmpLtBool' {a b : α}
    (h1 : ¬(cmpLtBool a b = true)) (h2 : ¬(cmpLtBool b a = true)) : a = b := by
  simp only [cmpLtBool, beq_iff_eq] at h1 h2
  have h1' : (compare a b).isGE := by rwa [Ordering.ne_lt_iff_isGE] at h1
  have h2' : (compare b a).isGE := by rwa [Ordering.ne_lt_iff_isGE] at h2
  rw [OrientedCmp.isGE_iff_isLE] at h1'
  exact (LawfulEqOrd.eq_of_compare (Ordering.eq_eq_of_isLE_of_isGE h1' h2')).symm

omit [Ord α] [TransOrd α] [LawfulEqOrd α] in
private theorem sorted_arr_cmpLt {α : Type u} [Ord α] {arr : Array α}
    (hs : arr.toList.Pairwise (cmpLt (α := α)))
    {i j : Nat} (hi : i < arr.size) (hj : j < arr.size) (hij : i < j) :
    cmpLt (α := α) arr[i] arr[j] := by
  have : arr.toList.Pairwise (cmpLt (α := α)) := hs
  rw [show arr.toList.Pairwise (cmpLt (α := α)) =
    (Array.Pairwise (cmpLt (α := α)) arr) from by simp [Array.Pairwise]] at this
  exact (Array.pairwise_iff_getElem.mp this) i j hi hj hij

omit [Ord α] [TransOrd α] [LawfulEqOrd α] in
private theorem insertIdx_eq_take_cons_drop {α : Type u} {l : List α} {i : Nat} {x : α} (h : i ≤ l.length) :
    l.insertIdx i x = l.take i ++ (x :: l.drop i) := by
  induction l generalizing i with
  | nil =>
    simp at h; subst h; simp [List.insertIdx]
  | cons hd tl ih =>
    cases i with
    | zero => simp [List.insertIdx]
    | succ i =>
      simp at h
      simp [List.insertIdx_succ_cons, ih h]

/-! ### `binInsertAux` correctness theorems -/

set_option maxHeartbeats 6400000 in
open private Array.binInsertAux in Array.binInsertM in
theorem binInsertAux_intact_if_in
    (a : α) (arr : Array α)
    (hs : arr.toList.Pairwise (cmpLt (α := α)))
    (hmem : a ∈ arr.toList)
    (lo hi : Fin arr.size) (hlh : lo.1 ≤ hi.1)
    (w : cmpLtBool arr[lo] a = true)
    (hhi : cmpLtBool a arr[hi] = true) :
    (Array.binInsertAux cmpLtBool (fun (_ : α) => (a : Id α)) (fun (_ : Unit) => (a : Id α))
      arr a lo hi hlh w : Id (Array α)).toList = arr.toList := by
  suffices ∀ n (lo hi : Fin arr.size) (hlh : lo.1 ≤ hi.1)
      (w : cmpLtBool arr[lo] a = true) (hhi : cmpLtBool a arr[hi] = true),
      hi.1 - lo.1 ≤ n →
      (Array.binInsertAux cmpLtBool (fun (_ : α) => (a : Id α)) (fun (_ : Unit) => (a : Id α))
        arr a lo hi hlh w : Id (Array α)).toList = arr.toList by
    exact this (hi.1 - lo.1) lo hi hlh w hhi (Nat.le_refl _)
  intro n; induction n with
  | zero =>
    intro lo hi hlh w hhi hle
    exfalso
    have hlohi : lo.1 = hi.1 := by omega
    have hw : cmpLt (α := α) arr[lo] a := cmpLt_of_cmpLtBool' w
    have hh : cmpLt (α := α) a arr[hi] := cmpLt_of_cmpLtBool' hhi
    have : cmpLt (α := α) a arr[lo] := by
      have : arr[hi.1] = arr[lo.1] := by simp [show hi.1 = lo.1 from hlohi.symm]
      simp [this] at hh; exact hh
    exact cmpLt_asymm' hw this
  | succ n ih =>
    intro lo hi hlh w hhi hle
    show (Array.binInsertAux cmpLtBool (fun _ => a) (fun _ => a) arr a lo hi hlh w : Id (Array α)).toList = _
    rw [Array.binInsertAux.eq_def]; dsimp only
    split
    · -- arr[mid] < a
      rename_i w₁; split
      · -- mid = lo: insertIdx. Impossible since a ∈ arr and lo < j < hi = lo+1.
        rename_i h'
        exfalso
        have hhi_eq : hi.1 = lo.1 + 1 := by
          let a := hi.val - lo.val
          have ha : hi.val = lo.val + a := by simp [a, hlh]
          clear_value a
          rw [ha] at h'
          cases a with
          | zero => simp at ha ; simp [cmpLtBool, ha] at w hhi ; have := OrientedCmp.gt_of_lt hhi ; grind
          | succ a =>
            cases a with
            | zero => exact ha
            | succ _ => grind
        rw [List.mem_iff_getElem] at hmem
        obtain ⟨j, hj, heqj⟩ := hmem
        simp only [Array.length_toList] at hj
        have heqj' : arr[j] = a := by simp at heqj; exact heqj
        have hjlo : lo.1 < j := by
          rcases Nat.lt_or_ge j lo.1 with hjl | hjge
          · exact absurd (cmpLt_of_cmpLtBool' w)
              (cmpLt_asymm' (heqj' ▸ sorted_arr_cmpLt hs hj lo.isLt hjl))
          · rcases Nat.eq_or_lt_of_le hjge with rfl | h
            · exact absurd (cmpLt_of_cmpLtBool' w) (heqj' ▸ cmpLt_irrefl' a)
            · exact h
        have hjhi : j < hi.1 := by
          rcases Nat.lt_or_ge hi.1 j with h | hhge
          · exact absurd (cmpLt_of_cmpLtBool' hhi)
              (cmpLt_asymm' (heqj' ▸ sorted_arr_cmpLt hs hi.isLt hj h))
          · rcases Nat.eq_or_lt_of_le hhge with rfl | h
            · exact absurd (cmpLt_of_cmpLtBool' hhi) (heqj' ▸ cmpLt_irrefl' a)
            · exact h
        omega
      · -- mid ≠ lo: recurse with lo' = mid
        exact ih ⟨(lo.1 + hi.1) / 2, by omega⟩ hi (by simp; omega) _ hhi (by simp; omega)
    · -- ¬(arr[mid] < a)
      rename_i w₁; split
      · -- a < arr[mid]: recurse with hi' = mid
        exact ih lo ⟨(lo.1 + hi.1) / 2, by omega⟩ (by simp; omega) w (by grind) (by simp; omega)
      · -- arr[mid] = a: modify, list unchanged
        rename_i w₂
        have heq_mid : arr[(lo.1 + hi.1) / 2] = a := eq_of_not_cmpLtBool' w₁ w₂
        -- modifyM in Id is modify
        show (arr.modify ((lo.1 + hi.1) / 2) (fun _ => a)).toList = arr.toList
        rw [Array.toList_modify]
        apply List.ext_getElem (by simp)
        intro j hj hj'
        simp only [List.getElem_modify]
        split
        · rename_i heqj; subst heqj; simp [heq_mid]
        · rfl

set_option maxHeartbeats 6400000 in
open private Array.binInsertAux in Array.binInsertM in
theorem binInsertAux_new_in
    (a : α) (arr : Array α)
    (hs : arr.toList.Pairwise (cmpLt (α := α)))
    (hmem : a ∉ arr.toList)
    (lo hi : Fin arr.size) (hlh : lo.1 ≤ hi.1)
    (w : cmpLtBool arr[lo] a = true)
    (hhi : cmpLtBool a arr[hi] = true) :
    ∃ pre suf, arr.toList = pre ++ suf ∧
      (Array.binInsertAux cmpLtBool (fun (_ : α) => (a : Id α)) (fun (_ : Unit) => (a : Id α))
        arr a lo hi hlh w : Id (Array α)).toList = pre ++ (a :: suf) ∧
      (∀ x ∈ pre, cmpLt (α := α) x a) ∧ (∀ x ∈ suf, cmpLt (α := α) a x) := by
  suffices ∀ n (lo hi : Fin arr.size) (hlh : lo.1 ≤ hi.1)
      (w : cmpLtBool arr[lo] a = true) (hhi : cmpLtBool a arr[hi] = true),
      hi.1 - lo.1 ≤ n →
      ∃ pre suf, arr.toList = pre ++ suf ∧
        (Array.binInsertAux cmpLtBool (fun (_ : α) => (a : Id α)) (fun (_ : Unit) => (a : Id α))
          arr a lo hi hlh w : Id (Array α)).toList = pre ++ (a :: suf) ∧
        (∀ x ∈ pre, cmpLt (α := α) x a) ∧ (∀ x ∈ suf, cmpLt (α := α) a x) by
    exact this (hi.1 - lo.1) lo hi hlh w hhi (Nat.le_refl _)
  intro n; induction n with
  | zero =>
    intro lo hi hlh w hhi hle
    exfalso
    have hlohi : lo.1 = hi.1 := by omega
    have hw : cmpLt (α := α) arr[lo] a := cmpLt_of_cmpLtBool' w
    have hh : cmpLt (α := α) a arr[hi] := cmpLt_of_cmpLtBool' hhi
    have : arr[hi.1] = arr[lo.1] := by simp [show hi.1 = lo.1 from hlohi.symm]
    have : cmpLt (α := α) a arr[lo] := by simp [this] at hh; exact hh
    exact cmpLt_asymm' hw this
  | succ n ih =>
    intro lo hi hlh w hhi hle
    show ∃ pre suf, arr.toList = pre ++ suf ∧
      (Array.binInsertAux cmpLtBool (fun _ => a) (fun _ => a) arr a lo hi hlh w : Id (Array α)).toList
        = pre ++ (a :: suf) ∧ _
    rw [Array.binInsertAux.eq_def]; dsimp only
    split
    · -- arr[mid] < a
      rename_i w₁; split
      · -- mid = lo (base): insertIdx at lo+1
        rename_i h'
        have hhi_eq : hi.1 = lo.1 + 1 := by
          let a := hi.val - lo.val
          have ha : hi.val = lo.val + a := by simp [a, hlh]
          clear_value a; rw [ha] at h'
          cases a with
          | zero => simp at ha; simp [cmpLtBool, ha] at w hhi; have := OrientedCmp.gt_of_lt hhi; grind
          | succ a => cases a with
            | zero => exact ha
            | succ _ => grind
        -- Result: arr.insertIdx (lo+1) a
        -- arr.toList = take (lo+1) ++ drop (lo+1)
        refine ⟨arr.toList.take (lo.1 + 1), arr.toList.drop (lo.1 + 1), ?_, ?_, ?_, ?_⟩
        · simp [List.take_append_drop]
        · -- insertIdx result
          show (arr.insertIdx (lo.1 + 1) a (by omega)).toList = _
          rw [Array.toList_insertIdx]
          exact insertIdx_eq_take_cons_drop (by simp; omega)
        · -- ∀ x ∈ take (lo+1), cmpLt x a
          intro x hx
          rw [List.mem_take_iff_getElem] at hx
          obtain ⟨j, hj, _, rfl⟩ := hx
          simp only [Array.length_toList] at hj
          have hj' : j < arr.size := by omega
          show cmpLt (α := α) arr[j] a
          rcases Nat.lt_or_ge j lo.1 with hjl | hjge
          · exact cmpLt_trans' (sorted_arr_cmpLt hs hj' lo.isLt hjl) (cmpLt_of_cmpLtBool' w)
          · rcases Nat.eq_or_lt_of_le hjge with rfl | h
            · exact cmpLt_of_cmpLtBool' w
            · omega -- j ≥ lo+1 contradicts j < lo+1
        · -- ∀ x ∈ drop (lo+1), cmpLt a x
          intro x hx
          rw [List.mem_drop_iff_getElem] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          simp only [Array.length_toList] at hj
          have hj' : lo.1 + 1 + j < arr.size := by omega
          show cmpLt (α := α) a arr.toList[lo.1 + 1 + j]
          simp only [Array.getElem_toList]
          have hh := cmpLt_of_cmpLtBool' hhi
          rcases Nat.eq_or_lt_of_le (show hi.1 ≤ lo.1 + 1 + j by omega) with heq | hjgt
          · have : arr[lo.1 + 1 + j] = arr[hi] := by congr 1; omega
            rw [this]; exact hh
          · exact cmpLt_trans' hh (sorted_arr_cmpLt hs hi.isLt hj' hjgt)
      · -- mid ≠ lo: recurse with lo' = mid
        exact ih ⟨(lo.1 + hi.1) / 2, by omega⟩ hi (by simp; omega) _ hhi (by simp; omega)
    · -- ¬(arr[mid] < a)
      rename_i w₁; split
      · -- a < arr[mid]: recurse with hi' = mid
        exact ih lo ⟨(lo.1 + hi.1) / 2, by omega⟩ (by simp; omega) w (by grind) (by simp; omega)
      · -- arr[mid] = a: impossible since a ∉ arr
        rename_i w₂
        exfalso; apply hmem
        have heq_mid : arr[(lo.1 + hi.1) / 2] = a := eq_of_not_cmpLtBool' w₁ w₂
        have hmid_lt : (lo.1 + hi.1) / 2 < arr.size := by omega
        rw [List.mem_iff_getElem]
        exact ⟨(lo.1 + hi.1) / 2, by simp; exact hmid_lt, by simp [heq_mid]⟩

-- open private Array.binInsertAux in Array.binInsertM in
theorem binInsert_toList_eq (a : α) (arr : Array α)
    (hs : arr.toList.Pairwise (cmpLt (α := α))) :
    (arr.binInsert cmpLtBool a).toList = sortedInsertNoDup a arr.toList := by
  dsimp [Array.binInsert, Array.binInsertM, pure, bind, Id.run]
  split <;> rename_i h1
  on_goal 1=> rw [← Array.eq_empty_iff_size_eq_zero] at h1 ; subst arr ; dsimp [sortedInsertNoDup]
  rename_i h1
  rw [Array.size_eq_length_toList] at h1
  rcases heq : arr.toList with _ | ⟨x, l⟩
  on_goal 1=> grind
  have htmp := Array.getElem_toList (xs := arr) (i := 0) (by grind)
  simp [heq] at htmp ; simp only [← htmp]
  simp [cmpLtBool]
  split <;> rename_i h2
  on_goal 1=> simp [sortedInsertNoDup, h2, heq]
  rw [Ordering.ne_lt_iff_isGE] at h2
  split <;> rename_i h3
  on_goal 2=>
    rw [Ordering.ne_lt_iff_isGE, Std.OrientedCmp.isGE_eq_isLE] at h3
    have : a = x := by grind [Ordering.eq_eq_of_isLE_of_isGE]
    subst a ; simp [sortedInsertNoDup, Array.modifyM, pure, bind]
    split
    on_goal 2=> grind
    simp [heq]
  rw [← heq] ; clear heq h2
  split <;> rename_i h4
  on_goal 1=>
    simp ; rw [← OrientedCmp.gt_iff_lt] at h4
    have hnotin : a ∉ arr.toList := by
      intro hin ; rw [List.mem_iff_getElem] at hin
      obtain ⟨j, hj, hjeq⟩ := hin
      by_cases hjend : j = arr.size - 1
      · subst j ; subst a ; simp at h4
      · rw [List.pairwise_iff_getElem] at hs
        simp at hj
        specialize hs j (arr.size - 1) hj (by simp; omega) (by omega)
        whnf at hs ; grind
    obtain ⟨pf, sf, heq, hafter, hpf, hsf⟩ := sortedInsertNoDup_new_in (a := a) hs hnotin
    rw [hafter, heq]
    cases sf with
    | nil => simp
    | cons b sf =>
      simp at hsf ; have hsf' := hsf.left
      cases sf with
      | nil =>
        have htmp : b = arr[arr.size - 1] := by simp [← Array.getElem_toList, heq] ; grind
        simp [← htmp] at h4 ; grind
      | cons c _ =>
        rw [List.pairwise_iff_getElem] at hs
        specialize hs pf.length (arr.size - 1) (by simp [heq]) (by simp; omega) (by simp [Array.size_eq_length_toList, heq])
        grind
  split <;> rename_i h5
  on_goal 2=>
    rw [Ordering.ne_lt_iff_isGE] at h4
    rw [Ordering.ne_lt_iff_isGE, Std.OrientedCmp.isGE_eq_isLE] at h5
    have : arr[arr.size - 1] = a := by grind [Ordering.eq_eq_of_isLE_of_isGE]
    subst a ; simp [Array.modifyM, pure, bind]
    rw [sortedInsertNoDup_intact_if_in] <;> grind
  by_cases hin : a ∈ arr.toList
  · rw [binInsertAux_intact_if_in] <;> try assumption
    · rw [sortedInsertNoDup_intact_if_in] <;> grind
    · unfold cmpLtBool ; simp ; assumption
  · obtain ⟨pre, suf, heq_arr, hres, hpre, hsuf⟩ :=
      binInsertAux_new_in a arr hs hin ⟨0, by omega⟩ ⟨arr.size - 1, by omega⟩ (Nat.zero_le _)
        (by simp [cmpLtBool]; rw [htmp] at h3; exact h3)
        (by simp [cmpLtBool]; exact h5)
    rw [hres]; symm
    apply sorted_unique (sortedInsertNoDup_sorted a arr.toList hs)
    · have hps : (pre ++ suf).Pairwise (cmpLt (α := α)) := heq_arr ▸ hs
      rw [List.pairwise_append] at hps ⊢
      refine ⟨hps.1, ?_, ?_⟩
      · rw [List.pairwise_cons]; exact ⟨hsuf, hps.2.1⟩
      · intro x hx y hy; simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hpre x hx
        · exact hps.2.2 x hx y hy
    · intro x; rw [sortedInsertNoDup_mem]
      simp only [List.mem_append, List.mem_cons, heq_arr]; tauto

/-- `ordArrayInsert` maintains sortedness. -/
theorem ordArrayInsert_sorted (a : α) (arr : Array α) --(threshold : Nat)
    (hs : arr.toList.Pairwise (cmpLt (α := α))) :
    (ordArrayInsert a arr).toList.Pairwise (cmpLt (α := α)) := by
  simp only [ordArrayInsert]
  -- split
  -- · simp ; exact sortedInsertNoDup_sorted a arr.toList hs
  · rw [binInsert_toList_eq a arr hs] ; exact sortedInsertNoDup_sorted a arr.toList hs

/-- `ordArrayInsert` produces the same list as `sortedInsertNoDup`. -/
theorem ordArrayInsert_toList (a : α) (arr : Array α) --(threshold : Nat)
    (hs : arr.toList.Pairwise (cmpLt (α := α))) :
    (ordArrayInsert a arr).toList = sortedInsertNoDup a arr.toList := by
  simp only [ordArrayInsert]
  -- split
  -- · simp
  · exact binInsert_toList_eq a arr hs

private theorem eq_of_cmpLtBool_false {a b : α}
    (h1 : cmpLtBool a b = false) (h2 : cmpLtBool b a = false) : a = b := by
  unfold cmpLtBool at h1 h2
  have h1' : compare a b ≠ .lt := by intro h; simp [h] at h1
  have h2' : compare b a ≠ .lt := by intro h; simp [h] at h2
  have hge1 : (compare a b).isGE := Ordering.ne_lt_iff_isGE.mp h1'
  have hge2 : (compare b a).isGE := Ordering.ne_lt_iff_isGE.mp h2'
  rw [Std.OrientedCmp.isGE_iff_isLE] at hge1
  exact (Std.LawfulEqOrd.eq_of_compare (Ordering.eq_eq_of_isLE_of_isGE hge1 hge2)).symm

private theorem sortedRemove_eq_eraseIdx {a : α} {l : List α}
    (hs : l.Pairwise (cmpLt (α := α)))
    {i : Nat} (hi : i < l.length) (heq : l[i] = a) :
    sortedRemove a l = l.eraseIdx i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons h t ih =>
    cases i with
    | zero =>
      simp at heq; subst heq
      simp [sortedRemove, Std.ReflOrd.compare_self]
    | succ j =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      simp only [List.getElem_cons_succ] at heq
      have hpw := List.pairwise_cons.mp hs
      have hlt_ha : cmpLt (α := α) h a := heq ▸ hpw.1 _ (List.getElem_mem hi)
      have hcmp : compare a h = .gt := Std.OrientedCmp.gt_of_lt hlt_ha
      simp [sortedRemove, hcmp, List.eraseIdx_cons_succ]
      exact ih hpw.2 hi heq

/-- `ordArrayRemove` produces the same list as `sortedRemove`. -/
theorem ordArrayRemove_toList (a : α) (arr : Array α)
    (hs : arr.toList.Pairwise (cmpLt (α := α))) :
    (ordArrayRemove a arr).toList = sortedRemove a arr.toList := by
  unfold ordArrayRemove
  match heq : arr.binSearchIdx a cmpLtBool with
  | some idx =>
    have hspec := Array.binSearchIdx_some_spec heq
    have ha_eq : arr[idx] = a := eq_of_cmpLtBool_false hspec.1 hspec.2
    rw [Array.toList_eraseIdx]
    exact (sortedRemove_eq_eraseIdx hs (by simp) (by simp; exact ha_eq)).symm
  | none =>
    have hmem : a ∉ arr.toList := by
      intro hmem; rw [List.mem_iff_getElem] at hmem
      obtain ⟨j, hj, hjeq⟩ := hmem
      simp only [Array.length_toList] at hj
      have := Array.binSearchIdx_none_spec
        (fun a b c hab hbc => by simp [cmpLtBool] at hab hbc ⊢; exact Std.TransCmp.lt_trans hab hbc)
        (by simp [Array.Pairwise]; exact hs) heq ⟨j, hj⟩
      simp only [Array.getElem_toList] at hjeq
      simp [hjeq, cmpLtBool, Std.ReflOrd.compare_self] at this
    exact (sortedRemove_intact_if_notin hs hmem).symm

/-- `ordArrayRemove` maintains sortedness. -/
theorem ordArrayRemove_sorted (a : α) (arr : Array α)
    (hs : arr.toList.Pairwise (cmpLt (α := α))) :
    (ordArrayRemove a arr).toList.Pairwise (cmpLt (α := α)) := by
  rw [ordArrayRemove_toList a arr hs]
  exact sortedRemove_sorted a arr.toList hs

omit [Ord α] [TransOrd α] [LawfulEqOrd α] in
set_option maxHeartbeats 3200000 in
private theorem append_subarray_toList (acc ys : Array α) (j : Nat) :
    (acc ++ ys[j:]).toList = acc.toList ++ ys.toList.drop j := by
  simp only [Array.toList_append, Subarray.toList_toArray]
  rw [← Array.toList_mkSlice_rci (xs := ys) (lo := j)]
  congr 1
  simp only [Array.toSubarray, Rci.Sliceable.mkSlice, Rci.HasRcoIntersection.intersection]
  split <;> split <;> split <;> congr 1 <;> simp_all
  omega

omit [TransOrd α] [LawfulEqOrd α] in
set_option maxHeartbeats 6400000 in
private theorem mergeDedupWith_go_toList (xs ys : Array α) (acc : Array α) (i j : Nat) :
    (Array.mergeDedupWith.go xs ys (fun x _ => x) acc i j).toList =
    acc.toList ++ sortedMergeNoDup (xs.toList.drop i) (ys.toList.drop j) := by
  induction acc, i, j using Array.mergeDedupWith.go.induct (ord := inferInstance) xs ys (fun x _ => x) with
  | case1 acc i j hi =>
    rw [Array.mergeDedupWith.go, dif_pos hi, append_subarray_toList]
    congr 1
    have : xs.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [this]; simp [sortedMergeNoDup]
  | case2 acc i j hni hj =>
    rw [Array.mergeDedupWith.go, dif_neg hni, dif_pos hj, append_subarray_toList]
    congr 1
    have : ys.toList.drop j = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [this]
    cases h : xs.toList.drop i <;> simp_all
  | case3 acc i j hni hnj x y hlt ih =>
    have hi' : i < xs.size := by omega
    have hj' : j < ys.size := by omega
    rw [Array.mergeDedupWith.go, dif_neg hni, dif_neg hnj]
    have hlt' : compare xs[i] ys[j] = .lt := hlt
    simp only [show x = xs[i] from rfl] at ih
    simp only [hlt']
    rw [ih]
    have hxs : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hi')]; simp
    have hys : ys.toList.drop j = ys[j] :: ys.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hj')]; simp
    rw [hxs, hys, sortedMergeNoDup, hlt']
    simp [Array.toList_push, ← hys, List.append_assoc]
  | case4 acc i j hni hnj x y hgt ih =>
    have hi' : i < xs.size := by omega
    have hj' : j < ys.size := by omega
    rw [Array.mergeDedupWith.go, dif_neg hni, dif_neg hnj]
    have hgt' : compare xs[i] ys[j] = .gt := hgt
    simp only [show y = ys[j] from rfl] at ih
    simp only [hgt']
    rw [ih]
    have hxs : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hi')]; simp
    have hys : ys.toList.drop j = ys[j] :: ys.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hj')]; simp
    rw [hxs, hys, sortedMergeNoDup, hgt']
    simp [Array.toList_push, ← hxs, List.append_assoc]
  | case5 acc i j hni hnj x y heq ih =>
    have hi' : i < xs.size := by omega
    have hj' : j < ys.size := by omega
    have hcmp : compare xs[i] ys[j] = .eq := by
      have : x = xs[i] := rfl; have : y = ys[j] := rfl
      cases h : compare xs[i] ys[j] <;> simp_all
    rw [Array.mergeDedupWith.go, dif_neg hni, dif_neg hnj]
    simp only [show x = xs[i] from rfl] at ih
    simp only [hcmp]
    rw [ih]
    have hxs : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hi')]; simp
    have hys : ys.toList.drop j = ys[j] :: ys.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hj')]; simp
    rw [hxs, hys, sortedMergeNoDup, hcmp]
    simp [Array.toList_push, List.append_assoc]

omit [TransOrd α] [LawfulEqOrd α] in
/-- `mergeDedup` on sorted arrays produces the same list as `sortedMergeNoDup`. -/
theorem mergeDedup_toList (arr1 arr2 : Array α)
    (_ : arr1.toList.Pairwise (cmpLt (α := α)))
    (_ : arr2.toList.Pairwise (cmpLt (α := α))) :
    (Array.mergeDedup arr1 arr2).toList = sortedMergeNoDup arr1.toList arr2.toList := by
  simp only [Array.mergeDedup, Array.mergeDedupWith]
  rw [mergeDedupWith_go_toList]
  simp

/-- `mergeDedup` maintains sortedness. -/
theorem mergeDedup_sorted (arr1 arr2 : Array α)
    (hs₁ : arr1.toList.Pairwise (cmpLt (α := α)))
    (hs₂ : arr2.toList.Pairwise (cmpLt (α := α))) :
    (Array.mergeDedup arr1 arr2).toList.Pairwise (cmpLt (α := α)) := by
  rw [mergeDedup_toList arr1 arr2 hs₁ hs₂]
  exact sortedMergeNoDup_sorted arr1.toList arr2.toList hs₁ hs₂

omit [TransOrd α] [LawfulEqOrd α] in
/-- Filtering an array preserves sortedness. -/
theorem array_filter_sorted (arr : Array α) (p : α → Bool)
    (hs : arr.toList.Pairwise (cmpLt (α := α))) :
    (arr.filter p).toList.Pairwise (cmpLt (α := α)) := by
  rw [Array.toList_filter]; exact List.Pairwise.filter p hs

omit [TransOrd α] [LawfulEqOrd α] in
set_option maxHeartbeats 6400000 in
private theorem mergeDiff_go_toList (xs ys : Array α) (acc : Array α) (i j : Nat) :
    (Array.mergeDiff.go xs ys acc i j).toList =
    acc.toList ++ sortedDiffNoDup (xs.toList.drop i) (ys.toList.drop j) := by
  induction acc, i, j using Array.mergeDiff.go.induct (ord := inferInstance) xs ys with
  | case1 acc i j hi =>
    rw [Array.mergeDiff.go, dif_pos hi]
    have : xs.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [this]; simp [sortedDiffNoDup]
  | case2 acc i j hni hj =>
    rw [Array.mergeDiff.go, dif_neg hni, dif_pos hj, append_subarray_toList]
    congr 1
    have : ys.toList.drop j = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [this]
    cases h : xs.toList.drop i <;> simp_all
  | case3 acc i j hni hnj x y hlt ih =>
    have hi' : i < xs.size := by omega
    have hj' : j < ys.size := by omega
    rw [Array.mergeDiff.go, dif_neg hni, dif_neg hnj]
    have hlt' : compare xs[i] ys[j] = .lt := hlt
    simp only [show x = xs[i] from rfl] at ih
    simp only [hlt']
    rw [ih]
    have hxs : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hi')]; simp
    have hys : ys.toList.drop j = ys[j] :: ys.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hj')]; simp
    rw [hxs, hys, sortedDiffNoDup, hlt']
    simp [Array.toList_push, ← hys, List.append_assoc]
  | case4 acc i j hni hnj x y hgt ih =>
    have hi' : i < xs.size := by omega
    have hj' : j < ys.size := by omega
    rw [Array.mergeDiff.go, dif_neg hni, dif_neg hnj]
    have hgt' : compare xs[i] ys[j] = .gt := hgt
    simp only [hgt']
    rw [ih]
    have hxs : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hi')]; simp
    have hys : ys.toList.drop j = ys[j] :: ys.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hj')]; simp
    rw [hxs, hys, sortedDiffNoDup, hgt']
  | case5 acc i j hni hnj x y heq ih =>
    have hi' : i < xs.size := by omega
    have hj' : j < ys.size := by omega
    have hcmp : compare xs[i] ys[j] = .eq := by
      have : x = xs[i] := rfl; have : y = ys[j] := rfl
      cases h : compare xs[i] ys[j] <;> simp_all
    rw [Array.mergeDiff.go, dif_neg hni, dif_neg hnj]
    simp only [hcmp]
    rw [ih]
    have hxs : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hi')]; simp
    have hys : ys.toList.drop j = ys[j] :: ys.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hj')]; simp
    rw [hxs, hys, sortedDiffNoDup, hcmp]

omit [TransOrd α] [LawfulEqOrd α] in
set_option maxHeartbeats 6400000 in
private theorem mergeIntersect_go_toList (xs ys : Array α) (acc : Array α) (i j : Nat) :
    (Array.mergeIntersect.go xs ys acc i j).toList =
    acc.toList ++ sortedIntersectNoDup (xs.toList.drop i) (ys.toList.drop j) := by
  induction acc, i, j using Array.mergeIntersect.go.induct (ord := inferInstance) xs ys with
  | case1 acc i j hi =>
    rw [Array.mergeIntersect.go, dif_pos hi]
    have : xs.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [this]; simp [sortedIntersectNoDup]
  | case2 acc i j hni hj =>
    rw [Array.mergeIntersect.go, dif_neg hni, dif_pos hj]
    have : ys.toList.drop j = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [this]
    cases h : xs.toList.drop i <;> simp_all
  | case3 acc i j hni hnj x y hlt ih =>
    have hi' : i < xs.size := by omega
    have hj' : j < ys.size := by omega
    rw [Array.mergeIntersect.go, dif_neg hni, dif_neg hnj]
    have hlt' : compare xs[i] ys[j] = .lt := hlt
    simp only [hlt']
    rw [ih]
    have hxs : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hi')]; simp
    have hys : ys.toList.drop j = ys[j] :: ys.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hj')]; simp
    rw [hxs, hys, sortedIntersectNoDup, hlt']
  | case4 acc i j hni hnj x y hgt ih =>
    have hi' : i < xs.size := by omega
    have hj' : j < ys.size := by omega
    rw [Array.mergeIntersect.go, dif_neg hni, dif_neg hnj]
    have hgt' : compare xs[i] ys[j] = .gt := hgt
    simp only [hgt']
    rw [ih]
    have hxs : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hi')]; simp
    have hys : ys.toList.drop j = ys[j] :: ys.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hj')]; simp
    rw [hxs, hys, sortedIntersectNoDup, hgt']
  | case5 acc i j hni hnj x y heq ih =>
    have hi' : i < xs.size := by omega
    have hj' : j < ys.size := by omega
    have hcmp : compare xs[i] ys[j] = .eq := by
      have : x = xs[i] := rfl; have : y = ys[j] := rfl
      cases h : compare xs[i] ys[j] <;> simp_all
    rw [Array.mergeIntersect.go, dif_neg hni, dif_neg hnj]
    simp only [show x = xs[i] from rfl] at ih
    simp only [hcmp]
    rw [ih]
    have hxs : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hi')]; simp
    have hys : ys.toList.drop j = ys[j] :: ys.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; exact hj')]; simp
    rw [hxs, hys, sortedIntersectNoDup, hcmp]
    simp [Array.toList_push, List.append_assoc]

/-- Set difference of two sorted arrays. -/
def ordArrayDiff (arr1 arr2 : Array α) : Array α :=
  Array.mergeDiff arr1 arr2

omit [TransOrd α] [LawfulEqOrd α] in
/-- `ordArrayDiff` produces the same list as `sortedDiffNoDup`. -/
theorem ordArrayDiff_toList (arr1 arr2 : Array α) :
    (ordArrayDiff arr1 arr2).toList = sortedDiffNoDup arr1.toList arr2.toList := by
  simp only [ordArrayDiff, Array.mergeDiff]
  rw [mergeDiff_go_toList]
  simp

/-- `ordArrayDiff` maintains sortedness. -/
theorem ordArrayDiff_sorted (arr1 arr2 : Array α)
    (hs₁ : arr1.toList.Pairwise (cmpLt (α := α)))
    (hs₂ : arr2.toList.Pairwise (cmpLt (α := α))) :
    (ordArrayDiff arr1 arr2).toList.Pairwise (cmpLt (α := α)) := by
  rw [ordArrayDiff_toList arr1 arr2]
  exact sortedDiffNoDup_sorted arr1.toList arr2.toList hs₁ hs₂

/-- Intersection of two sorted arrays. -/
def ordArrayIntersect (arr1 arr2 : Array α) : Array α :=
  Array.mergeIntersect arr1 arr2

omit [TransOrd α] [LawfulEqOrd α] in
/-- `ordArrayIntersect` produces the same list as `sortedIntersectNoDup`. -/
theorem ordArrayIntersect_toList (arr1 arr2 : Array α) :
    (ordArrayIntersect arr1 arr2).toList = sortedIntersectNoDup arr1.toList arr2.toList := by
  simp only [ordArrayIntersect, Array.mergeIntersect]
  rw [mergeIntersect_go_toList]
  simp

/-- `ordArrayIntersect` maintains sortedness. -/
theorem ordArrayIntersect_sorted (arr1 arr2 : Array α)
    (hs₁ : arr1.toList.Pairwise (cmpLt (α := α)))
    (hs₂ : arr2.toList.Pairwise (cmpLt (α := α))) :
    (ordArrayIntersect arr1 arr2).toList.Pairwise (cmpLt (α := α)) := by
  rw [ordArrayIntersect_toList arr1 arr2]
  exact sortedIntersectNoDup_sorted arr1.toList arr2.toList hs₁ hs₂

@[inline] def ofOrdList [TransOrd α] [LawfulEqOrd α] (l : OrdList α) : OrdArray α :=
  ⟨l.val.toArray, by simp; exact l.property⟩

@[inline] def toOrdList (arr : OrdArray α) : OrdList α :=
  ⟨arr.val.toList, arr.property⟩

-- FIXME: Possibly use `Array.sortDedup` in the future?

/-- Build an `OrdArray` from an arbitrary list by sorting and removing duplicates. -/
@[inline] def ofList [TransOrd α] [LawfulEqOrd α] (l : List α) : OrdArray α :=
  ⟨(OrdList.ofList.inner l).toArray, by simp; exact (OrdList.ofList.inner_spec l).left⟩

/-- The empty `OrdArray`. -/
@[inline] def empty : OrdArray α := ⟨#[], by simp⟩

@[inline] def subarrays [TransOrd α] [LawfulEqOrd α] (l : OrdArray α) : List (OrdArray α) :=
  l.toOrdList.sublists.map ofOrdList

end Bridge

/-! ## Instances -/

section Instances
variable {α : Type u} [Ord α]

instance : Inhabited (OrdArray α) where
  default := ⟨#[], by simp⟩

instance [Repr α] : Repr (OrdArray α) where
  reprPrec s p := reprPrec s.val.toList p

instance [Repr α] : Lean.ToJson (OrdArray α) := Veil.jsonOfRepr

/-! ### Ordering instances -/

instance [Std.ReflOrd α] : Std.ReflOrd (OrdArray α) where
  compare_self := Std.ReflOrd.compare_self (α := Array α)

instance [Std.LawfulEqOrd α] : Std.LawfulEqOrd (OrdArray α) where
  eq_of_compare h := Subtype.ext (Std.LawfulEqOrd.eq_of_compare (α := Array α) h)

instance [Std.OrientedOrd α] : Std.OrientedOrd (OrdArray α) where
  eq_swap := Std.OrientedOrd.eq_swap (α := Array α)

instance [Std.TransOrd α] : Std.TransOrd (OrdArray α) where
  isLE_trans h1 h2 := Std.TransOrd.isLE_trans (α := Array α) h1 h2

/-! ### Enumeration -/

instance instEnumerationOrdArray [TransOrd α] [LawfulEqOrd α] [DecidableEq α] [Veil.Enumeration α]
    : Veil.Enumeration (OrdArray α) where
  allValues :=
    (OrdList.ofList (Veil.Enumeration.allValues (α := α))).sublists |>.map OrdArray.ofOrdList
  complete := by
    intro ⟨a, ha⟩ ; simp [ofOrdList]
    exists a.toList ; simp ; exists ha ; simp [OrdList.sublists]
    apply OrdList.mem_contains_then_is_sublist <;> try grind
    intros _ ; simp [OrdList.ofList, ofList.inner_spec, Veil.Enumeration.complete]

end Instances
