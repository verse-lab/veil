import Mathlib.Tactic.Common

/-!
# List Splitting

A pure, tail-recursive function that splits a `List α` into `max 1 numSplits`
disjoint parts, following the same chunking logic as `computeChunkRanges`.

Each chunk is produced in **reversed** order relative to the natural reading order;
this is acceptable for consumers (like BFS) that only care about membership, not ordering.

We prove that the flattened result is a permutation of the original list, which
is sufficient for all downstream membership-based reasoning.
-/

namespace ListSplit

/-! ## Definitions -/

/-- Non-tail-recursive specification function. Splits a list into `n` parts
where each non-last part has `chunkSize` elements and the last part gets the rest. -/
def splitListSpec (chunkSize : Nat) : (n : Nat) → List α → List (List α)
  | 0, _ => []
  | n + 1, remaining =>
    if n = 0 then [remaining]
    else (remaining.take chunkSize) :: splitListSpec chunkSize n (remaining.drop chunkSize)

/-- Like `List.splitAt` but without reversing the first component.
    Equivalent to `(l.take n |>.reverse, l.drop n)` but computed in a single pass. -/
def takeNoRev (n : Nat) (l : List α) : List α × List α := go l n [] where
  go : List α → Nat → List α → List α × List α
  | [],       _,   acc => (acc, [])
  | x :: xs,  n+1, acc => go xs n (x :: acc)
  | xs,       _,   acc => (acc, xs)

/-- Tail-recursive implementation using single-pass chunk extraction.
    Each chunk is produced in reversed order relative to `splitListSpec`. -/
def splitListTR (chunkSize : Nat) : (n : Nat) → List α → List (List α) → List (List α)
  | 0, _, acc => acc.reverse
  | n + 1, remaining, acc =>
    if n = 0 then (remaining.reverse :: acc).reverse
    else
      let (chunk, rest) := takeNoRev chunkSize remaining
      splitListTR chunkSize n rest (chunk :: acc)

/-- Split a list into `max 1 numSplits` disjoint parts using the given `chunkSize`. -/
def splitList (numSplits : Nat) (chunkSize : Nat) (l : List α) : List (List α) :=
  let n := max 1 numSplits
  splitListTR chunkSize n l []

/-! ## Bridge lemmas -/

private theorem takeNoRev.go_spec (l : List α) (n : Nat) (acc : List α) :
    takeNoRev.go l n acc = ((l.take n).reverse ++ acc, l.drop n) := by
  induction l generalizing n acc with
  | nil => simp [takeNoRev.go]
  | cons x xs ih =>
    cases n with
    | zero => simp [takeNoRev.go]
    | succ n =>
      simp only [takeNoRev.go, List.take_succ_cons, List.drop_succ_cons]
      rw [ih]; simp [List.reverse_cons, List.append_assoc]

theorem takeNoRev_spec (n : Nat) (l : List α) :
    takeNoRev n l = ((l.take n).reverse, l.drop n) := by
  simp [takeNoRev, takeNoRev.go_spec]

/-- `splitListTR` produces the same chunks as `splitListSpec`, each reversed. -/
theorem splitListTR_eq_spec (chunkSize : Nat) (n : Nat) (remaining : List α)
    (acc : List (List α)) :
    splitListTR chunkSize n remaining acc =
      acc.reverse ++ (splitListSpec chunkSize n remaining).map List.reverse := by
  induction n generalizing remaining acc with
  | zero => simp [splitListTR, splitListSpec]
  | succ n ih =>
    simp only [splitListTR, splitListSpec]
    split
    · rename_i h; subst h; simp [List.reverse_cons]
    · rename_i h
      simp only [takeNoRev_spec]
      rw [ih]; simp [List.reverse_cons, List.append_assoc]

theorem splitList_eq_spec (numSplits chunkSize : Nat) (l : List α) :
    splitList numSplits chunkSize l =
      (splitListSpec chunkSize (max 1 numSplits) l).map List.reverse := by
  simp [splitList, splitListTR_eq_spec]

/-! ## Length theorem -/

theorem splitListSpec_length (chunkSize : Nat) (n : Nat) (l : List α) :
    (splitListSpec chunkSize n l).length = n := by
  induction n generalizing l with
  | zero => simp [splitListSpec]
  | succ n ih =>
    simp only [splitListSpec]
    split
    · rename_i h; subst h; simp
    · simp [ih]

theorem splitList_length (numSplits chunkSize : Nat) (l : List α) :
    (splitList numSplits chunkSize l).length = max 1 numSplits := by
  rw [splitList_eq_spec, List.length_map, splitListSpec_length]

/-! ## Flatten theorem -/

theorem splitListSpec_flatten (chunkSize : Nat) (n : Nat) (l : List α) (hn : 0 < n) :
    (splitListSpec chunkSize n l).flatten = l := by
  induction n generalizing l with
  | zero => omega
  | succ n ih =>
    simp only [splitListSpec]
    split
    · simp
    · rename_i h
      simp only [List.flatten_cons]
      rw [ih (l.drop chunkSize) (by omega)]
      exact List.take_append_drop chunkSize l

private theorem flatten_map_reverse_perm (ll : List (List α)) :
    List.Perm (ll.map List.reverse).flatten ll.flatten := by
  induction ll with
  | nil => simp
  | cons l ll ih =>
    simp only [List.map_cons, List.flatten_cons]
    exact (List.reverse_perm l).append ih

theorem splitList_flatten (numSplits chunkSize : Nat) (l : List α) :
    List.Perm (splitList numSplits chunkSize l).flatten l := by
  rw [splitList_eq_spec]
  exact (flatten_map_reverse_perm _).trans
    (splitListSpec_flatten _ _ _ (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)) ▸ List.Perm.refl _)

/-! ## Membership theorems -/

theorem splitList_mem_iff (numSplits chunkSize : Nat) (l : List α) (x : α) :
    (∃ chunk ∈ splitList numSplits chunkSize l, x ∈ chunk) ↔ x ∈ l := by
  rw [← List.mem_flatten]
  exact (splitList_flatten numSplits chunkSize l).mem_iff

theorem splitList_mem (numSplits chunkSize : Nat) (l : List α) (x : α) (hx : x ∈ l) :
    ∃ chunk ∈ splitList numSplits chunkSize l, x ∈ chunk :=
  (splitList_mem_iff numSplits chunkSize l x).mpr hx

/-! ## Slice correspondence theorem (spec only) -/

/-- The i-th chunk of `splitListSpec` corresponds to a specific slice of the original list. -/
theorem splitListSpec_getElem (chunkSize : Nat) (n : Nat) (l : List α)
    (i : Nat) (hi : i < n) (hn : 0 < n) :
    (splitListSpec chunkSize n l)[i]'(by rw [splitListSpec_length]; exact hi) =
      if i = n - 1 then l.drop (i * chunkSize)
      else (l.drop (i * chunkSize)).take chunkSize := by
  induction n generalizing l i with
  | zero => omega
  | succ n ih =>
    simp only [splitListSpec]
    split
    · rename_i h_n_zero; subst h_n_zero
      have hi0 : i = 0 := by omega
      subst hi0; simp
    · rename_i h_n_ne_zero
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.zero_mul, List.drop_zero]
        simp [show ¬(0 = n) from by omega]
      | succ i =>
        simp only [List.getElem_cons_succ]
        rw [ih (l.drop chunkSize) i (by omega) (by omega)]
        by_cases h₁ : i = n - 1
        · by_cases h₂ : i + 1 = n + 1 - 1
          · simp only [if_pos h₁, if_pos h₂]
            rw [List.drop_drop]
            congr 1; rw [Nat.succ_mul]; omega
          · exfalso; omega
        · by_cases h₂ : i + 1 = n + 1 - 1
          · exfalso; omega
          · simp only [if_neg h₁, if_neg h₂]
            congr 1; rw [List.drop_drop]
            congr 1; rw [Nat.succ_mul]; omega

/-- The starting index of the i-th chunk. -/
def chunkStart (chunkSize : Nat) (i : Nat) : Nat := i * chunkSize

/-- The ending index of the i-th chunk. -/
def chunkEnd (chunkSize : Nat) (n : Nat) (totalLen : Nat) (i : Nat) : Nat :=
  if i = n - 1 then totalLen else (i + 1) * chunkSize

theorem splitListSpec_getElem_slice (chunkSize : Nat) (n : Nat) (l : List α)
    (i : Nat) (hi : i < n) (hn : 0 < n) :
    let s := chunkStart chunkSize i
    let e := chunkEnd chunkSize n l.length i
    (splitListSpec chunkSize n l)[i]'(by rw [splitListSpec_length]; exact hi) =
      (l.drop s).take (e - s) := by
  simp only [chunkStart, chunkEnd]
  rw [splitListSpec_getElem _ _ _ _ hi hn]
  split
  · rw [show l.length - i * chunkSize = (l.drop (i * chunkSize)).length from by simp]
    exact List.take_length.symm
  · congr 1
    rw [Nat.succ_mul]; omega

/-- The chunk ranges are contiguous: the end of chunk i equals the start of chunk i+1. -/
theorem chunkEnd_eq_next_chunkStart (chunkSize n totalLen i : Nat) (hi : i + 1 < n) :
    chunkEnd chunkSize n totalLen i = chunkStart chunkSize (i + 1) := by
  simp [chunkEnd, chunkStart]; omega

/-- The first chunk starts at 0. -/
theorem chunkStart_zero (chunkSize : Nat) : chunkStart chunkSize 0 = 0 := by
  simp [chunkStart]

/-- The last chunk ends at the list length. -/
theorem chunkEnd_last (chunkSize n totalLen : Nat) :
    chunkEnd chunkSize n totalLen (n - 1) = totalLen := by
  simp [chunkEnd]

/-- Start ≤ End for each chunk range. -/
theorem chunkStart_le_chunkEnd (chunkSize n totalLen i : Nat) (hi : i < n)
    (h_bound : n * chunkSize ≤ totalLen) :
    chunkStart chunkSize i ≤ chunkEnd chunkSize n totalLen i := by
  simp only [chunkStart, chunkEnd]
  split
  · calc i * chunkSize ≤ (n - 1) * chunkSize := by
            apply Nat.mul_le_mul_right; omega
      _ ≤ n * chunkSize := by apply Nat.mul_le_mul_right; omega
      _ ≤ totalLen := h_bound
  · apply Nat.mul_le_mul_right; omega

end ListSplit
