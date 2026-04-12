import Mathlib.Tactic.Common

/-!
# List Splitting

A pure, tail-recursive function that splits a `List α` into `max 1 numSplits`
disjoint parts with a fair distribution: the first `numLarge` parts get
`chunkSize + 1` elements and the rest get `chunkSize` elements.

Each chunk is produced in **reversed** order relative to the natural reading order;
this is acceptable for consumers (like BFS) that only care about membership, not ordering.

We prove that the flattened result is a permutation of the original list, which
is sufficient for all downstream membership-based reasoning.
-/

namespace ListSplit

/-! ## Definitions -/

/-- Non-tail-recursive specification function. Splits a list into `n` parts.
The first `numLarge` parts have `chunkSize + 1` elements; the rest have `chunkSize`.
The last part always gets all remaining elements. -/
def splitListSpec (chunkSize numLarge : Nat) : (n : Nat) → List α → List (List α)
  | 0, _ => []
  | n + 1, remaining =>
    let curSize := if numLarge > 0 then chunkSize + 1 else chunkSize
    if n = 0 then [remaining]
    else (remaining.take curSize) :: splitListSpec chunkSize (numLarge - 1) n (remaining.drop curSize)

/-- Like `List.splitAt` but without reversing the first component.
    Equivalent to `(l.take n |>.reverse, l.drop n)` but computed in a single pass. -/
def takeNoRev (n : Nat) (l : List α) : List α × List α := go l n [] where
  go : List α → Nat → List α → List α × List α
  | [],       _,   acc => (acc, [])
  | x :: xs,  n+1, acc => go xs n (x :: acc)
  | xs,       _,   acc => (acc, xs)

/-- Tail-recursive implementation using single-pass chunk extraction.
    Each chunk is produced in reversed order relative to `splitListSpec`. -/
def splitListTR (chunkSize numLarge : Nat) : (n : Nat) → List α → List (List α) → List (List α)
  | 0, _, acc => acc.reverse
  | n + 1, remaining, acc =>
    let curSize := if numLarge > 0 then chunkSize + 1 else chunkSize
    if n = 0 then (remaining.reverse :: acc).reverse
    else
      let (chunk, rest) := takeNoRev curSize remaining
      splitListTR chunkSize (numLarge - 1) n rest (chunk :: acc)

/-- Split a list into `max 1 numSplits` disjoint parts.
    The first `numLarge` parts get `chunkSize + 1` elements; the rest get `chunkSize`. -/
def splitList (numSplits : Nat) (chunkSize numLarge : Nat) (l : List α) : List (List α) :=
  let n := max 1 numSplits
  splitListTR chunkSize numLarge n l []

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
theorem splitListTR_eq_spec (chunkSize numLarge : Nat) (n : Nat) (remaining : List α)
    (acc : List (List α)) :
    splitListTR chunkSize numLarge n remaining acc =
      acc.reverse ++ (splitListSpec chunkSize numLarge n remaining).map List.reverse := by
  induction n generalizing numLarge remaining acc with
  | zero => simp [splitListTR, splitListSpec]
  | succ n ih =>
    simp only [splitListTR, splitListSpec]
    split
    · rename_i h; subst h; simp [List.reverse_cons]
    · rename_i h
      simp only [takeNoRev_spec]
      rw [ih]; simp [List.reverse_cons, List.append_assoc]

theorem splitList_eq_spec (numSplits chunkSize numLarge : Nat) (l : List α) :
    splitList numSplits chunkSize numLarge l =
      (splitListSpec chunkSize numLarge (max 1 numSplits) l).map List.reverse := by
  simp [splitList, splitListTR_eq_spec]

/-! ## Length theorem -/

theorem splitListSpec_length (chunkSize numLarge : Nat) (n : Nat) (l : List α) :
    (splitListSpec chunkSize numLarge n l).length = n := by
  induction n generalizing numLarge l with
  | zero => simp [splitListSpec]
  | succ n ih =>
    simp only [splitListSpec]
    split
    · rename_i h; subst h; simp
    · simp [ih]

theorem splitList_length (numSplits chunkSize numLarge : Nat) (l : List α) :
    (splitList numSplits chunkSize numLarge l).length = max 1 numSplits := by
  rw [splitList_eq_spec, List.length_map, splitListSpec_length]

/-! ## Flatten theorem -/

theorem splitListSpec_flatten (chunkSize numLarge : Nat) (n : Nat) (l : List α) (hn : 0 < n) :
    (splitListSpec chunkSize numLarge n l).flatten = l := by
  induction n generalizing numLarge l with
  | zero => omega
  | succ n ih =>
    simp only [splitListSpec]
    split
    · simp
    · rename_i h
      simp only [List.flatten_cons]
      rw [ih (numLarge - 1) (l.drop _) (by omega)]
      exact List.take_append_drop _ l

private theorem flatten_map_reverse_perm (ll : List (List α)) :
    List.Perm (ll.map List.reverse).flatten ll.flatten := by
  induction ll with
  | nil => simp
  | cons l ll ih =>
    simp only [List.map_cons, List.flatten_cons]
    exact (List.reverse_perm l).append ih

theorem splitList_flatten (numSplits chunkSize numLarge : Nat) (l : List α) :
    List.Perm (splitList numSplits chunkSize numLarge l).flatten l := by
  rw [splitList_eq_spec]
  exact (flatten_map_reverse_perm _).trans
    (splitListSpec_flatten _ _ _ _ (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)) ▸ List.Perm.refl _)

/-! ## Membership theorems -/

theorem splitList_mem_iff (numSplits chunkSize numLarge : Nat) (l : List α) (x : α) :
    (∃ chunk ∈ splitList numSplits chunkSize numLarge l, x ∈ chunk) ↔ x ∈ l := by
  rw [← List.mem_flatten]
  exact (splitList_flatten numSplits chunkSize numLarge l).mem_iff

theorem splitList_mem (numSplits chunkSize numLarge : Nat) (l : List α) (x : α) (hx : x ∈ l) :
    ∃ chunk ∈ splitList numSplits chunkSize numLarge l, x ∈ chunk :=
  (splitList_mem_iff numSplits chunkSize numLarge l x).mpr hx

end ListSplit
