import Std
import Batteries.Tactic.Trans

namespace Std.TreeSet

/-- Wrapper that provides `ForIn m ρ (α × Unit)` given `ForIn m ρ α`,
    yielding `(a, ())` pairs lazily without allocating an intermediate collection. -/
structure WithUnit (ρ : Type u) where
  inner : ρ

@[inline] instance WithUnit.ForIn [ForIn m ρ α] : ForIn m (WithUnit ρ) (α × Unit) where
  forIn l init f :=
    ForIn.forIn l.inner init fun a acc => f (a, ()) acc

/-- A faster `TreeSet.insertMany` that uses single-pass `insert` (via `TreeMap.insertMany`)
    instead of double-pass `insertIfNew`. Accepts any `ForIn`-compatible collection. -/
@[inline] def insertManyFast {ρ : Type u} [ForIn Id ρ α]
    (t : Std.TreeSet α cmp) (l : ρ) : Std.TreeSet α cmp :=
  ⟨Std.TreeMap.insertMany t.inner (WithUnit.mk l)⟩

/-- A faster `TreeSet.ofList` that uses single-pass `insert` instead of double-pass `insertIfNew`. -/
@[inline] def ofListFast (l : List α) (cmp : α → α → Ordering := by exact compare) :
    Std.TreeSet α cmp :=
  insertManyFast ∅ l

section InsertManyFastLemmas

variable {α : Type u} {cmp : α → α → Ordering} [Std.TransCmp cmp] [BEq α] [Std.LawfulBEqCmp cmp]

theorem contains_insertManyFast_list
    {t : Std.TreeSet α cmp} {l : List α} {k : α} :
    (t.insertManyFast l).contains k = (t.contains k || l.contains k) := by
  rw [← contains_insertMany_list (t := t) (l := l) (k := k)]
  dsimp only [insertManyFast, TreeMap.insertMany, DTreeMap.Const.insertMany,
    DTreeMap.Internal.Impl.Const.insertMany, WithUnit.ForIn,
    insertMany, TreeMap.insertManyIfNewUnit, DTreeMap.Const.insertManyIfNewUnit,
    DTreeMap.Internal.Impl.Const.insertManyIfNewUnit, DTreeMap.Internal.Impl.insertIfNew,
    contains, DTreeMap.contains, TreeMap.contains]
  simp ; repeat rw [List.foldl_eq_foldr_reverse]
  generalize l.reverse = l' ; clear l
  induction l' generalizing k with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr]
    rw [Std.DTreeMap.Internal.Impl.contains_insert]
    · rw [← ih] ; split
      next h =>
        dsimp only ; rw [← ih]
        rcases hcmp : cmp a k == Ordering.eq
        · rfl
        · simp at hcmp ⊢ ; rw [Std.DTreeMap.Internal.Impl.contains_congr]
          · exact h
          · clear ih h hcmp ; induction l with
            | nil => exact t.inner.inner.wf
            | cons a l ih =>
              dsimp only [List.foldr]
              let : Ord α := ⟨cmp⟩
              apply Std.DTreeMap.Internal.Impl.WF.insert ; exact ih
          · simp ; rw [OrientedCmp.eq_comm] ; exact hcmp
      next h =>
        rw [Std.DTreeMap.Internal.Impl.contains_insert]
        · rw [← ih]
        · -- NOTE: This is repeating, but clearing the repeating is not very easy? So just keep it now
          clear h ih ; induction l with
          | nil => exact t.inner.inner.wf
          | cons a l ih =>
            dsimp only [List.foldr]
            let : Ord α := ⟨cmp⟩
            split
            · exact ih
            · apply Std.DTreeMap.Internal.Impl.WF.insert ; exact ih
    · clear ih ; induction l with
      | nil => exact t.inner.inner.wf
      | cons a l ih =>
        dsimp only [List.foldr]
        let : Ord α := ⟨cmp⟩
        apply Std.DTreeMap.Internal.Impl.WF.insert ; exact ih

-- NOTE: Write `l.contains k = true` since making it equivalent to `k ∈ l` would require `LawfulBEq α`
theorem mem_insertManyFast_list {t : Std.TreeSet α cmp} {l : List α} {k : α} :
    k ∈ t.insertManyFast l ↔ k ∈ t ∨ l.contains k = true := by
  grind [contains_insertManyFast_list]

theorem mem_ofListFast {l : List α} {k : α} :
    k ∈ Std.TreeSet.ofListFast l cmp ↔ l.contains k = true := by
  simp [Std.TreeSet.ofListFast, mem_insertManyFast_list]

end InsertManyFastLemmas

end Std.TreeSet
