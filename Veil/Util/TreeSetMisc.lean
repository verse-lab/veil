module

public import Std
meta import Batteries.Tactic.Trans

public section

namespace Std.TreeSet

/-- `TreeSet.insertMany` on a `HashSet` is equal to `TreeSet.insertMany` on the `HashSet`'s `toList`.
    This follows from the fact that `forIn` on a `HashSet` is equivalent to `forIn` on its `toList`. -/
theorem insertMany_hashset_eq_insertMany_toList {α : Type u} {cmp : α → α → Ordering} [BEq α] [Hashable α]
  {t : Std.TreeSet α cmp} {hs : Std.HashSet α} :
  t.insertMany hs = t.insertMany hs.toList := by
  unfold Std.TreeSet.insertMany Std.TreeMap.insertManyIfNewUnit Std.DTreeMap.Const.insertManyIfNewUnit
    Std.DTreeMap.Internal.Impl.Const.insertManyIfNewUnit
  grind [Std.HashSet.forIn_eq_forIn_toList]

/-- Wrapper that provides `ForIn m ρ (α × Unit)` given `ForIn m ρ α`,
    yielding `(a, ())` pairs lazily without allocating an intermediate collection. -/
structure WithUnit (ρ : Type u) where
  inner : ρ

@[inline] instance WithUnit.ForIn [ForIn m ρ α] : ForIn m (WithUnit ρ) (α × Unit) where
  forIn l init f :=
    ForIn.forIn l.inner init fun a acc => f (a, ()) acc

/-- A faster `TreeSet.insertMany` that uses single-pass `insert` (via `TreeMap.insertMany`)
    instead of double-pass `insertIfNew`. Accepts any `ForIn`-compatible collection. -/
@[inline, specialize] def insertManyFast {ρ : Type u} [ForIn Id ρ α]
    (t : Std.TreeSet α cmp) (l : ρ) : Std.TreeSet α cmp :=
  ⟨Std.TreeMap.insertMany t.inner (WithUnit.mk l)⟩

/-- A faster `TreeSet.ofList` that uses single-pass `insert` instead of double-pass `insertIfNew`. -/
@[specialize] def ofListFast (l : List α) (cmp : α → α → Ordering := by exact compare) :
    Std.TreeSet α cmp :=
  insertManyFast ∅ l

@[specialize] def ofArrayFast (arr : Array α) (cmp : α → α → Ordering := by exact compare) :
    Std.TreeSet α cmp :=
  insertManyFast ∅ arr

theorem insertManyFast_array_eq_insertManyFast_toList {α : Type u} {cmp : α → α → Ordering} [BEq α]
    {t : Std.TreeSet α cmp} {arr : Array α} :
    t.insertManyFast arr = t.insertManyFast arr.toList := by
  simp +instances only [insertManyFast, TreeMap.insertMany, DTreeMap.Const.insertMany,
    DTreeMap.Internal.Impl.Const.insertMany, WithUnit.ForIn]
  simp only [Array.forIn_toList]

theorem insertManyFast_hashset_eq_insertManyFast_toList {α : Type u} {cmp : α → α → Ordering} [BEq α] [Hashable α]
    {t : Std.TreeSet α cmp} {hs : Std.HashSet α} :
    t.insertManyFast hs = t.insertManyFast hs.toList := by
  simp +instances only [insertManyFast, TreeMap.insertMany, DTreeMap.Const.insertMany,
    DTreeMap.Internal.Impl.Const.insertMany, WithUnit.ForIn,
    Std.HashSet.forIn_eq_forIn_toList]

section InsertManyFastLemmas

variable {α : Type u} {cmp : α → α → Ordering} [BEq α] [Std.TransCmp cmp] [Std.LawfulBEqCmp cmp]

theorem contains_insertManyFast_list
    {t : Std.TreeSet α cmp} {l : List α} {k : α} :
    (t.insertManyFast l).contains k = (t.contains k || l.contains k) := by
  have h : t.insertManyFast l = ⟨Std.TreeMap.insertMany t.inner (l.map (·, ()))⟩ := by
    simp +instances only [insertManyFast, TreeMap.insertMany, DTreeMap.Const.insertMany,
      DTreeMap.Internal.Impl.Const.insertMany, WithUnit.ForIn, List.forIn_map]
  rw [h]
  show (Std.TreeMap.insertMany t.inner (l.map (·, ()))).contains k = (t.inner.contains k || l.contains k)
  rw [Std.TreeMap.contains_insertMany_list, List.map_map]
  congr 2
  exact List.map_id'' (fun _ => rfl) l

-- NOTE: Write `l.contains k = true` since making it equivalent to `k ∈ l` would require `LawfulBEq α`
theorem mem_insertManyFast_list {t : Std.TreeSet α cmp} {l : List α} {k : α} :
    k ∈ t.insertManyFast l ↔ k ∈ t ∨ l.contains k = true := by
  grind [contains_insertManyFast_list]

theorem mem_ofListFast {l : List α} {k : α} :
    k ∈ Std.TreeSet.ofListFast l cmp ↔ l.contains k = true := by
  simp [Std.TreeSet.ofListFast, mem_insertManyFast_list]

theorem mem_ofArrayFast {l : Array α} {k : α} :
    k ∈ Std.TreeSet.ofArrayFast l cmp ↔ l.contains k = true := by
  dsimp [Std.TreeSet.ofArrayFast]
  simp [insertManyFast_array_eq_insertManyFast_toList, mem_insertManyFast_list]

theorem mem_insertManyFast_hashset [Hashable α] [LawfulBEq α]
    {t : Std.TreeSet α cmp} {hs : Std.HashSet α} {k : α} :
    k ∈ t.insertManyFast hs ↔ k ∈ t ∨ hs.contains k = true := by
  simp [insertManyFast_hashset_eq_insertManyFast_toList, mem_insertManyFast_list, Std.HashSet.mem_toList]

end InsertManyFastLemmas

end Std.TreeSet
