import Veil.Util.Tactics

/-! List operations and completeness facts for executable finite enumeration. -/
namespace Veil.List

/-- Functions over a finite list, preserving the caller's candidate order. -/
def pi [DecidableEq ι] {α : ι → Type v} :
    (l : List ι) → (∀ i, List (α i)) → List (∀ i, i ∈ l → α i)
  | [], _ => [fun _ h => nomatch h]
  | i :: l, fs => (fs i).flatMap fun a => (pi l fs).map fun f j h =>
      if e : j = i then e ▸ a else f j (by simpa [e] using h)

theorem mem_pi [DecidableEq ι] {α : ι → Type v} {l : List ι}
    (fs : ∀ i, List (α i)) (f : ∀ i, i ∈ l → α i) :
    f ∈ pi l fs ↔ ∀ i h, f i h ∈ fs i := by
  induction l with
  | nil => simp [pi]; funext i h; cases h
  | cons i l ih =>
    simp only [pi, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨a, ha, g, hg, rfl⟩ j hj
      dsimp only
      split
      · rename_i e; subst j; exact ha
      · exact (ih g).mp hg j _
    · intro h
      refine ⟨f i (by simp), h i _, (fun j hj => f j (by simp [hj])), (ih _).mpr (fun j hj => h j _), ?_⟩
      funext j hj
      split
      · rename_i e; subst j; rfl
      · rfl
end Veil.List

namespace List
@[simp] theorem mem_sublists {s t : List α} : s ∈ sublists t ↔ s.Sublist t := by
  induction t generalizing s with
  | nil => simp [sublists]
  | cons a t ih =>
    simp only [sublists, foldr_cons, mem_flatMap, mem_cons, not_mem_nil, or_false]
    constructor
    · rintro ⟨x, hx, rfl | rfl⟩
      · exact (ih.mp hx).cons a
      · exact (ih.mp hx).cons_cons a
    · intro h
      cases h with
      | cons _ h => exact ⟨s, ih.mpr h, Or.inl rfl⟩
      | cons_cons _ h => exact ⟨_, ih.mpr h, Or.inr rfl⟩
end List

namespace Veil.List
/-- Remove duplicate candidates, retaining their last occurrences. -/
def dedup [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => if a ∈ l then dedup l else a :: dedup l
@[simp] theorem mem_dedup [DecidableEq α] {a : α} {l : List α} : a ∈ dedup l ↔ a ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons b l ih => simp only [dedup]; split <;> simp_all
@[simp] theorem nodup_dedup [DecidableEq α] (l : List α) : (dedup l).Nodup := by
  induction l with
  | nil => simp [dedup]
  | cons a l ih => simp only [dedup]; split <;> simp_all
end Veil.List

namespace List
/-- Counting two predicates never exceeds the universe plus their overlap. -/
theorem filter_count_overlap (l : List α) (p q : α → Bool) :
    (l.filter p).length + (l.filter q).length ≤
      l.length + (l.filter (fun a => p a && q a)).length := by
  induction l with
  | nil => simp
  | cons a l ih => cases hp : p a <;> cases hq : q a <;> simp [hp, hq] <;> omega

theorem filter_count_mono (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a → q a) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ht := ih (fun b hb => h b (by simp [hb]))
    have ha := h a (by simp)
    cases hp : p a <;> cases hq : q a <;> (simp_all; all_goals omega)

theorem Pairwise.nodup {r : α → α → Prop} [Std.Irrefl r] {l : List α}
    (h : l.Pairwise r) : l.Nodup :=
  h.imp (fun {a b} hab heq => by subst b; exact Std.Irrefl.irrefl a hab)

theorem sublist_of_subperm_of_pairwise {r : α → α → Prop} [Std.Antisymm r]
    {l₁ l₂ : List α} (hp : l₁.Subperm l₂)
    (hs₁ : l₁.Pairwise r) (hs₂ : l₂.Pairwise r) : l₁.Sublist l₂ := by
  obtain ⟨l, h, h'⟩ := hp
  have heq := h.eq_of_pairwise (fun _ _ _ _ => Std.Antisymm.antisymm _ _) (hs₂.sublist h') hs₁
  exact heq ▸ h'

theorem Pairwise.eq_of_mem_iff {r : α → α → Prop} [Std.Antisymm r] [Std.Irrefl r]
    {l₁ l₂ : List α} (h₁ : l₁.Pairwise r) (h₂ : l₂.Pairwise r)
    (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ :=
  ((perm_ext_iff_of_nodup h₁.nodup h₂.nodup).mpr h).eq_of_pairwise
    (fun _ _ _ _ => Std.Antisymm.antisymm _ _) h₁ h₂
end List

namespace List
theorem nodup_flatMap {l : List α} {f : α → List β} :
    (l.flatMap f).Nodup ↔ (∀ x ∈ l, (f x).Nodup) ∧
      l.Pairwise (fun a b => ∀ x ∈ f a, x ∉ f b) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [flatMap_cons, nodup_append, ih, forall_mem_cons, pairwise_cons]
    simp only [mem_flatMap]
    aesop
end List

namespace List
theorem Nodup.filter (p : α → Bool) {l : List α} (h : l.Nodup) : (l.filter p).Nodup :=
  h.sublist (List.filter_sublist)
end List
