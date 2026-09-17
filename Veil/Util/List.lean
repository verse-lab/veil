/-
Adapted from mathlib. All rights reserved by the respective copyright holders;
released under Apache 2.0 license as described in LICENSE. Sources, with their
upstream copyright lines; see `Veil/Util/README.md` for which declaration came
from where:

* `Mathlib.Data.List.Pi` -- (c) 2023 Yuyang Zhao. Authors: Yuyang Zhao
* `Mathlib.Data.List.Defs` -- (c) 2014 Parikshit Khanna. Authors: Parikshit
  Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
* `Mathlib.Data.List.Dedup` -- (c) 2018 Mario Carneiro. Authors: Mario Carneiro
* `Mathlib.Data.List.Sublists` -- (c) 2019 Mario Carneiro. Authors: Mario Carneiro
* `Mathlib.Data.List.Nodup` -- (c) 2018 Mario Carneiro. Authors: Mario Carneiro,
  Kenny Lau
* `Mathlib.Data.List.Sort` -- (c) 2016 Jeremy Avigad. Authors: Jeremy Avigad,
  Wrenna Robson
-/
import Veil.Util.Tactics

namespace Veil.List

open _root_.List

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

theorem nodup_of_pairwise {r : α → α → Prop} [Std.Irrefl r] {l : List α}
    (h : l.Pairwise r) : l.Nodup :=
  h.imp (fun {a b} hab heq => by subst b; exact Std.Irrefl.irrefl a hab)

theorem sublist_of_subperm_of_pairwise {r : α → α → Prop} [Std.Antisymm r]
    {l₁ l₂ : List α} (hp : l₁.Subperm l₂)
    (hs₁ : l₁.Pairwise r) (hs₂ : l₂.Pairwise r) : l₁.Sublist l₂ := by
  obtain ⟨l, h, h'⟩ := hp
  have heq := h.eq_of_pairwise (fun _ _ _ _ => Std.Antisymm.antisymm _ _) (hs₂.sublist h') hs₁
  exact heq ▸ h'

theorem eq_of_pairwise_of_mem_iff {r : α → α → Prop} [Std.Antisymm r] [Std.Irrefl r]
    {l₁ l₂ : List α} (h₁ : l₁.Pairwise r) (h₂ : l₂.Pairwise r)
    (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ :=
  ((perm_ext_iff_of_nodup (nodup_of_pairwise h₁) (nodup_of_pairwise h₂)).mpr h).eq_of_pairwise
    (fun _ _ _ _ => Std.Antisymm.antisymm _ _) h₁ h₂

theorem nodup_flatMap {l : List α} {f : α → List β} :
    (l.flatMap f).Nodup ↔ (∀ x ∈ l, (f x).Nodup) ∧
      l.Pairwise (fun a b => ∀ x ∈ f a, x ∉ f b) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [flatMap_cons, nodup_append, ih, forall_mem_cons, pairwise_cons]
    simp only [mem_flatMap]
    aesop

theorem nodup_filter (p : α → Bool) {l : List α} (h : l.Nodup) : (l.filter p).Nodup :=
  h.sublist (List.filter_sublist)

end Veil.List
