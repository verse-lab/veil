/-
Adapted from mathlib; only what Veil's sorted-list operations need. All rights
reserved by the respective copyright holders; released under Apache 2.0 license
as described in LICENSE.

* `destutter`/`destutter'` come from `Mathlib.Data.List.Defs` -- (c) 2014
  Parikshit Khanna. Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de
  Moura, Floris van Doorn, Mario Carneiro
* their lemmas come from `Mathlib.Data.List.Destutter` -- (c) 2022 Eric
  Rodriguez. Authors: Eric Rodriguez, Eric Wieser
-/
import Veil.Util.List

namespace Veil.List

open _root_.List

def destutter' (R : α → α → Prop) [DecidableRel R] : α → List α → List α
  | a, [] => [a]
  | a, b :: l => if R a b then a :: destutter' R b l else destutter' R a l

def destutter (R : α → α → Prop) [DecidableRel R] : List α → List α
  | [] => []
  | a :: l => destutter' R a l

variable (R : α → α → Prop) [DecidableRel R]
@[simp] theorem destutter'_nil (a : α) : destutter' R a [] = [a] := rfl
@[simp] theorem destutter'_cons (a b : α) (l : List α) :
    destutter' R a (b :: l) = if R a b then a :: destutter' R b l else destutter' R a l := rfl
@[simp] theorem destutter_cons' (a : α) (l : List α) :
    destutter R (a :: l) = destutter' R a l := rfl

theorem destutter'_sublist (l : List α) (a : α) : destutter' R a l <+ a :: l := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [destutter'_cons]
    split
    · exact (ih b).cons_cons a
    · exact (ih a).trans ((sublist_cons_self b l).cons_cons a)

theorem destutter_sublist (l : List α) : destutter R l <+ l := by
  cases l with
  | nil => exact .refl _
  | cons a l => exact destutter'_sublist R l a

theorem mem_destutter' (l : List α) (a : α) : a ∈ destutter' R a l := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp only [destutter'_cons]; split <;> simp_all

private theorem destutter'_pairwise [Trans R R R] (l : List α) (a : α) :
    (destutter' R a l).Pairwise R ∧ ∀ b ∈ destutter' R a l, b = a ∨ R a b := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [destutter'_cons]
    split
    · rename_i hab
      have hb := ih b
      constructor
      · apply List.pairwise_cons.mpr
        exact ⟨fun c hc => (hb.2 c hc).elim (fun e => e ▸ hab) (fun hbc => Trans.trans hab hbc), hb.1⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact .inl rfl
        · exact .inr ((hb.2 c hc).elim (fun e => e ▸ hab) (fun hbc => Trans.trans hab hbc))
    · exact ih a

theorem pairwise_destutter [Trans R R R] (l : List α) : (destutter R l).Pairwise R := by
  cases l with
  | nil => exact .nil
  | cons a l => exact (destutter'_pairwise R l a).1

end Veil.List
