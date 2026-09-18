/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
Adapted from `Mathlib.Logic.Equiv.Defs` and `Mathlib.Logic.Equiv.Prod`; the
`Function` definitions come from `Mathlib.Logic.Function.Defs` ((c) 2014
Microsoft Corporation; authors: Leonardo de Moura, Jeremy Avigad, Haitao
Zhang). Only what Veil's finite encodings need.
-/
import Lean
import Aesop
import Batteries

/-! Small equivalences used by Veil's concrete state representations. -/
namespace Veil

namespace Function
abbrev Injective (f : α → β) := ∀ ⦃a b⦄, f a = f b → a = b
abbrev LeftInverse (g : β → α) (f : α → β) := ∀ a, g (f a) = a
abbrev RightInverse (g : β → α) (f : α → β) := LeftInverse f g
end Function

@[ext] structure Equiv (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun

scoped infix:25 " ≃ " => Equiv

namespace Equiv
instance : CoeFun (Equiv α β) (fun _ => α → β) := ⟨Equiv.toFun⟩
@[simp] theorem toFun_as_coe (e : α ≃ β) : e.toFun = e := rfl
@[simp] theorem coe_fn_mk (f : α → β) (g h k) : (Equiv.mk f g h k : α → β) = f := rfl
@[inline] def refl (α : Sort u) : α ≃ α := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
@[inline] def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩
@[inline] def trans (e : α ≃ β) (f : β ≃ γ) : α ≃ γ :=
  ⟨fun x => f (e x), fun x => e.symm (f.symm x),
   fun x => by simp [symm, f.left_inv, e.left_inv],
   fun x => by simp [symm, e.right_inv, f.right_inv]⟩
@[simp, grind =] theorem symm_apply_apply (e : α ≃ β) (a : α) : e.symm (e a) = a := e.left_inv a
@[simp, grind =] theorem apply_symm_apply (e : α ≃ β) (b : β) : e (e.symm b) = b := e.right_inv b
@[simp] theorem invFun_as_coe (e : α ≃ β) : e.invFun = e.symm := rfl
theorem injective (e : α ≃ β) : Function.Injective e := by
  intro a b h
  simpa only [symm_apply_apply] using congrArg e.symm h
@[simp] theorem apply_eq_iff_eq (e : α ≃ β) {a b : α} : e a = e b ↔ a = b :=
  ⟨fun h => e.injective h, congrArg e⟩
theorem apply_eq_iff_eq_symm_apply (e : α ≃ β) {a : α} {b : β} : e a = b ↔ a = e.symm b := by
  constructor <;> intro h
  · rw [← h, symm_apply_apply]
  · rw [h, apply_symm_apply]
theorem symm_apply_eq (e : α ≃ β) {a : α} {b : β} : e.symm b = a ↔ b = e a := by
  rw [apply_eq_iff_eq_symm_apply]; rfl
@[inline] def sigmaEquivProd (α : Type u) (β : Type v) : (Sigma fun _ : α => β) ≃ (α × β) :=
  ⟨fun x => (x.1, x.2), fun x => ⟨x.1, x.2⟩, fun _ => rfl, fun _ => rfl⟩
end Equiv
end Veil
