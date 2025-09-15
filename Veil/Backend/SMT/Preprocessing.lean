import Lean
import Batteries.Lean.Meta.UnusedNames
import Veil.Backend.SMT.Base

open Lean Meta Elab Tactic

namespace Veil

theorem funextEq' {α β : Type} (f g : α → β) :
  (f = g) = ∀ x, f x = g x := by
  apply propext
  constructor
  { intro h ; simp only [h, implies_true] }
  { intro h ; apply funext h }

open Lean Expr Lean.Meta in

/-- Applies functional extensionality to all equalities between functions. -/
simproc ↓ funextEq (_ = _) :=
  fun e => do
  let_expr Eq _ lhs rhs := e | return .continue
  let lhsT ← inferType lhs
  if lhsT.isArrow && (← inferType rhs).isArrow then
    -- NOTE: this cannot be `anonymous` because it is used in the SMT-LIB
    -- translation, which gets confused in the presence of multiple anonymous
    -- binders. TODO: generate a more informative name.
    let bn ← getUnusedUserName `a
    let bt := lhsT.bindingDomain!
    let nlhs := app lhs (bvar 0)
    let nrhs := app rhs (bvar 0)
    let qexpr := forallE bn bt (← mkEq nlhs nrhs) BinderInfo.default
    let proof ← mkAppM ``funextEq' #[lhs, rhs]
    return .visit { expr := qexpr, proof? := proof }
  return .continue
attribute [smtSimp] funextEq

/-- Tuples are not supported in SMT-LIB, so we destruct tuple equalities. -/
@[smtSimp] theorem tupleEq [DecidableEq t1] [DecidableEq t2] (a c : t1) (b d : t2):
  ((a, b) = (c, d)) = (a = c ∧ b = d) := by
  apply propext; constructor
  { intro h ; injection h ; constructor <;> assumption }
  { rintro ⟨h1, h2⟩ ; rw [h1, h2] }

/-- Tuples are not supported in SMT-LIB, so we destruct quantifiers over tuples. -/
@[smtSimp] theorem tupleForall {P : α × β → Prop}:
  (∀ (x : α × β), P x) = (∀ (a: α) (b : β), P (a, b)) := by
  apply propext; constructor
  { rintro h a b ; exact h (a, b) }
  { rintro h ⟨a, b⟩ ; exact h a b }

/-- Tuples are not supported in SMT-LIB, so we destruct quantifiers over tuples. -/
@[smtSimp] theorem tupleExists {P : α × β → Prop}:
  (∃ (x : α × β), P x) = (∃ (a: α) (b : β), P (a, b)) := by
  apply propext; constructor
  { rintro ⟨⟨a, b⟩, h⟩ ; exact ⟨a, b, h⟩ }
  { rintro ⟨a, b, h⟩ ; exact ⟨⟨a, b⟩, h⟩ }


attribute [smtSimp] exists_prop forall_const
attribute [smtSimp] decide_eq_true_eq decide_eq_false_iff_not

-- If-then-else simplification lemmas
attribute [smtSimp] ite_true ite_false dite_true dite_false ite_self
  if_true_left if_true_right if_false_left if_false_right

end Veil
