import Lean
import Veil.Frontend.DSL.Module.Names
import Veil.Frontend.DSL.Infra.Simp
open Lean Meta Elab Tactic

namespace Veil

/-- Typeclass that gets inferred if a type is Higher Order. -/
class IsHigherOrder.{u} (t : Sort u)

instance (t₁ t₂ : Type) : IsHigherOrder (t₁ -> t₂) := ⟨⟩
instance (t₁ : Type) (t₂ : Prop) : IsHigherOrder (t₁ -> t₂) := ⟨⟩

def isHigherOrder (e : Expr) : MetaM Bool := do
  let t ← inferType e
  let isHO := (!t.isProp) && (e.isArrow || e.isAppOf stateName || e.isAppOf theoryName)
  return isHO

section EnablerTheorems
theorem if_app {α β : Type} {_ : Decidable c} (t e : α -> β) (a : α) :
  (if c then t else e) a =
  if c then (t a) else (e a) := by
  by_cases c <;> simp_all
end EnablerTheorems

/-! ## Forall Quantifiers -/

section UniversalQuantifierTheorems

/- Shift HO quantifiers left (ensuring you don't go into loops, i.e. if both quantifiers are HO) -/
theorem forall_comm_eq {p : α → β → Prop} : (∀ a b, p a b) = (∀ b a, p a b) := by rw [forall_comm]

/- `∀ a b, p a b` => `∀ b a, p a b` _iff_ `b` is HO and `a` is NOT -/
def HO_forall_push_left_impl : Simp.Simproc := fun e => do
  match e with
  | Expr.forallE _ t (Expr.forallE _ t' _ .default) .default =>
    if (← isHigherOrder t') && !(← isHigherOrder t) then
      let step ← forallBoundedTelescope e (maxFVars? := some 2) (fun ks body' => do
        let e' ← mkForallFVars ks.reverse body'
        let body ← mkLambdaFVars ks body'
        let proof ← mkAppOptM ``forall_comm_eq #[t, t', body]
        return .visit { expr := e', proof? := proof }
      )
      return step
    else
      return .continue
  | _ => return .continue

simproc HO_forall_push_left (∀_ _, _) := HO_forall_push_left_impl
attribute [quantifierSimp] HO_forall_push_left

attribute [quantifierSimp] forall_const forall_eq forall_eq

-- To enable some of the lemmas below; FIXME: do we need more of these?
-- attribute [quantifierSimp] and_imp not_and

section forall_and
set_option linter.unusedSectionVars false
open Classical
variable [IsHigherOrder α] [ne : Nonempty α] {p q : α → Prop} {b : Prop}

/-! Hoist `∀` quantifiers to the top of the goal. -/
theorem forall_and_on_the_left : b ∧ (∀ x, p x) ↔ (∀ x, b ∧ p x) := by
  constructor
  { simp_all only [and_self, implies_true] }
  {
    simp_all only [implies_true, and_true]
    intro h; rcases h (Classical.choice ne) with ⟨hb, _⟩
    assumption
  }

theorem forall_and_on_the_right : (∀ x, p x) ∧ b ↔ (∀ x, p x ∧ b) := by
  simp only [and_comm, forall_and_on_the_left]

attribute [quantifierSimp] forall_and_on_the_left forall_and_on_the_right
end forall_and

section forall_imp
set_option linter.unusedSectionVars false
-- `α : Type` because we don't want this to apply to `α := Prop`
variable {α : Type} [IsHigherOrder α] {p : α → Prop} {b : Prop}

theorem forall_imp_left : b → (∀ x, p x) ↔ (∀ x, b → p x) := by
  constructor
  { intro h x hb; exact h hb x }
  { intro h hb x; exact h x hb }

attribute [quantifierSimp] forall_imp_left
end forall_imp

section IteForallPushOutTheorems
open Classical

open Lean Elab Tactic in
elab "prove_ite_forall_push_out" p:term : tactic => withMainContext do evalTactic $ ←
`(tactic|apply propext; by_cases h : $p; { simp only [if_pos h, forall_const] }; { simp only [if_neg h, forall_const] })

theorem ite_then_forall_push_out [IsHigherOrder α] [ne : Nonempty α] (c r : Prop) (q : α → Prop) : (if c then ∀ t, q t else r) = (∀ t, if c then q t else r) := by prove_ite_forall_push_out c
attribute [quantifierSimp] ite_then_forall_push_out

theorem ite_else_forall_push_out [IsHigherOrder α] [ne : Nonempty α] (c r : Prop) (q : α → Prop) : (if c then r else ∀ t, q t) = (∀ t, if c then r else q t) := by prove_ite_forall_push_out c
attribute [quantifierSimp] ite_else_forall_push_out

-- FIXME George: does this trigger?
theorem ite_both_forall_push_out [IsHigherOrder α] [ne : Nonempty α] [ne' : Nonempty β] (p : α → Prop) (q : β → Prop) :
  (if c then ∀ a, p a else ∀ b, q b) = (∀ (a : α) (b : β), if c then p a else q b) := by prove_ite_forall_push_out c
attribute [quantifierSimp] ite_both_forall_push_out
end IteForallPushOutTheorems


attribute [quantifierSimp] if_false_left if_false_right if_app
attribute [quantifierSimp] and_imp Classical.not_imp and_self eq_self ne_eq implies_true false_implies
attribute [quantifierSimp] and_true true_and and_false false_and or_true
  true_or or_false false_or iff_true true_iff iff_false false_iff

end UniversalQuantifierTheorems


end Veil
