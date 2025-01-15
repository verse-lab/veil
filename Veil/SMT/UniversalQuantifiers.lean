import Lean

import Veil.Basic
import Veil.DSL.Util
import Veil.SMT.Preparation

open Lean

private def skipTopLevel [MonadControlT MetaM n] [Monad n] {α : Type} (type : Expr) (k : Array Expr → Expr → n α) (cleanupAnnotations : Bool := false) := do
  match type with
  | Expr.forallE _ _ b _   => do skipTopLevel b k cleanupAnnotations
  | Expr.lam _ _ b _       => do skipTopLevel b k cleanupAnnotations
  | Expr.letE _ _ _ b _    => do skipTopLevel b k cleanupAnnotations
  | _                      => k #[] type

/-- Check if the given type `t` has ALL `∀` quantification over type with
name `overT` at the top-level (and none in the body). -/
def hasOnlyTopLevelForAll (t : Expr) (overT : Name) : MetaM Bool := do
  let t ← Meta.reduceAll t
  -- Meta.forallTelescopeReducing t fun _ body => do
  skipTopLevel t fun _ body => do
    trace[debug] "[hasOnlyTopLevelForAll] body: {body}"
    let found := findForAll body
    if found.isSome then
      trace[debug] "[hasOnlyTopLevelForAll] found: {found}"
    return !found.isSome
  where
  findForAll (e : Expr) : Option Expr :=
    e.find? (fun e =>
      match e with
        | Expr.forallE _ t _ _ => t.isAppOf overT
        | _ => false)

/-- Check if the given type `t` has non top-level ∀ quantification over
the state type. (This means we cannot send the type/goal to SMT.) -/
def hasStateHOInnerForall (e : Expr) : MetaM Bool := do
  let stateName ← getStateName
  return !(← hasOnlyTopLevelForAll (← Meta.reduceAll e) stateName)


section UniversalQuantifierTheorems
attribute [quantifierElim] forall_const forall_eq forall_eq
forall_exists_index

section forall_and
open Classical
variable [ne : Nonempty α] {p q : α → Prop} {b : Prop}

/-! Hoist `∀` quantifiers to the top of the goal. -/
theorem forall_and_left : b ∧ (∀ x, p x) ↔ (∀ x, b ∧ p x) := by
  constructor
  { simp_all only [and_self, implies_true] }
  {
    simp_all only [implies_true, and_true]
    intro h; rcases h (Classical.choice ne) with ⟨hb, _⟩
    assumption
  }
theorem forall_and_right : (∀ x, p x) ∧ b ↔ (∀ x, p x ∧ b) := by
  simp only [and_comm, forall_and_left]

attribute [quantifierElim] forall_and_left forall_and_right
end forall_and

section forall_imp
-- `α : Type` because we don't want this to apply to `α := Prop`
variable {α : Type} {p : α → Prop} {b : Prop}

theorem forall_imp_left : b → (∀ x, p x) ↔ (∀ x, b → p x) := by
  constructor
  { intro h x hb; exact h hb x }
  { intro h hb x; exact h x hb }

attribute [quantifierElim] forall_imp_left
end forall_imp

section IteForallPushOutTheorems
open Classical

open Lean Elab Tactic in
elab "prove_ite_forall_push_out" p:term : tactic => withMainContext do evalTactic $ ←
`(tactic|apply propext; by_cases h : $p; { simp only [if_pos h, forall_const] }; { simp only [if_neg h, forall_const] })

theorem ite_then_forall_push_out [ne : Nonempty α] (c r : Prop) (q : α → Prop) : (if c then ∀ t, q t else r) = (∀ t, if c then q t else r) := by prove_ite_forall_push_out c
attribute [quantifierElim] ite_then_forall_push_out

theorem ite_else_forall_push_out [ne : Nonempty α] (c r : Prop) (q : α → Prop) : (if c then r else ∀ t, q t) = (∀ t, if c then r else q t) := by prove_ite_forall_push_out c
attribute [quantifierElim] ite_else_forall_push_out

-- FIXME George: this doesn't seem to trigger
theorem ite_both_forall_push_out [ne : Nonempty α] [ne' : Nonempty β] (p : α → Prop) (q : β → Prop) :
  (if c then ∀ a, p a else ∀ b, q b) = (∀ (a : α) (b : β), if c then p a else q b) := by prove_ite_forall_push_out c
attribute [quantifierElim] ite_both_forall_push_out
end IteForallPushOutTheorems

end UniversalQuantifierTheorems
