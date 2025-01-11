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
end forall_and
attribute [quantifierElim] forall_and_left forall_and_right

end UniversalQuantifierTheorems
