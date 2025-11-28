
import Lean
import Batteries.Lean.Meta.UnusedNames
import Lean.Util.ForEachExpr

import Veil.Base
import Veil.Util.DSL
import Veil.SMT.Preparation
import Veil.SMT.Quantifiers.Check

import Lean.Util.MonadCache
import Lean.Meta.Basic

-- FIXME: `Mathlib.Tactic.Push` defines `Classical.not_imp._simp_3`, and this file
-- defines the same (by tagging it with `quantifierSimp`). I think the new module
-- system (which we haven't yet switched to) generates a duplicate definition (in
-- the files that import us downstream) if this file is not aware of that one.
import Mathlib.Data.Set.Basic

open Lean Meta Elab Tactic

namespace Veil

/-- Typeclass that gets inferred if a type is Higher Order. -/
class IsHigherOrder.{u} (t : Sort u)

instance (t₁ t₂ : Type) : IsHigherOrder (t₁ -> t₂) := ⟨⟩
instance (t₁ : Type) (t₂ : Prop) : IsHigherOrder (t₁ -> t₂) := ⟨⟩

/- Identify if an expression has higher-order quantification (arrow types or `State`). -/



/-- Returns an `Array` of the top-level higher-order existentially quantified
variables in `e`. -/
partial def getTopLevelHOExists (e : Expr) : SimpM (Array Name) := do
  let rec go (e : Expr) (acc : Array Name) : SimpM (Array Name) := do
    -- Stop as soon as we find a non-existential quantifier
    let_expr Exists t eBody ← e | return acc
    let qs ← ← lambdaBoundedTelescope eBody (maxFVars := 1) (fun ks lBody => do
        let #[k] := ks
          | throwError "[getExistentialsOverState::go] Expected exactly one variable in the lambda telescope"
        if ← isHigherOrder t then
          let decl := (← k.fvarId!.findDecl?).get!
          return go lBody (acc.push decl.userName)
        else
          return go lBody acc
    )
    return qs
  go e #[]

partial def forallLambdaLetTelescope (type : Expr) (k : Array Expr → Expr → MetaM α) (cleanupAnnotations : Bool) : MetaM α := do
  let rec go (type : Expr) (acc : Array Expr) : MetaM α := do
    match type with
    | Expr.forallE .. => forallTelescope type (fun xs body => go body (acc ++ xs)) cleanupAnnotations
    | Expr.lam ..  | Expr.letE .. => lambdaLetTelescope type (fun xs body => go body (acc ++ xs)) cleanupAnnotations
    | _ => k acc type
  go type #[]

def allHOQuantIsTopLevelForAll (t : Expr) : MetaM Bool := do
  let t ← Meta.reduceAll t
  forallLambdaLetTelescope t (fun _ body => do return !(← hasHigherOrderQuantification body)) true

/-! ## Existential Quantifiers

These simprocs & theorems hoist higher-order existential quantification to the
top of the goal. They also remove trivial quantification. -/
section ExistentialQuantifierTheorems

/- Shift HO quantifiers left (ensuring you don't go into loops, i.e. if both quantifiers are HO) -/
theorem exists_comm_eq {p : α → β → Prop} : (∃ a b, p a b) = (∃ b a, p a b) := by rw [exists_comm]

/- `∃ a b, p a b` => `∃ b a, p a b` _iff_ `b` is HO and `a` is NOT -/
def HO_exists_push_left_impl : Simp.Simproc := fun e => do
  let_expr Exists t eBody := e | return .continue
  -- The body of an `∃` is a lambda
  let step : Simp.Step ← lambdaBoundedTelescope eBody (maxFVars := 1) (fun ks lBody => do
      let_expr Exists t' eBody' := lBody | return .continue
      -- We only want to push HO types left over non-HO types. But we must be
      -- careful: if `t'` depends on the value of the previous binder, we cannot
      -- swap them.
      if (← isHigherOrder t') && !(← isHigherOrder t) && !(dependsOn t' ks)  then
        let step : Simp.Step ← lambdaBoundedTelescope eBody' (maxFVars := 1) (fun ks' lBody' => do
          -- swap the quantifiers
          let innerExists := mkAppN e.getAppFn #[t, ← mkLambdaFVars ks lBody']
          let outerExists := mkAppN lBody.getAppFn #[t', ← mkLambdaFVars ks' innerExists]
          let body ← mkLambdaFVars (ks ++ ks') lBody'
          let proof ← mkAppOptM ``exists_comm_eq #[t, t', body]
          return .visit { expr := outerExists, proof? := proof })
        return step
      else
        return .continue
  )
  return step
where
  dependsOn (child : Expr) (deps : Array Expr) : Bool :=
    child.find? (fun e => deps.contains e) != none

simproc HO_exists_push_left (∃ _ _, _) := HO_exists_push_left_impl
attribute [quantifierSimp] HO_exists_push_left

attribute [quantifierSimp] exists_const exists_eq exists_eq'
exists_eq_left exists_eq_left' exists_eq_right exists_eq_right'

/-! The default exists simp lemmas _unhoist_ quantifiers (push them as far in as
  possible), but to enable quantifier elimination, we want to _hoist_ them
  to the top of the goal, so we run these lemmas in the reverse direction. -/
section exists_and
set_option linter.unusedSectionVars false
variable [IsHigherOrder α] {p q : α → Prop} {b : Prop}
theorem exists_and_left'_eq : (b ∧ (∃ x, p x)) = (∃ x, b ∧ p x) := by rw [exists_and_left]
theorem exists_and_right'_eq : ((∃ x, p x) ∧ b) = (∃ x, p x ∧ b) := by rw [exists_and_right]
end exists_and
attribute [quantifierSimp] exists_and_left'_eq exists_and_right'_eq

section not_forall
-- `α : Type` because we don't want this to apply to `α := Prop`
-- GEORGE: should we specialize these to HO types?
variable {α : Type}

theorem not_forall' {p : α → Prop} : (¬∀ x, p x) ↔ ∃ x, ¬p x := Classical.not_forall
theorem not_forall_not' {p : α → Prop} : (¬∀ x, ¬p x) ↔ ∃ x, p x := Classical.not_forall_not
theorem not_exists_not' {p : α → Prop} : (¬∃ x, ¬p x) ↔ ∀ x, p x := Classical.not_exists_not

attribute [quantifierSimp] not_forall' not_forall_not'
attribute [quantifierSimp low] not_exists_not'
end not_forall

section exists_or
set_option linter.unusedSectionVars false
variable [IsHigherOrder α] [ne : Nonempty α] {p q : α → Prop} {b : Prop}

theorem exists_or_left : b ∨ (∃ x, p x) ↔ (∃ x, b ∨ p x) := by
  constructor
  {
    rintro (hb | ⟨x, px⟩)
    · rcases ne with ⟨x⟩; exists x; exact Or.inl hb
    · exists x; exact Or.inr px
  }
  {
    rintro ⟨x, hb | px⟩
    · exact Or.inl hb
    · exact Or.inr ⟨x, px⟩
  }

theorem exists_or_right : (∃ x, p x) ∨ b ↔ (∃ x, p x ∨ b) := by
  constructor
  {
    rintro (⟨x, hx⟩ | hb)
    · exists x; exact Or.inl hx
    · rcases ne with ⟨x⟩; exists x; exact Or.inr hb
  }
  {
    rintro ⟨x, hx | hb⟩
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr hb
  }
attribute [quantifierSimp] exists_or_left exists_or_right
end exists_or


open Classical in
theorem ite_exists_push_out [IsHigherOrder α] [ne : Nonempty α] (p r : Prop) (q : α → Prop) : (if p then ∃ t, q t else r) = (∃ t, if p then q t else r) := by
  apply propext; by_cases h : p
  { simp only [if_pos h] }
  {
    simp only [if_neg h]; constructor
    intro hr
    · rcases ne with ⟨t⟩; exists t
    · rintro ⟨t, ht⟩; apply ht
  }

attribute [quantifierSimp] ite_exists_push_out

end ExistentialQuantifierTheorems

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
