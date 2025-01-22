
import Lean
import Batteries.Lean.Meta.UnusedNames
import Lean.Util.ForEachExpr

import Veil.Basic
import Veil.DSL.Util
import Veil.SMT.Preparation

import Lean.Util.MonadCache
import Lean.Meta.Basic

import Lean.Util.MonadCache
import Lean.Meta.Basic

namespace Lean.Meta

variable {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]

partial def forEachExprSane'
  (input : Expr)
  (fn : Expr → m Bool)
  : m Unit := do
  let _ : STWorld IO.RealWorld m := ⟨⟩
  let _ : MonadLiftT (ST IO.RealWorld) m := { monadLift := fun x => liftM (m := MetaM) (liftM (m := ST IO.RealWorld) x) }
  let rec visit (e : Expr) : MonadCacheT Expr Unit m Unit :=
    checkCache e fun _ => do
      if (← liftM (fn e)) then
        match e with
        | .forallE n d b c  => do visit d; withLocalDecl n c d (fun x => visit $ b.instantiate1 x)
        | .lam n d b c      => do visit d; withLocalDecl n c d (fun x => visit $ b.instantiate1 x)
        | .letE n d v b _   => do visit d; visit v; withLetDecl n d v (fun x => visit $ b.instantiate1 x)
        | .app f a      => visit f; visit a
        | .mdata _ b    => visit b
        | .proj _ _ b   => visit b
        | _             => return ()
  visit input |>.run

/-- Similar to `Expr.forEach`, but creates free variables whenever going inside
of a binder. Unlike `Meta.forEachExpr`, this doesn't use the strange
`visitForall` function which behaves unintuitively. -/
def forEachExprSane (e : Expr) (f : Expr → m Unit) : m Unit :=
  forEachExprSane' e fun e => do
    f e
    return true
end Lean.Meta

open Lean Meta Elab Tactic

#check Meta.forEachExpr

/-- Typeclass that gets inferred if a type is Higher Order. -/
class IsHigherOrder.{u} (t : Sort u)

instance (t₁ t₂ : Type) : IsHigherOrder (t₁ -> t₂) := ⟨⟩
instance (t₁ : Type) (t₂ : Prop) : IsHigherOrder (t₁ -> t₂) := ⟨⟩

/- Identify if an expression has higher-order quantification (arrow types or `State`). -/

structure QEState where
  quantifiedTypes : Std.HashSet Expr
deriving Inhabited

abbrev QuantElimM := StateT QEState MetaM

def isHigherOrder (e : Expr) : MetaM Bool := do
  let t ← inferType e
  let isHO := !t.isProp && (e.isArrow || e.isAppOf (← getStateName))
  return isHO


private def higherOrderQuantifiedTypes' (e : Expr) (existentialOnly? : Bool := false) : QuantElimM (Array Expr) := do
  let _ ← Meta.forEachExprSane e (fun e => do
    match e with
    | Expr.forallE _ t _ _ => if !existentialOnly? then recordTypeIfHigherOrder t else pure ()
    | _ => match_expr e with
      | Exists t _ => recordTypeIfHigherOrder t
      | _ => pure ()
  )
  let res := (← get).quantifiedTypes.toArray
  return res
  where recordTypeIfHigherOrder (e : Expr) : QuantElimM Unit := do
    if ← isHigherOrder e then
      modify (fun s => { s with quantifiedTypes := s.quantifiedTypes.insert e })

def Lean.Expr.higherOrderQuantifiers (e : Expr) (existentialOnly? : Bool := false) : MetaM (Array Expr) := do
  let (types, _st) ← (higherOrderQuantifiedTypes' e existentialOnly?).run default
  return types

def Lean.Expr.hasHigherOrderQuantification (e : Expr) (existentialOnly? : Bool := false) : MetaM Bool := do
  return (← e.higherOrderQuantifiers existentialOnly?).size > 0

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
  forallLambdaLetTelescope t (fun _ body => do return !(← body.hasHigherOrderQuantification)) true

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
      if (← isHigherOrder t') && !(← isHigherOrder t) then
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

simproc HO_exists_push_left (∃ _ _, _) := HO_exists_push_left_impl
attribute [quantifierElim] HO_exists_push_left

attribute [quantifierElim] exists_const exists_eq exists_eq'
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
attribute [quantifierElim] exists_and_left'_eq exists_and_right'_eq

section not_forall
-- `α : Type` because we don't want this to apply to `α := Prop`
-- GEORGE: should we specialize these to HO types?
variable {α : Type}

theorem not_forall' {p : α → Prop} : (¬∀ x, p x) ↔ ∃ x, ¬p x := Classical.not_forall
theorem not_forall_not' {p : α → Prop} : (¬∀ x, ¬p x) ↔ ∃ x, p x := Classical.not_forall_not
theorem not_exists_not' {p : α → Prop} : (¬∃ x, ¬p x) ↔ ∀ x, p x := Classical.not_exists_not

attribute [quantifierElim] not_forall' not_forall_not'
attribute [quantifierElim low] not_exists_not'
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
attribute [quantifierElim] exists_or_left exists_or_right
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

attribute [quantifierElim] ite_exists_push_out

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
attribute [quantifierElim] HO_forall_push_left

attribute [quantifierElim] forall_const forall_eq forall_eq forall_exists_index

-- To enable some of the lemmas below; FIXME: do we need more of these?
-- attribute [quantifierElim] and_imp not_and

section forall_and
set_option linter.unusedSectionVars false
open Classical
variable [IsHigherOrder α] [ne : Nonempty α] {p q : α → Prop} {b : Prop}

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
set_option linter.unusedSectionVars false
-- `α : Type` because we don't want this to apply to `α := Prop`
variable {α : Type} [IsHigherOrder α] {p : α → Prop} {b : Prop}

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

theorem ite_then_forall_push_out [IsHigherOrder α] [ne : Nonempty α] (c r : Prop) (q : α → Prop) : (if c then ∀ t, q t else r) = (∀ t, if c then q t else r) := by prove_ite_forall_push_out c
attribute [quantifierElim] ite_then_forall_push_out

theorem ite_else_forall_push_out [IsHigherOrder α] [ne : Nonempty α] (c r : Prop) (q : α → Prop) : (if c then r else ∀ t, q t) = (∀ t, if c then r else q t) := by prove_ite_forall_push_out c
attribute [quantifierElim] ite_else_forall_push_out

-- FIXME George: does this trigger?
theorem ite_both_forall_push_out [IsHigherOrder α] [ne : Nonempty α] [ne' : Nonempty β] (p : α → Prop) (q : β → Prop) :
  (if c then ∀ a, p a else ∀ b, q b) = (∀ (a : α) (b : β), if c then p a else q b) := by prove_ite_forall_push_out c
attribute [quantifierElim] ite_both_forall_push_out
end IteForallPushOutTheorems

end UniversalQuantifierTheorems
