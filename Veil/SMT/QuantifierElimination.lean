
import Lean
import Batteries.Lean.Meta.UnusedNames
import Lean.Util.ForEachExpr

import Veil.Basic
import Veil.DSL.Util
import Veil.SMT.Preparation

open Lean Meta Elab Tactic

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
  let _ ← Meta.forEachExpr e (fun e =>
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

/-- Check if the given `Expr` quantifies over type with name `overT`. -/
def hasQuantificationOver (e : Expr) (overT : Name) (existentialOnly? : Bool := false) : Bool :=
  let found := e.find? (fun e =>
   match e with
    | Expr.forallE _ t _ _ => !existentialOnly? && isHigherOrder t overT
    | _ => match_expr e with
      | Exists t _ => isHigherOrder t overT
      | _ => false
  )
  found.isSome
  where
  isHigherOrder (t : Expr) (overT : Name) :=
    t.isAppOf overT

/-- Check if the given `Expr` quantifies (∀ or ∃) over the state type. -/
def hasStateHOQuant (e : Expr) (existentialOnly? : Bool := false) : MetaM Bool := do
  let stateName ← getStateName
  return hasQuantificationOver (← Meta.reduceAll e) stateName existentialOnly?

/-- Check if the given `Expr` existentially quantifies over the state type. -/
def hasStateHOExist (e : Expr) : MetaM Bool := hasStateHOQuant e (existentialOnly? := true)

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

/-- ## Existential Quantifiers-/

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
