import Lean
import Batteries.Lean.Meta.UnusedNames

import LeanSts.Basic
import LeanSts.DSL.Util

open Lean Meta

/-- Used to generate unique names for binders. -/
structure SmtState where
  binderIds : HashMap Name UInt64 := {}
deriving Inhabited

open SmtState

initialize smtExt : EnvExtension SmtState ←
  registerEnvExtension (pure default)

theorem funextEq' {α β : Type} (f g : α → β) :
  (f = g) = ∀ x, f x = g x := by
  apply propext
  constructor
  { intro h ; simp only [h, implies_true] }
  { intro h ; apply funext h }

open Lean Expr Lean.Meta in
/-- Applies functional extensionality to all equalities between functions.
    This also functions as a partial workaround for
    [lean-smt#100](https://github.com/ufmg-smite/lean-smt/issues/100). -/
simproc ↓ funextEq (_ = _) :=
  fun e => do
  let_expr Eq _ lhs rhs := e | return .continue
  let (lhsT, rhsT) := (← inferType lhs, ← inferType rhs)
  if lhsT.isArrow && rhsT.isArrow then
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

def uniqueBinder (e : Expr) : MetaM Expr := do
  match e with
  | .forallE bn bt body bi =>
    let ids := (← smtExt.get).binderIds
    let id := ids.findD bn 0
    let bn' :=  Name.mkSimple s!"{bn}{id}"
    smtExt.set { binderIds := ids.insert bn (id + 1) }
    return .forallE (bn') bt body bi
  | _ => return e

def renameBinders (e : Expr) : MetaM Expr := do
  smtExt.set { binderIds := default }
  let e' ← Core.transform e (pre := fun e => do
    return TransformStep.continue (← uniqueBinder e))
  return e'

def _root_.Lean.MVarId.replaceTargetDefEq' (mvarId : MVarId) (targetNew : Expr) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `change
    let target  ← mvarId.getType
    let tag     ← mvarId.getTag
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag
    let newVal  ← mkExpectedTypeHint mvarNew target
    mvarId.assign newVal
    return mvarNew.mvarId!

open Elab Tactic in
/-- Workaround for [lean-smt#100](https://github.com/ufmg-smite/lean-smt/issues/100) -/
elab "rename_binders" : tactic => do
  let goal ← getMainGoal
  let goalType ← getMainTarget
  let goalType' ← renameBinders goalType
  let goal' ← goal.replaceTargetDefEq' goalType'
  setGoals [goal']


/-- Tuples are not supported in SMT-LIB, so we destruct tuple equalities. -/
@[smtSimp] theorem tupleEq [DecidableEq t1] [DecidableEq t2] (a c : t1) (b d : t2):
  ((a, b) = (c, d)) = (a = c ∧ b = d) := by
  apply propext
  constructor
  { intro h ; injection h ; constructor <;> assumption }
  { rintro ⟨h1, h2⟩ ; rw [h1, h2] }

/- These something show up in goals: https://github.com/verse-lab/lean-sts/issues/3#issuecomment-2244192371 -/
attribute [smtSimp] decide_eq_true_eq
attribute [smtSimp] decide_not
attribute [smtSimp] not_decide_eq_true
