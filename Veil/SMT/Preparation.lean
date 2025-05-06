import Lean
import Batteries.Lean.Meta.UnusedNames

import Veil.Base
import Veil.Util.DSL

open Lean Meta Elab Tactic

/-- Used to generate unique names for binders. -/
structure SmtState where
  binderIds : Std.HashMap Name UInt64 := {}
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

private def uniqueBinder (e : Expr) : MetaM Expr := do
  match e with
  | .forallE bn bt body bi => return .forallE (← freshBinderName bn) bt body bi
  | .lam bn bt body bi => return .lam (← freshBinderName bn) bt body bi
  | .letE n t v b nd => return .letE (← freshBinderName n) t v b nd
  | _ => return e
  where freshBinderName (bn : Name) := do
    let ids := (← smtExt.get).binderIds
    let id := ids.getD bn 0
    let bn' := if id == 0 then bn else Name.mkSimple s!"{bn}{id}"
    smtExt.set { binderIds := ids.insert bn (id + 1) }
    return bn'

/-- Ensure all the binders in `e` have unique names. -/
def uniqueBinders (e : Expr) : MetaM Expr := do
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
  let goalType' ← uniqueBinders goalType
  let goal' ← goal.replaceTargetDefEq' goalType'
  setGoals [goal']

/-- Workaround for
[lean-smt#121](https://github.com/ufmg-smite/lean-smt/issues/121). The
fix implemented there seems unreliable. -/
@[smtSimp] theorem iff_eq_eq : (p ↔ q) = (p = q) := propext ⟨propext, (· ▸ ⟨(·), (·)⟩)⟩

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

/-! ## decidable -/
attribute [smtSimp] Decidable.not_not decide_eq_decide Decidable.not_imp_self
  decide_implies decide_ite ite_then_decide_self ite_else_decide_self
  decide_eq_true_eq decide_eq_false_iff_not decide_not not_decide_eq_true
  cond_true cond_false decide_False decide_True

-- These are from `SimpLemmas.lean` and `PropLemmas.lean`
/-
```bash
cat /home/dranov/.elan/toolchains/leanprover--lean4---v4.11.0/src/lean/Init/PropLemmas.lean /home/dranov/.elan/toolchains/leanprover--lean4---v4.11.0/src/lean/Init/SimpLemmas.lean | grep "@\[simp\] theorem" | cut -d ' ' -f 3 | tr '\n' ' '
```
Note: the above misses some lemmas that have `@[simp]` above the line with `theorem`.
-/
/-! ## cast and equality -/
attribute [logicSimp] eq_mp_eq_cast eq_mpr_eq_cast cast_cast eq_true_eq_id

/-! ## Ite -/
theorem not_if {_ : Decidable c} :
  ¬ (if c then t else e) =
  if c then ¬ t else ¬ e := by
  by_cases c <;> simp_all

/-! ## distributivity -/
attribute [logicSimp] not_or not_imp not_and not_if -- Classical.not_forall
/-! ## Ite -/
theorem if_app {α β : Type} {_ : Decidable c} (t e : α -> β) (a : α) :
  (if c then t else e) a =
  if c then (t a) else (e a) := by
  by_cases c <;> simp_all

attribute [logicSimp] if_true if_false dite_true dite_false
attribute [logicSimp] if_false_left if_false_right if_app
attribute [logicSimp low] if_true_left if_true_right
attribute [logicSimp] dite_not ite_not ite_then_self ite_else_self

/-

These change quantifier structure, so can make decidable queries undecidable.
We keep them commented out, since we want explicit control, which we get
via the `quantifierSimp` attribute.

/-! ## exists and forall -/
attribute [logicSimp] forall_exists_index exists_const exists_true_left
  not_exists exists_false forall_const forall_eq forall_eq' exists_eq
  exists_eq' exists_eq_left exists_eq_right

attribute [logicSimp] exists_eq_left' exists_eq_right' forall_eq_or_imp
  exists_eq_or_imp exists_eq_right_right exists_eq_right_right'
  exists_or_eq_left exists_or_eq_right exists_or_eq_left'
  exists_or_eq_right' exists_prop exists_apply_eq_apply
  forall_apply_eq_imp_iff forall_eq_apply_imp_iff forall_apply_eq_imp_iff₂
-/

/-! ## decidable -/
attribute [logicSimp] Decidable.not_not decide_eq_decide
  Decidable.not_imp_self decide_implies decide_ite ite_then_decide_self
  ite_else_decide_self

/-! From `SimpLemmas.Lean`-/
attribute [logicSimp] eq_self ne_eq ite_true ite_false dite_true
  dite_false ite_self and_true true_and and_false false_and and_self
  and_not_self not_and_self and_imp or_self or_true true_or
  or_false false_or iff_self iff_true true_iff iff_false false_iff
  false_implies forall_false implies_true true_implies not_false_eq_true
  not_true_eq_false not_iff_self and_self_left and_self_right
  and_congr_right_iff and_congr_left_iff and_iff_left_iff_imp
  and_iff_right_iff_imp iff_self_and iff_and_self or_self_left
  or_self_right or_iff_left_iff_imp or_iff_right_iff_imp iff_self_or
  iff_or_self Bool.or_false Bool.or_true Bool.false_or Bool.true_or
  Bool.or_self Bool.or_eq_true Bool.and_false Bool.and_true Bool.false_and
  Bool.true_and Bool.and_self Bool.and_eq_true Bool.not_not Bool.not_true
  Bool.not_false beq_true beq_false Bool.not_eq_true' Bool.not_eq_false'
  Bool.not_eq_true Bool.not_eq_false decide_eq_true_eq
  decide_eq_false_iff_not decide_not not_decide_eq_true heq_eq_eq
  cond_true cond_false beq_self_eq_true bne_self_eq_false decide_False
  decide_True bne_iff_ne beq_eq_false_iff_ne bne_eq_false_iff_eq
  Nat.le_zero_eq
