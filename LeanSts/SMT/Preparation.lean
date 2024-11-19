import Lean
import Batteries.Lean.Meta.UnusedNames

import LeanSts.Basic
import LeanSts.DSL.Util

open Lean Meta Elab Tactic

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

/-- When calling actions, we get goals that quantify over the post-state,
    e.g. `∃ st', preconditions ∧ st' = ... ∧ ...`. We can eliminate these
    quantifers by replacing st' in the body of the existential with the RHS
    of the equality. This function helps do that by pushing equalities
    involving the inner-most existential `bvar 0` to the left.
    `exists_eq_left` (in `smtSimp`) will then eliminate the quantifier.-/
partial def pushEqLeft (e : Expr) : MetaM Expr := do
  -- go under existential quantifiers
  match_expr e with
  | Exists t body => return mkAppN e.getAppFn #[t, (← pushEqLeft body)]
  | _ =>
  match e with
  -- go inside function bodies (the body of an `∃` is a lambda)
  | .lam bn bt body bi => return .lam bn bt (← pushEqLeft body) bi
  | _ =>
    -- (?lhs ∧ ?rhs)
    let_expr And lhs rhs := e | return e
    let rhs' ← pushEqLeft rhs -- recursively transform RHS
    let (rhs, e) := (rhs', mkAnd lhs rhs') -- update RHS and the whole expression
    match_expr rhs with
    -- (?lhs ∧ ?a = ?b) => (?a = ?b ∧ ?lhs)
    | Eq a b =>
        -- trace[dsl] "(?lhs ∧ ?a = ?b) => (?a = ?b ∧ ?lhs)"
        if isInnerMost a || isInnerMost b then return mkAnd rhs lhs else return e
    -- (?lhs ∧ (?top ∧ ?bottom))
    | And top bottom  =>
        let_expr Eq _ a b := top | return e
        -- trace[dsl] "(?lhs ∧ ({top} ∧ ?bottom))"
        if isInnerMost a || isInnerMost b then return mkAnd top (mkAnd lhs bottom) else return e
    | _ => return e
    where isInnerMost (e : Expr) : Bool := e == .bvar 0

def pushEqLeftTactic (id : Option (TSyntax `ident)) : TacticM Unit := withMainContext do
  let e ← (match id with
  | none => return ← getMainTarget
  | some id => do
      let ctx ← getLCtx
      let .some hyp := ctx.findFromUserName? id.getId
        | throwError "unknown identifier '{id}'"
      return hyp.type
  )
  let e' ← pushEqLeft e
  -- trace[dsl] "{e} => {e'}"
  let goal ← getMainGoal
  let heq ← mkFreshExprMVar (← Meta.mkEq e e')
  let hname ← mkFreshUserName `heq
  let goal' ← MVarId.assert goal hname (← heq.mvarId!.getType) heq
  let (_h, goal') ← goal'.intro1P
  setGoals [heq.mvarId!, goal']
  heq.mvarId!.withContext do
    evalTactic $ ← `(tactic|ac_rfl)
  let tactic ← match id with
  | none => `(tactic| rw [$(mkIdent hname):ident]; clear $(mkIdent hname):ident)
  | some id => `(tactic| rw [$(mkIdent hname):ident] at $id:ident; clear $(mkIdent hname):ident)
  evalTactic tactic

elab "pushEqLeft" "at" id:ident : tactic => pushEqLeftTactic (some id)
elab "pushEqLeft" "at" "⊢" : tactic => pushEqLeftTactic none
elab "pushEqLeft" : tactic => pushEqLeftTactic none

-- TODO: do we need to do the same for `∀` quantification and `→`, with `forall_eq'`?

-- These are from `SimpLemmas.lean` and `PropLemmas.lean`, but with
-- `smtSimp` attribute They are used to enable "eliminating" higher-order
-- quantification over state, as explained in:
--  (1) https://github.com/verse-lab/lean-sts/issues/32#issuecomment-2418792775
--  (2) https://github.com/verse-lab/lean-sts/issues/32#issuecomment-2419140869
-- Also: https://github.com/verse-lab/lean-sts/issues/3#issuecomment-2244192371
-- Things are quite a bit faster than the whole `simp` set this way.
/-
```bash
cat /home/dranov/.elan/toolchains/leanprover--lean4---v4.11.0/src/lean/Init/PropLemmas.lean /home/dranov/.elan/toolchains/leanprover--lean4---v4.11.0/src/lean/Init/SimpLemmas.lean | grep "@\[simp\] theorem" | cut -d ' ' -f 3 | tr '\n' ' '
```
Note: the above misses some lemmas that have `@[simp]` above the line with `theorem`.
-/
/-! ## cast and equality -/
attribute [smtSimp] eq_mp_eq_cast eq_mpr_eq_cast cast_cast eq_true_eq_id

/-! ## distributivity -/
attribute [smtSimp] not_or

/-! ## Ite -/
attribute [smtSimp] if_false_left if_false_right
attribute [smtSimp low] if_true_left if_true_right
attribute [smtSimp] dite_not ite_not ite_true_same ite_false_same

/-! ## exists and forall -/
attribute [smtSimp] forall_exists_index exists_const exists_true_left
  not_exists exists_false forall_const forall_eq forall_eq' exists_eq
  exists_eq' exists_eq_left exists_eq_right

/-! The default exists simp lemmas _unhoist_ quantifiers (push them as far in as
  possible), but to enable quantifier elimination, we want to _hoist_ them
  to the top of the goal, so we run these lemmas in the reverse direction. -/
section quantifiers
variable {p q : α → Prop} {b : Prop}
theorem exists_and_left' : b ∧ (∃ x, p x) ↔ (∃ x, b ∧ p x) := by rw [exists_and_left]
theorem exists_and_right' : (∃ x, p x) ∧ b ↔ (∃ x, p x ∧ b) := by rw [exists_and_right]
end quantifiers
attribute [smtSimp] exists_and_left' exists_and_right'

-- TODO: do we correctly hoist `∀`?
attribute [smtSimp] exists_eq_left' exists_eq_right' forall_eq_or_imp
  exists_eq_or_imp exists_eq_right_right exists_eq_right_right'
  exists_or_eq_left exists_or_eq_right exists_or_eq_left'
  exists_or_eq_right' exists_prop exists_apply_eq_apply
  forall_apply_eq_imp_iff forall_eq_apply_imp_iff forall_apply_eq_imp_iff₂

/-! ## decidable -/
attribute [smtSimp] Decidable.not_not decide_eq_decide
  Decidable.not_imp_self decide_implies decide_ite ite_true_decide_same
  ite_false_decide_same

/-! From `SimpLemmas.Lean`-/
attribute [smtSimp] eq_self ne_eq ite_true ite_false dite_true
  dite_false ite_self and_true true_and and_false false_and and_self
  and_not_self not_and_self and_imp not_and or_self or_true true_or
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
