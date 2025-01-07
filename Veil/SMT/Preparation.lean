import Lean
import Batteries.Lean.Meta.UnusedNames

import Veil.Basic
import Veil.DSL.Util

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
    let id := ids.findD bn 0
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

theorem exists_comm_eq {p : α → β → Prop} : (∃ a b, p a b) = (∃ b a, p a b) := by rw [exists_comm]

/-- Used to provide a proof in `pushEqInvolvingLeft` -/
theorem and_comm_eq {p q : Prop} : (p ∧ q) = (q ∧ p) := propext and_comm

/-- Used to provide a proof in `pushEqInvolvingLeft` -/
theorem and_comm_middle {p q r : Prop} : (p ∧ (q ∧ r)) = (q ∧ (p ∧ r)) := by
  apply propext
  constructor <;> (intro h; simp only [h, and_self])

/-- Returns an `Array` of the free variables that are existentially
quantified `State` in `e`. -/
partial def getExistentialsOverState (e : Expr) : SimpM (Array Name) := do
  let stateName ← getStateName
  let rec go (e : Expr) (acc : Array Name) : SimpM (Array Name) := do
    -- Stop as soon as we find a non-existential quantifier
    let_expr Exists t eBody ← e | return acc
    let qs ← ← lambdaBoundedTelescope eBody (maxFVars := 1) (fun ks lBody => do
        let #[k] := ks
          | throwError "[getExistentialsOverState::go] Expected exactly one variable in the lambda telescope"
        if (t.isAppOf stateName) then
          let decl := (← k.fvarId!.findDecl?).get!
          return go lBody (acc.push decl.userName)
        else
          return go lBody acc
    )
    return qs
  go e #[]

/-- Push all equalities having the expression `this` on the LHS left
(one step) over `∧` in `e.` The goals we generate should only have each
state on the LHS of an equality ONCE (they might appear on the RHS
multiple times). -/
def pushEqInvolvingLeft (this : Name) : Simp.Simproc := fun e => do
  -- trace[dsl.debug] "[pushEqInvolvingLeft] {this} in {e}"
  let_expr And top bottom ← e | return .continue
  match_expr bottom with
  -- (?top ∧ (?lhs = ?rhs)) => ((?lhs = ?rhs) ∧ ?top)
  | Eq _ lhs _rhs =>
      -- We only want to push the equality if `this` is on the LHS
      if !(← ematches lhs) then
        return .continue
      let e' := mkAnd bottom top
      let pf ← mkAppOptM ``and_comm_eq #[top, bottom]
      return .visit { expr := e', proof? := pf }
  -- (?top ∧ (?lhs = ?rhs) ∧ ?bottom) => ((?lhs = ?rhs) ∧ ?top ∧ ?bottom)
  | And middle bottom =>
      let_expr Eq _ lhs _rhs ← middle | return .continue
      -- We only want to push the equality if `this` is on the LHS
      if !(← ematches lhs) then
        return .continue
      let e' := mkAnd middle (mkAnd top bottom)
      let pf ← mkAppOptM ``and_comm_middle #[top, middle, bottom]
      return .visit { expr := e', proof? := pf }
  | _ => return .continue
  where ematches (e : Expr) := do
    match e.isFVar with
    | true => return (← e.fvarId!.findDecl?).get!.userName == this
    | false => return false

/-- Pushes existential quantifiers over `State` to the right, e.g.
`∃ (s : State) x1 x2, P` becomes `∃ x1 x2 s, P`. For details, see:
https://github.com/verse-lab/lean-sts/issues/32#issuecomment-2419140869 -/
def State_exists_push_right (this : Name) : Simp.Simproc := fun e => do
  let_expr Exists t eBody := e | return .continue
  let stateName ← getStateName
  if !(t.isAppOf stateName) then
    return .continue
  -- the body of an `∃` is a lambda
  let step ← lambdaBoundedTelescope eBody (maxFVars := 1) (fun ks lBody => do
      -- if this isn't the right binder, we can bail out
      let #[k] := ks
        | throwError "[State_exists_push_right] Expected exactly one variable in the lambda telescope"
      if !(← ematches k) then
        return .continue
      let_expr Exists t' eBody' := lBody | return .continue
      let step ← lambdaBoundedTelescope eBody' (maxFVars := 1) (fun ks' lBody' => do
        -- swap the quantifiers
        let innerExists := mkAppN e.getAppFn #[t, ← mkLambdaFVars ks lBody']
        let outerExists := mkAppN lBody.getAppFn #[t', ← mkLambdaFVars ks' innerExists]
        let body ← mkLambdaFVars (ks ++ ks') lBody'
        let proof ← mkAppOptM ``exists_comm_eq #[t, t', body]
        -- trace[dsl.debug] "[State_exists_comm ({stateName})] {e} ~~> {outerExists}"
        /- This needs to be `.visit` rather than `.done` to ensure the
        quantifier is pushed as far right as possible (on subsequent
        applications of this rule) -/
        return .visit { expr := outerExists, proof? := proof }
      )
      return step
  )
  return step
  where ematches (e : Expr) := do
    match e.isFVar with
    | true => return (← e.fvarId!.findDecl?).get!.userName == this
    | false => return false

/-- Used to provide a proof in `exist_eq_left_simproc`. -/
theorem exists_eq_left_propext : ∀ {α : Sort u} {p : α → Prop} {a' : α},
  (∃ a, a = a' ∧ p a) = p a' := propext exists_eq_left

/-- This is a `simproc` version of `exists_eq_left`, because I couldn't
figure out how to call `exists_eq_left` from within a `simproc`. See
[this Zulip thread.](https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/How.20to.20call.20a.20simp.20lemma.20within.20a.20simproc.3F/near/491257020)
-/
private def exist_eq_left_simproc' : Simp.Simproc := fun e => do
  let_expr Exists t eBody := e | return .continue
  let step ← lambdaBoundedTelescope eBody (maxFVars := 1) (fun ks lBody => do
      let #[k] := ks
        | throwError "Expected exactly one variable in the lambda telescope"
      let_expr And l r ← lBody | return .continue
      let_expr Eq _ lhs rhs ← l | return .continue
      if ← isDefEq lhs k then
        let r' ← mkLambdaFVars #[lhs] r
        let newBody ← Core.betaReduce $ mkAppN r' #[rhs]
        let proof ← mkAppOptM ``exists_eq_left_propext #[t, r', rhs]
        return .done { expr := newBody, proof? := proof }
      else
        return .continue
  )
  return step

/- We have to give the pattern for the simproc to be callable. -/
simproc_decl exist_eq_left_simproc (∃ _, _) := exist_eq_left_simproc'

-- TODO ∀: do we need to do the same for `∀` quantification and `→`, with `forall_eq'`?

-- These are from `SimpLemmas.lean` and `PropLemmas.lean`, but with
-- `logicSimp` attribute They are used to enable "eliminating" higher-order
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
attribute [logicSimp] eq_mp_eq_cast eq_mpr_eq_cast cast_cast eq_true_eq_id

/-! ## distributivity -/
attribute [logicSimp] not_or

/-! ## Ite -/
attribute [logicSimp] if_false_left if_false_right
attribute [logicSimp low] if_true_left if_true_right
attribute [logicSimp] dite_not ite_not ite_true_same ite_false_same

/-! ## exists and forall -/
attribute [logicSimp] forall_exists_index exists_const exists_true_left
  not_exists exists_false forall_const forall_eq forall_eq' exists_eq
  exists_eq' exists_eq_left exists_eq_right

/-! The default exists simp lemmas _unhoist_ quantifiers (push them as far in as
  possible), but to enable quantifier elimination, we want to _hoist_ them
  to the top of the goal, so we run these lemmas in the reverse direction.
  We give these lemmas the `logicSimp` attribute (as opposed to `quantifierElim`)
  because we want them to run _before_ the `quantifierElim` lemmas. -/
section quantifiers
variable {p q : α → Prop} {b : Prop}
theorem exists_and_left' : b ∧ (∃ x, p x) ↔ (∃ x, b ∧ p x) := by rw [exists_and_left]
theorem exists_and_right' : (∃ x, p x) ∧ b ↔ (∃ x, p x ∧ b) := by rw [exists_and_right]
end quantifiers
attribute [logicSimp] exists_and_left' exists_and_right'

-- TODO: do we correctly hoist `∀`?
attribute [logicSimp] exists_eq_left' exists_eq_right' forall_eq_or_imp
  exists_eq_or_imp exists_eq_right_right exists_eq_right_right'
  exists_or_eq_left exists_or_eq_right exists_or_eq_left'
  exists_or_eq_right' exists_prop exists_apply_eq_apply
  forall_apply_eq_imp_iff forall_eq_apply_imp_iff forall_apply_eq_imp_iff₂

/-! quantifier elimination -/
attribute [quantifierElim] forall_eq' exists_eq exists_eq'
  exists_eq_left exists_eq_right exists_and_left' exists_and_right'
  exists_eq_left' exists_eq_right_right exists_eq_right_right'

/-- A variant of the above, for use when defining a `Simp.Context` in
`elim_exists_State`. (I couldn't figure out how to create a list of
`SimpTheorems` from ). -/
@[inline] def quantifierElimThms : MetaM SimpTheorems :=
  quantifierElimThms'.foldlM (·.addConst ·) ({} : SimpTheorems)
  where quantifierElimThms' : List Name := [``forall_eq', ``exists_eq,
    ``exists_eq', ``exists_eq_left, ``exists_eq_right, ``exists_and_left',
    ``exists_and_right', ``exists_eq_left',
    ``exists_eq_right_right, ``exists_eq_right_right']
    /- `and_assoc` ensures these work even in larger cojunctions -/
    ++ [``and_assoc]
    /- so we behave similarly to `simp only` -/
    ++ simpOnlyBuiltins

/- When calling actions, we get goals that quantify over the post-state,
e.g. `∃ st', preconditions ∧ st' = ... ∧ ...`. We can eliminate these
quantifers by replacing `st'` in the body of the existential with the
RHS of the equality. This `simproc` assumes that (1) existential
quantifiers have been hoisted and that (2) we have already called
`simp [and_assoc]`, such that the formula has `a ∧ (b ∧ c)`
associativity. -/
simproc ↓ elim_exists_State (∃ _, _) := fun e => do
  let_expr Exists _ _ ← e | return .continue
  let e ← uniqueBinders e
  -- Step 1: identify all variables which quantify over `State`
  let qs ← getExistentialsOverState e
  if qs.isEmpty then
    -- no point visiting sub-expressions (since we assume quantifiers
    -- have been hoisted already)
    return .done { expr := e }
  -- Step 2: get rid of this quantifier
  let q := qs.get! 0
  let ctx : Simp.Context := {
      config := {(← Simp.getContext).config with singlePass := false}
      simpTheorems := #[(← quantifierElimThms)] -- includes `and_assoc`
      congrTheorems := (← getSimpCongrTheorems)
  }
  let method := (pushEqInvolvingLeft q)
                |> Simp.andThen (State_exists_push_right q)
                |> Simp.andThen (exist_eq_left_simproc)
  let (res, _stats) ← Simp.main e ctx (methods := { post := method})
  return .done res

/-! ## decidable -/
attribute [logicSimp] Decidable.not_not decide_eq_decide
  Decidable.not_imp_self decide_implies decide_ite ite_true_decide_same
  ite_false_decide_same

/-! From `SimpLemmas.Lean`-/
attribute [logicSimp] eq_self ne_eq ite_true ite_false dite_true
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
