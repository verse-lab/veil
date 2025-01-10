import Lean
import Lean.Util.ForEachExpr
import Batteries.Lean.Meta.UnusedNames

import Veil.Basic
import Veil.DSL.Util
import Veil.SMT.Preparation

/- # Quantifier elimination

This file contains the `simproc`s and `simp` lemmas used to eliminate
higher-order quantification from the Lean goals we generate, in
preparation for sending them to SMT.
-/

open Lean Meta Elab Tactic

/-- Check if the given `Expr` quantifies over type with name `overT`. -/
def hasHOQuantification (e : Expr) (overT : Name) (existentialOnly? : Bool := true) : Bool :=
  let found := e.find? (fun e =>
   match e with
    | Expr.forallE _ t _ _ => !existentialOnly? && isHigherOrder t overT
    | _ => match_expr e with
      | Exists t _ =>

        isHigherOrder t overT
      | _ => false
  )
  found.isSome
  where
  isHigherOrder (t : Expr) (overT : Name) :=
    t.isAppOf overT

/-- Check if the given `Expr` quantifies (∀ or ∃) over the state type. -/
def hasStateHOQuant (e : Expr) (existentialOnly? : Bool := false) : MetaM Bool := do
  let stateName ← getStateName
  return hasHOQuantification (← Meta.reduceAll e) stateName existentialOnly?

/-- Check if the given `Expr` existentially quantifies over the state type. -/
def hasStateHOExist (e : Expr) : MetaM Bool := hasStateHOQuant e (existentialOnly? := true)

open Lean.Parser.Tactic in
/-- [DEBUG] For debugging purposes, we add a conv `simp?` conv tactic. -/
syntax (name := conv_simp_debug) "simp?" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")? : conv

open Lean Meta  Elab.Tactic Conv  in
@[tactic conv_simp_debug] def evalSimp : Tactic := fun stx => withMainContext do
  let { ctx, simprocs, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
  let lhs ← getLhs
  let (result, stats) ← dischargeWrapper.with fun d? => simp lhs ctx (simprocs := simprocs) (discharge? := d?)
  applySimpResult result
  traceSimpCall stx stats.usedTheorems

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

-- TODO ∀: do we need to do the same for `∀` quantification and `→`, with `forall_eq'`?

/-! quantifier elimination -/
attribute [quantifierElim] forall_eq' exists_eq exists_eq'
  exists_eq_left exists_eq_right exists_and_left' exists_and_right'
  exists_eq_left' exists_eq_right_right exists_eq_right_right'
