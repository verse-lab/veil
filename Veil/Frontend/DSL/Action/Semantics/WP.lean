import Veil.Frontend.DSL.Action.Semantics.Definitions
import Veil.Frontend.DSL.State.SubState
import Veil.Frontend.DSL.Infra.Simp

namespace Veil
open PartialCorrectness DemonicChoice

variable (hd : ExId -> Prop) [IsHandler hd]

/- Languge constructs -/

def VeilExecM.assert (p : Prop) [Decidable p] (ex : ExId) : VeilExecM m ρ σ Unit := do
  if p then pure () else throw ex

def VeilM.assert (p : Prop) [Decidable p] (ex : ExId) : VeilM m ρ σ Unit := do
  liftM (@VeilExecM.assert m ρ σ p _ ex)

/-- We require the predicate to be `Decidable`, even though `assume`
does not, in order to collect the appropriate instances needed for
execution. -/
@[reducible]
def VeilM.assume (p : Prop) [Decidable p] : VeilM m ρ σ PUnit := do
  MonadNonDet.assume p

/-- We require the predicate to be `Decidable`, even though `assume`
does not, in order to collect the appropriate instances needed for
execution. -/
def VeilM.pickSuchThat (τ : Type) (p : τ → Prop) [∀ x, Decidable (p x)] : VeilM m ρ σ τ := do
  MonadNonDet.pickSuchThat τ p

def VeilM.require (p : Prop) [Decidable p] (ex : ExId) : VeilM m ρ σ Unit := do
  match m with
  | .internal => VeilM.assert p ex
  | .external => assume p

def VeilM.ensure (p : Prop) [Decidable p] (ex : ExId) : VeilM m ρ σ Unit := do
  match m with
  | .internal => assume p
  | .external => VeilM.assert p ex

/-- `ens` takes the pre-state as an argument to be able to compute the
frame (`unchanged`). -/
@[reducible] def VeilM.spec (req : SProp ρ σ) (ens : σ → RProp ρ σ α) (pre_ex post_ex : ExId) [∀ rd st, Decidable (req rd st)] [∀ rd st st' ret, Decidable (ens rd st st' ret)] : VeilM m ρ σ α := do
  let (rd, st) := (← read, ← get)
  VeilM.require (req rd st) pre_ex
  let (ret, st') := (← pick α, ← pick σ)
  VeilM.ensure (ens st rd st' ret) post_ex
  set st'
  return ret

/-- Takes a `VeilM` action, executes it, and returns `Unit`.-/
@[reducible]
def VeilM.returnUnit (act : VeilM m ρ σ α) : VeilM m ρ σ Unit := do
  let _ ← act
  return ()

omit hd [IsHandler hd] in
theorem VeilM.wp_returnUnit {hd' : ExId → Prop} {act : VeilM m ρ σ α} {q : VeilSpecM ρ σ α}
  (h : ∀ post_, [IgnoreEx hd'| wp act post_] = q post_) post :
  [IgnoreEx hd'| wp (VeilM.returnUnit act : VeilM m ρ σ Unit) post] = q (fun _ => post ()) := by
  simp only [wp_bind, wp_pure, h]

/-!
## WP rewrites

`wpSimp` rewrites WPs only after they are fully applied to their reader and
state. This keeps all intermediate equality endpoints proposition-valued and
avoids eta junctions around large interpreter applications.

Deliberately, only these fully-applied `VeilM`-headed lemmas are in the
`wpSimp` set: the generic (unapplied) `wp_pure`/`wp_map` rules were removed
because `fun`-shaped equality endpoints re-trigger the kernel def-eq blowup
of leanprover/lean4#14803. Downstream lemmas of the old shape
`wp act post = fun r s => …` should be restated pointwise
(`wp act post r s = …`) to keep simplifying under `wpSimp`. -/

lemma VeilM.wp_bind (act : VeilM m ρ σ α) (f : α → VeilM m ρ σ β)
    (post : RProp β ρ σ) (r : ρ) (s : σ) :
    wp (act >>= f) post r s = wp act (fun x => wp (f x) post) r s := by
  rw [_root_.wp_bind]

@[wpSimp ↓]
lemma VeilM.wp_pure (x : α) (post : RProp α ρ σ) (r : ρ) (s : σ) :
    wp (pure x : VeilM m ρ σ α) post r s = post x r s := by
  rw [_root_.wp_pure]

@[wpSimp ↓]
lemma VeilM.wp_map (act : VeilM m ρ σ α) (f : α → β)
    (post : RProp β ρ σ) (r : ρ) (s : σ) :
    wp (f <$> act) post r s = wp act (fun x => post (f x)) r s := by
  rw [_root_.wp_map]

@[wpSimp ↓]
lemma VeilExecM.wp_assume (p : Prop) [Decidable p]
    (post : RProp PUnit ρ σ) (r : ρ) (s : σ) :
    wp (VeilM.assume p : VeilM m ρ σ PUnit) post r s = (p → post .unit r s) := by
  simp [MonadNonDet.wp_assume, loomLogicSimp, himp]

/-- This formulation avoids a blowup in formula size by avoiding copies of `post`. -/
@[wpSimp ↓]
lemma VeilM.wp_require (p : Prop) [Decidable p] (ex : ExId)
    (post : RProp Unit ρ σ) (r : ρ) (s : σ) :
    wp (VeilM.require p ex : VeilM m ρ σ Unit) post r s =
      (letI wpI := fun _p [Decidable _p] _post =>
        wp (VeilM.assert _p ex : VeilM .internal ρ σ Unit) _post
       letI wpE := fun _p [Decidable _p] _post =>
        wp (VeilM.assume _p : VeilM .external ρ σ Unit) _post
       (match m with | .internal => wpI | .external => wpE) p post) r s := by
  cases m <;> rfl

/-- This formulation avoids a blowup in formula size by avoiding copies of `post`. -/
@[wpSimp ↓]
lemma VeilM.wp_ensure (p : Prop) [Decidable p] (ex : ExId)
    (post : RProp Unit ρ σ) (r : ρ) (s : σ) :
    wp (VeilM.ensure p ex : VeilM m ρ σ Unit) post r s =
      (letI wpI := fun _p [Decidable _p] _post =>
        wp (VeilM.assume _p : VeilM .internal ρ σ Unit) _post
       letI wpE := fun _p [Decidable _p] _post =>
        wp (VeilM.assert _p ex : VeilM .external ρ σ Unit) _post
       (match m with | .internal => wpI | .external => wpE) p post) r s := by
  cases m <;> rfl

@[wpSimp ↓]
lemma VeilExecM.wp_assert (p : Prop) {_ : Decidable p} (ex : ExId)
    (post : RProp Unit ρ σ) (r : ρ) (s : σ) :
    wp (@VeilExecM.assert m ρ σ p _ ex) post r s =
      if p then post () r s else hd ex := by
  simp [VeilExecM.assert]
  split
  · simp [_root_.wp_pure]
  simp +instances only [throw, throwThe, ReaderT.instMonadExceptOf]
  have : ∀ (α σ : Type) (m : Type -> Type) [Monad m],
      StateT.lift (σ := σ) (α := α) (m := m) = liftM := by
    simp +instances [liftM, monadLift, StateT.instMonadLift]
  simp only [MAlgLift.wp_lift]
  erw [ExceptT.wp_throw]
  simp [loomLogicSimp]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[wpSimp ↓]
lemma VeilM.wp_assert (p : Prop) {_ : Decidable p} (ex : ExId)
    (post : RProp Unit ρ σ) (r : ρ) (s : σ) :
    wp (@VeilM.assert m ρ σ p _ ex) post r s =
      if p then post () r s else hd ex := by
  simp only [assert, MAlgLift.wp_lift, monadLift_self, ↓VeilExecM.wp_assert]

@[wpSimp ↓]
lemma VeilM.wp_get {_ : IsSubStateOf σₛ σ}
    (post : RProp σₛ ρ σ) (r : ρ) (s : σ) :
    wp (get : VeilM m ρ σ σₛ) post r s = post (getFrom s) r s := by
  rfl

/-- This is used when converting transitions to actions, which require getting
the full state, not just the sub-state. -/
@[wpSimp ↓]
lemma VeilM.wp_getOf (post : RProp σ ρ σ) (r : ρ) (s : σ) :
    wp (MonadStateOf.get : VeilM m ρ σ σ) post r s = post s r s := by
  rfl

@[wpSimp ↓ high]
lemma VeilM.wp_get' (post : RProp σ ρ σ) (r : ρ) (s : σ) :
    wp (get : VeilM m ρ σ σ) post r s = post s r s := by
  rfl

@[wpSimp ↓]
lemma VeilM.wp_set {_ : IsSubStateOf σₛ σ} (s' : σₛ)
    (post : RProp Unit ρ σ) (r : ρ) (s : σ) :
    wp (set s' : VeilM m ρ σ Unit) post r s = post () r (setIn s' s) := by
  rfl

@[wpSimp ↓ high]
lemma VeilM.wp_set' (s' : σ) (post : RProp Unit ρ σ) (r : ρ) (s : σ) :
    wp (set s' : VeilM m ρ σ Unit) post r s = post () r s' := by
  rfl

@[wpSimp ↓]
lemma VeilM.wp_modifyGet {_ : IsSubStateOf σₛ σ} (f : σₛ → α × σₛ)
    (post : RProp α ρ σ) (r : ρ) (s : σ) :
    wp (modifyGet f : VeilM m ρ σ α) post r s =
      post (f (getFrom s)).1 r (setIn (f (getFrom s)).2 s) := by
  rfl

@[wpSimp ↓ high]
lemma VeilM.wp_modifyGet' (f : σ → α × σ)
    (post : RProp α ρ σ) (r : ρ) (s : σ) :
    wp (modifyGet f : VeilM m ρ σ α) post r s = post (f s).1 r (f s).2 := by
  rfl

@[wpSimp ↓]
lemma VeilM.wp_modify {_ : IsSubStateOf σₛ σ} (f : σₛ → σₛ)
    (post : RProp PUnit ρ σ) (r : ρ) (s : σ) :
    wp (modify f : VeilM m ρ σ PUnit) post r s =
      post .unit r (setIn (f (getFrom s)) s) := by
  rfl

@[wpSimp ↓ high]
lemma VeilM.wp_modify' (f : σ → σ)
    (post : RProp PUnit ρ σ) (r : ρ) (s : σ) :
    wp (modify f : VeilM m ρ σ PUnit) post r s = post .unit r (f s) := by
  rfl

@[wpSimp ↓]
lemma VeilM.wp_read {_ : IsSubReaderOf ρₛ ρ}
    (post : RProp ρₛ ρ σ) (r : ρ) (s : σ) :
    wp (read : VeilM m ρ σ ρₛ) post r s = post (readFrom r) r s := by
  rfl

@[wpSimp ↓ high]
lemma VeilM.wp_read' (post : RProp ρ ρ σ) (r : ρ) (s : σ) :
    wp (read : VeilM m ρ σ ρ) post r s = post r r s := by
  rfl

lemma VeilM.wp_pick (post : RProp τ ρ σ) (r : ρ) (s : σ) :
    wp (pick τ : VeilM m ρ σ τ) post r s = ∀ t, post t r s := by
  simp only [MonadNonDet.wp_pick, iInf, sInf, Set.mem_range, eq_iff_iff, Subtype.exists,
    exists_prop, exists_exists_eq_and, forall_exists_index]
  aesop

lemma VeilM.wp_pickSuchThat {p : τ → Prop} {_ : ∀ x, Decidable (p x)}
    (post : RProp τ ρ σ) (r : ρ) (s : σ) :
    wp (VeilM.pickSuchThat τ p : VeilM m ρ σ τ) post r s =
      ∀ t, p t → post t r s := by
  simp only [VeilM.pickSuchThat, MonadNonDet.wp_pickSuchThat, iInf, sInf, himpE,
    himpPureE, Set.mem_range, eq_iff_iff, Subtype.exists, pureE, purePropE,
    exists_prop, exists_exists_eq_and, forall_exists_index]
  aesop

@[wpSimp ↓]
lemma VeilM.wp_if [Decidable p] (a b : VeilM m ρ σ τ)
    (post : RProp τ ρ σ) (r : ρ) (s : σ) :
    wp (if p then a else b) post r s =
      if p then wp a post r s else wp b post r s := by
  split <;> rfl

-- Keep this as an unfolding rule so the binder-preserving bind simproc sees
-- the continuation introduced by `returnUnit` with its source names intact.
attribute [wpSimp ↓] VeilM.returnUnit

/-!
## Binder-preserving WP rewrites for `bind`, `pick`, and `pickSuchThat`

Applying the pointwise WP lemmas as plain simp rules replaces source binder
names from do-notation with generic ones like `x`, `x_1`, or `t`. These
simprocs perform the same rewrites and then alpha-rename the introduced
binders to match the original source names.
-/
section PickSimprocs

open Lean Meta

/-- Binder name of a lambda head, if non-anonymous. -/
private def lambdaName? (e : Expr) : Option Name :=
  match e.consumeMData with
  | .lam n .. => if n.isAnonymous then none else some n
  | _ => none

/-- Like `lambdaName?` but also rejects compiler-generated internal names. -/
private def lambdaUserName? (e : Expr) : Option Name :=
  lambdaName? e |>.filter (!·.isInternal)

private def renameBinder (n : Name) : Expr → Expr
  | .forallE _ ty b bi => .forallE n ty b bi
  | .lam     _ ty b bi => .lam     n ty b bi
  | e => e

private partial def underLambdas (f : Expr → Expr) : Expr → Expr
  | .lam n ty b bi => .lam n ty (underLambdas f b) bi
  | e => f e

/-- Rewrite `e` at the root with `lem` (one shot — no recursion into the result). -/
private def rewriteRoot? (e : Expr) (lem : Name) : MetaM (Option (Expr × Expr)) := do
  let goal ← mkFreshExprMVar (mkConst ``True)
  let r ←
    try goal.mvarId!.rewrite e (← mkConstWithFreshMVarLevels lem) (config := { occs := .pos [1] })
    catch _ => return none
  unless ← r.mvarIds.allM (·.isAssigned) do return none
  return some (← instantiateMVars r.eNew, ← instantiateMVars r.eqProof)

/-- Position of the `post` arg in a `wp ...` application (accounts for applied state). -/
private def wpPostIdx? (e : Expr) : MetaM (Option Nat) := do
  unless e.getAppFn'.isConstOf ``wp do return none
  let n := e.getAppNumArgs
  if n < 2 then return none
  let applied := (← whnf (← inferType e)).isProp && n ≥ 4
  return some (if applied then n - 3 else n - 1)

simproc_decl wpChoicePreserveBinder (_) := fun e => do
  let some postIdx ← wpPostIdx? e | return .continue
  let args := e.getAppArgs'
  let act  := args[postIdx - 1]!
  let post := args[postIdx]!
  let go (name : Name) (lem : Name) : SimpM Simp.Step := do
    let some (rhs, proof) ← rewriteRoot? e lem | return .continue
    return .visit { expr := underLambdas (renameBinder name) rhs.headBeta, proof? := some proof }
  if act.getAppFn'.isConstOf ``MonadNonDet.pick then
    go ((lambdaUserName? post).getD `t) ``VeilM.wp_pick
  else if act.getAppFn'.isConstOf ``VeilM.pickSuchThat then
    -- `let x : τ :| p` may keep the user name on the predicate, not the post lambda.
    let name ← match lambdaUserName? post with
      | some n => pure n
      | none   =>
        let p? ← act.getAppArgs'.findSomeM? fun a => do
          let .forallE _ _ b _ := ← whnf (← inferType a) | return none
          return if b.isProp then some a else none
        pure <| (p?.bind lambdaUserName?).getD `t
    go name ``VeilM.wp_pickSuchThat
  else return .continue

simproc_decl wpBindPreserveBinder (_) := fun e => do
  let some postIdx ← wpPostIdx? e | return .continue
  let act := e.getAppArgs'[postIdx - 1]!
  unless act.getAppFn'.isConstOf ``Bind.bind do return .continue
  let name := (lambdaName? act.getAppArgs'.back!).getD `x
  let some (rhs, proof) ← rewriteRoot? e ``VeilM.wp_bind | return .continue
  let some postIdx' ← wpPostIdx? rhs | return .continue
  let result := mkAppN rhs.getAppFn' (rhs.getAppArgs'.modify postIdx' (renameBinder name))
  return .visit { expr := result, proof? := some proof }

attribute [wpSimp] wpBindPreserveBinder wpChoicePreserveBinder

end PickSimprocs

/-!
## WP compactification rewrites

This is a deliberately small, proof-producing compaction pass for duplicated
postconditions in generated WPs.

The algorithm runs as `wpCompactIteSimp` post-simplification (`↑`):

1. First do the cheap guards once: the expression must be a proposition, and it
   must be an `if`.

2. Before trying to merge the current `if`, repeatedly hoist branch-local
   sharing barriers introduced by this pass:

   `if p then marked(letEq v f) else b`

   is rewritten with `ite_letEq_hoist_left`, and symmetrically for the right
   branch.  After hoisting one barrier, the algorithm recurses into the newly
   produced `letEq` continuation and keeps hoisting until the inner `if` has no
   marked `letEq` branch left.  The metadata marker is a provenance bit: only
   `letEq`s introduced by this compactification pass are hoisted.

3. Once there is no marked branch-local `letEq`, try the actual postcondition
   merge.  Since Lean applications are binary, the duplicated-continuation test
   only compares the two branches' immediate `appFn`s:

   `if p then k a₁ else k a₂`

   is rewritten with `ite_push_cond_into_arg` to

   `letEq (decide p) fun b => k (if b then a₁ else a₂)`.

The theorem `ite_push_cond_into_arg` and the hoisting theorems are intentionally
not registered as ordinary simp rules: unguarded use would rewrite unrelated
conditionals, and hoisting every `letEq` would destroy the provenance invariant.
All root rewrites below use `rewriteRoot?`, so each rewrite comes with an
equality proof.  Recursive work under a generated `letEq` continuation is lifted
back with `funext` and `congrArg`; metadata is definitionally transparent and
carries no proof obligation.
-/
section CompactSimprocs

open Lean Meta

private def wpCompactIteMarkerKey : Name := `Veil.wpCompactLetEq

private partial def wpCompactIteImpl : Simp.Simproc := fun e => do
  let e := e.consumeMData
  unless (← Meta.isProp e) && e.isIte do
    return .continue
  let result ← compactIte e
  if let some res := result then
    return .done res
  else
    return .continue
where
  iteBranches? (e : Expr) : Option (Expr × Expr) := do
    let_expr ite _ _ _ thenBranch elseBranch := e | none
    some (thenBranch, elseBranch)
  isLetEq (e : Expr) : Bool := e.isAppOfArity' ``letEq 4
  isMarkedLetEq : Expr → Bool
    | .mdata md body => md.getBool wpCompactIteMarkerKey false && isLetEq body
    | _ => false
  sameAppFn (thenBranch elseBranch : Expr) : Bool :=
    match thenBranch.consumeMData, elseBranch.consumeMData with
    | .app thenFn _, .app elseFn _ => thenFn.consumeMData == elseFn.consumeMData
    | _, _ => false
  pushSameContinuation (e thenBranch elseBranch : Expr) : SimpM (Option Simp.Result) := do
    unless sameAppFn thenBranch elseBranch do
      return none
    let some (rhs, proof) ← rewriteRoot? e ``ite_push_cond_into_arg | return none
    return some { expr := markLetEqUnchecked rhs, proof? := some proof }
  compactIte (e : Expr) : SimpM (Option Simp.Result) := do
    let some (thenBranch, elseBranch) := iteBranches? e.consumeMData | return none
    let some lem :=
      if isMarkedLetEq thenBranch then
        some ``ite_letEq_hoist_left
      else if isMarkedLetEq elseBranch then
        some ``ite_letEq_hoist_right
      else
        none
      | pushSameContinuation e thenBranch elseBranch
    let some (rhs, _) ← rewriteRoot? e lem | return none
    let afterHoist : Simp.Result := { expr := markLetEqUnchecked rhs }
    let some bodyResult ← compactMarkedLetEqBody afterHoist.expr | return some afterHoist
    return some (← afterHoist.mkEqTrans bodyResult)
  compactMarkedLetEqBody (e : Expr) : SimpM (Option Simp.Result) := do
    let .mdata md body := e | return none
    let body := body.consumeMData
    let .app letEqFn f := body | return none
    lambdaBoundedTelescope f 1 fun xs body => do
      if xs.isEmpty then
        return none
      let some bodyResult ← compactIte body | return none
      let resNew ← bodyResult.addLambdas xs
      let fNew := resNew.expr
      let funProof ← resNew.getProof
      let proof ← mkCongrArg letEqFn funProof
      return some {
        expr := .mdata md (mkApp letEqFn fNew)
        proof? := some proof
      }
  markLetEqUnchecked (e : Expr) : Expr :=
    .mdata (MData.empty.insert wpCompactIteMarkerKey (.ofBool true)) e

simproc_decl wpCompactIte (ite _ _ _) := wpCompactIteImpl

attribute [wpCompactIteSimp ↑] wpCompactIte

end CompactSimprocs


end Veil
