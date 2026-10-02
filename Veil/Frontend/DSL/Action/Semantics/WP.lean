module

public import Batteries.Lean.Expr
public meta import Batteries.Lean.Expr
public import Veil.Frontend.DSL.Action.Semantics.Definitions
public import Veil.Frontend.DSL.State.SubState
public meta import Veil.Frontend.DSL.Infra.Simp

public section

open Loom.Order
open scoped Loom.Order

namespace Veil
open PartialCorrectness DemonicChoice

variable (hd : ExId -> Prop) [IsHandler hd]

/- Languge constructs -/

@[expose] def VeilExecM.assert (p : Prop) [Decidable p] (ex : ExId) : VeilExecM m ρ σ Unit := do
  if p then pure () else throw ex

@[expose] def VeilM.assert (p : Prop) [Decidable p] (ex : ExId) : VeilM m ρ σ Unit := do
  liftM (@VeilExecM.assert m ρ σ p _ ex)

/-- We require the predicate to be `Decidable`, even though `assume`
does not, in order to collect the appropriate instances needed for
execution. -/
@[reducible, expose] def VeilM.assume (p : Prop) [Decidable p] : VeilM m ρ σ PUnit := do
  MonadNonDet.assume p

/-- We require the predicate to be `Decidable`, even though `assume`
does not, in order to collect the appropriate instances needed for
execution. -/
@[expose] def VeilM.pickSuchThat (τ : Type) (p : τ → Prop) [∀ x, Decidable (p x)] : VeilM m ρ σ τ := do
  MonadNonDet.pickSuchThat τ p

@[expose] def VeilM.require (p : Prop) [Decidable p] (ex : ExId) : VeilM m ρ σ Unit := do
  match m with
  | .internal => VeilM.assert p ex
  | .external => assume p

@[expose] def VeilM.ensure (p : Prop) [Decidable p] (ex : ExId) : VeilM m ρ σ Unit := do
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
@[reducible, expose] def VeilM.returnUnit (act : VeilM m ρ σ α) : VeilM m ρ σ Unit := do
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

theorem VeilM.wp_bind (act : VeilM m ρ σ α) (f : α → VeilM m ρ σ β)
    (post : RProp β ρ σ) (r : ρ) (s : σ) :
    wp (act >>= f) post r s = wp act (fun x => wp (f x) post) r s := by
  rw [_root_.wp_bind]

@[wpSimp ↓]
theorem VeilM.wp_pure (x : α) (post : RProp α ρ σ) (r : ρ) (s : σ) :
    wp (pure x : VeilM m ρ σ α) post r s = post x r s := by
  rw [_root_.wp_pure]

@[wpSimp ↓]
theorem VeilM.wp_map (act : VeilM m ρ σ α) (f : α → β)
    (post : RProp β ρ σ) (r : ρ) (s : σ) :
    wp (f <$> act) post r s = wp act (fun x => post (f x)) r s := by
  rw [_root_.wp_map]

@[wpSimp ↓]
theorem VeilExecM.wp_assume (p : Prop) [Decidable p]
    (post : RProp PUnit ρ σ) (r : ρ) (s : σ) :
    wp (VeilM.assume p : VeilM m ρ σ PUnit) post r s = (p → post .unit r s) := by
  simp [VeilM.assume, MonadNonDet.wp_assume, loomLogicSimp]

/-- This formulation avoids a blowup in formula size by avoiding copies of `post`. -/
@[wpSimp ↓]
theorem VeilM.wp_require (p : Prop) [Decidable p] (ex : ExId)
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
theorem VeilM.wp_ensure (p : Prop) [Decidable p] (ex : ExId)
    (post : RProp Unit ρ σ) (r : ρ) (s : σ) :
    wp (VeilM.ensure p ex : VeilM m ρ σ Unit) post r s =
      (letI wpI := fun _p [Decidable _p] _post =>
        wp (VeilM.assume _p : VeilM .internal ρ σ Unit) _post
       letI wpE := fun _p [Decidable _p] _post =>
        wp (VeilM.assert _p ex : VeilM .external ρ σ Unit) _post
       (match m with | .internal => wpI | .external => wpE) p post) r s := by
  cases m <;> rfl

@[wpSimp ↓]
theorem VeilExecM.wp_assert (p : Prop) {_ : Decidable p} (ex : ExId)
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
theorem VeilM.wp_assert (p : Prop) {_ : Decidable p} (ex : ExId)
    (post : RProp Unit ρ σ) (r : ρ) (s : σ) :
    wp (@VeilM.assert m ρ σ p _ ex) post r s =
      if p then post () r s else hd ex := by
  simp only [assert, MAlgLift.wp_lift, monadLift_self, ↓VeilExecM.wp_assert]

@[wpSimp ↓]
theorem VeilM.wp_get {_ : IsSubStateOf σₛ σ}
    (post : RProp σₛ ρ σ) (r : ρ) (s : σ) :
    wp (get : VeilM m ρ σ σₛ) post r s = post (getFrom s) r s := by
  rfl

/-- This is used when converting transitions to actions, which require getting
the full state, not just the sub-state. -/
@[wpSimp ↓]
theorem VeilM.wp_getOf (post : RProp σ ρ σ) (r : ρ) (s : σ) :
    wp (MonadStateOf.get : VeilM m ρ σ σ) post r s = post s r s := by
  rfl

@[wpSimp ↓ high]
theorem VeilM.wp_get' (post : RProp σ ρ σ) (r : ρ) (s : σ) :
    wp (get : VeilM m ρ σ σ) post r s = post s r s := by
  rfl

@[wpSimp ↓]
theorem VeilM.wp_set {_ : IsSubStateOf σₛ σ} (s' : σₛ)
    (post : RProp Unit ρ σ) (r : ρ) (s : σ) :
    wp (set s' : VeilM m ρ σ Unit) post r s = post () r (setIn s' s) := by
  rfl

@[wpSimp ↓ high]
theorem VeilM.wp_set' (s' : σ) (post : RProp Unit ρ σ) (r : ρ) (s : σ) :
    wp (set s' : VeilM m ρ σ Unit) post r s = post () r s' := by
  rfl

@[wpSimp ↓]
theorem VeilM.wp_modifyGet {_ : IsSubStateOf σₛ σ} (f : σₛ → α × σₛ)
    (post : RProp α ρ σ) (r : ρ) (s : σ) :
    wp (modifyGet f : VeilM m ρ σ α) post r s =
      post (f (getFrom s)).1 r (setIn (f (getFrom s)).2 s) := by
  rfl

@[wpSimp ↓ high]
theorem VeilM.wp_modifyGet' (f : σ → α × σ)
    (post : RProp α ρ σ) (r : ρ) (s : σ) :
    wp (modifyGet f : VeilM m ρ σ α) post r s = post (f s).1 r (f s).2 := by
  rfl

@[wpSimp ↓]
theorem VeilM.wp_modify {_ : IsSubStateOf σₛ σ} (f : σₛ → σₛ)
    (post : RProp PUnit ρ σ) (r : ρ) (s : σ) :
    wp (modify f : VeilM m ρ σ PUnit) post r s =
      post .unit r (setIn (f (getFrom s)) s) := by
  rfl

@[wpSimp ↓ high]
theorem VeilM.wp_modify' (f : σ → σ)
    (post : RProp PUnit ρ σ) (r : ρ) (s : σ) :
    wp (modify f : VeilM m ρ σ PUnit) post r s = post .unit r (f s) := by
  rfl

@[wpSimp ↓]
theorem VeilM.wp_read {_ : IsSubReaderOf ρₛ ρ}
    (post : RProp ρₛ ρ σ) (r : ρ) (s : σ) :
    wp (read : VeilM m ρ σ ρₛ) post r s = post (readFrom r) r s := by
  rfl

@[wpSimp ↓ high]
theorem VeilM.wp_read' (post : RProp ρ ρ σ) (r : ρ) (s : σ) :
    wp (read : VeilM m ρ σ ρ) post r s = post r r s := by
  rfl

theorem VeilM.wp_pick (post : RProp τ ρ σ) (r : ρ) (s : σ) :
    wp (pick τ : VeilM m ρ σ τ) post r s = ∀ t, post t r s := by
  simp [MonadNonDet.wp_pick, loomLogicSimp]


theorem VeilM.wp_pickSuchThat {p : τ → Prop} {_ : ∀ x, Decidable (p x)}
    (post : RProp τ ρ σ) (r : ρ) (s : σ) :
    wp (VeilM.pickSuchThat τ p : VeilM m ρ σ τ) post r s =
      ∀ t, p t → post t r s := by
  simp [VeilM.pickSuchThat, MonadNonDet.wp_pickSuchThat, loomLogicSimp]


@[wpSimp ↓]
theorem VeilM.wp_if [Decidable p] (a b : VeilM m ρ σ τ)
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
meta section PickSimprocs

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
private meta def rewriteRoot? (e : Expr) (lem : Name) : MetaM (Option (Expr × Expr)) := do
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
  let applied := (← whnf (← inferType e)).isProp && Nat.ble 4 n
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

The algorithm runs as `wpCompactIteSimp` post-simplification (`↑`), so the
branches of a conditional have already been compacted when the conditional
itself is visited:

1. First do the cheap guards once: the expression must be a proposition, and it
   must be an `if`.

2. Hoist the sharing barriers introduced by this pass out of both branches.
   For example,

   `if p then marked(letEq v f) else b`

   becomes `letEq v fun a => if p then f a else b` (`ite_letEq_hoist_left`), and
   symmetrically for the right branch; a branch may start with a chain of such
   barriers, which are hoisted one after the other.  A barrier is identified by
   its value: when the other branch, or an outer barrier of the same branch,
   already provided a barrier with the same value, the two are merged into one
   binder instead of nesting two `letEq`s of the same value.  This matters for
   sequences of conditionals: `if c₁ …; if c₂ …` yields a copy of the `c₂`
   conditional in each branch of `c₁`, and the merge keeps the number of
   barriers linear in the number of conditionals rather than exponential.

   `marked(…)` is the metadata marker `wpCompactIteMarkerKey` on the `letEq`
   application.  It is a provenance bit: every `letEq` produced by this pass
   (in step 2 or step 3) carries it, and only marked `letEq`s are hoisted or
   merged.  `letEq`s that were already in the WP, such as the ones standing for
   `let` statements of the action, stay where they are.

3. Once no marked `letEq` is left on top of either branch, try the actual
   postcondition merge.  Since Lean applications are binary, the
   duplicated-continuation test only compares the two branches' immediate
   `appFn`s:

   `if p then k a₁ else k a₂`

   is rewritten with `ite_push_cond_into_arg` to

   `marked(letEq (decide p) fun b => k (if b then a₁ else a₂))`.

The theorem `ite_push_cond_into_arg` and the hoisting theorems are intentionally
not registered as ordinary simp rules: unguarded use would rewrite unrelated
conditionals, and hoisting every `letEq` would destroy the provenance invariant.
Step 3 uses `rewriteRoot?`, so the merge comes with an equality proof, which is
lifted back through the hoisted binders with `funext` and `congrArg`.  Step 2
needs no proof: hoisting and merging barriers only unfolds `letEq`, so the
rebuilt chain is definitionally equal to the conditional it came from (the
hoisting theorems are `rfl`), and metadata is definitionally transparent.
-/
meta section CompactSimprocs

open Lean Meta

private def wpCompactIteMarkerKey : Name := `Veil.wpCompactLetEq

/-- A barrier hoisted out of the conditional being compacted. -/
private structure HoistedBarrier where
  /-- The value `v` of the barrier's `letEq`.  Barriers with the same value are
  merged. -/
  value : Expr
  /-- The barrier's `letEq` application without its continuation, `@letEq α β v`.
  Applying it to a new continuation rebuilds the barrier, and it is the function
  `congrArg` is applied to when the proof of the merged continuation is lifted
  through the barrier's binder. -/
  head : Expr
  /-- The local variable standing for the bound value while the conditional is
  rebuilt; the rebuilt barrier binds it again. -/
  var : Expr

private meta partial def wpCompactIteImpl : Simp.Simproc := fun e => do
  let e := e.consumeMData
  unless (← Meta.isProp e) && e.isIte do
    return .continue
  let some res ← compactIte e | return .continue
  return .done res
where
  /-- The barrier `e` stands for, if `e` is a `letEq` carrying the provenance
  marker: the `letEq` application, the type of its value, the value, and the
  continuation. -/
  markedLetEq? (e : Expr) : Option (Expr × Expr × Expr × Expr) := do
    let .mdata md letEqApp := e | none
    guard <| md.getBool wpCompactIteMarkerKey false
    let_expr letEq α _ value f := letEqApp | none
    return (letEqApp, α, value, f)
  markLetEqUnchecked (e : Expr) : Expr :=
    .mdata (MData.empty.insert wpCompactIteMarkerKey (.ofBool true)) e
  sameAppFn (thenBranch elseBranch : Expr) : Bool :=
    match thenBranch.consumeMData, elseBranch.consumeMData with
    | .app thenFn _, .app elseFn _ => thenFn.consumeMData == elseFn.consumeMData
    | _, _ => false
  pushSameContinuation (e thenBranch elseBranch : Expr) : SimpM (Option Simp.Result) := do
    unless sameAppFn thenBranch elseBranch do
      return none
    let some (rhs, proof) ← rewriteRoot? e ``ite_push_cond_into_arg | return none
    return some { expr := markLetEqUnchecked rhs, proof? := some proof }
  /-- Hoist the chain of marked barriers off `branch`, then continue with the
  barriers collected so far and the chain's body, in which every barrier has
  been replaced by its variable.  A barrier whose value is that of an already
  collected barrier (from this branch or the other one) reuses that variable
  instead of being collected again. -/
  hoistBarriers (barriers : Array HoistedBarrier) (branch : Expr)
      (k : Array HoistedBarrier → Expr → SimpM (Option Simp.Result)) : SimpM (Option Simp.Result) := do
    let some (letEqApp, α, value, f) := markedLetEq? branch | k barriers branch
    if let some b := barriers.find? (·.value == value) then
      hoistBarriers barriers (f.beta #[b.var]) k
    else
      let name := match f with | .lam n .. => n | _ => `b
      withLocalDeclD name α fun x =>
        hoistBarriers (barriers.push { value, head := letEqApp.appFn!, var := x }) (f.beta #[x]) k
  compactIte (e : Expr) : SimpM (Option Simp.Result) := do
    let e := e.consumeMData
    let_expr ite α c inst thenBranch elseBranch := e | return none
    hoistBarriers #[] thenBranch fun barriers thenBody =>
    hoistBarriers barriers elseBranch fun barriers elseBody => do
      let inner := mkApp5 e.getAppFn α c inst thenBody elseBody
      let pushed? ← pushSameContinuation inner thenBody elseBody
      if barriers.isEmpty then
        return pushed?
      -- Rebuild the chain of barriers around the conditional (or around the
      -- merged continuation).  `e` and the rebuilt chain are definitionally
      -- equal, so only the proof of the merge has to be lifted through the
      -- binders.
      let res ← barriers.foldrM (init := pushed?.getD { expr := inner }) fun b res => do
        let res ← res.addLambdas #[b.var]
        return {
          expr := markLetEqUnchecked (mkApp b.head res.expr)
          proof? := ← res.proof?.mapM fun h => mkCongrArg b.head h
        }
      return some res

simproc_decl wpCompactIte (ite _ _ _) := wpCompactIteImpl

attribute [wpCompactIteSimp ↑] wpCompactIte

end CompactSimprocs


end Veil
