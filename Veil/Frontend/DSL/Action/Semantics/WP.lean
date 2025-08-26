import Veil.Frontend.DSL.Action.Semantics.Definitions
import Veil.Frontend.DSL.State
import Veil.Frontend.DSL.SimpAttrs

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
def VeilM.assume (p : Prop) [Decidable p] : VeilM m ρ σ PUnit := do
  MonadNonDet.assume p

/-- We require the predicate to be `Decidable`, even though `assume`
does not, in order to collect the appropriate instances needed for
execution. -/
def VeilM.pickSuchThat (τ : Type) (p : τ → Prop) [∀ x, Decidable (p x)] : VeilM m ρ σ τ := do
  MonadNonDet.pickSuchThat τ p

@[doSimp]
def VeilM.require (p : Prop) [Decidable p] (ex : ExId) : VeilM m ρ σ Unit := do
  match m with
  | .internal => VeilM.assert p ex
  | .external => assume p

@[doSimp]
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
@[doSimp, reducible]
def VeilM.returnUnit (act : VeilM m ρ σ α) : VeilM m ρ σ Unit := do
  let _ ← act
  return ()

@[wpSimp]
lemma VeilExecM.wp_assume :
  wp (assume p : VeilM m ρ σ PUnit) post = fun r s => p -> post .unit r s := by
  simp [MonadNonDet.wp_assume, loomLogicSimp, himp];

@[wpSimp]
lemma VeilM.wp_require (p : Prop) [Decidable p] (ex : ExId) :
  wp (require p ex : VeilM m ρ σ Unit) post =
    match m with
    | .internal => wp (VeilM.assert p ex : VeilM .internal ρ σ Unit) post
    | .external => wp (      assume p    : VeilM .external ρ σ PUnit) post := by
  cases m <;> rfl

@[wpSimp]
lemma VeilM.wp_ensure (p : Prop) [Decidable p] (ex : ExId) :
  wp (ensure p ex : VeilM m ρ σ Unit) post =
    match m with
    | .internal => wp (      assume p    : VeilM .internal ρ σ PUnit) post
    | .external => wp (VeilM.assert p ex : VeilM .external ρ σ Unit) post := by
  cases m <;> rfl

@[wpSimp]
lemma VeilExecM.wp_assert (p : Prop) {_ : Decidable p} (ex : ExId) :
  wp (@VeilExecM.assert m ρ σ p _ ex) post = fun r s => if p then post () r s else hd ex := by
  simp [VeilExecM.assert]; split
  { simp [wp_pure] }
  simp only [throw, throwThe, ReaderT.instMonadExceptOf, StateT.instMonadExceptOf,
    Function.comp_apply]
  have : ∀ (α σ : Type) (m : Type -> Type) [Monad m], StateT.lift (σ := σ) (α := α) (m := m) = liftM := by
    simp [liftM, monadLift, StateT.instMonadLift]
  simp only [this, MAlgLift.wp_lift, lift_cont_eq]; erw [ExceptT.wp_throw]
  simp [loomLogicSimp]

@[wpSimp]
lemma VeilM.wp_assert (p : Prop) {_ : Decidable p} (ex : ExId) :
  wp (@VeilM.assert m ρ σ p _ ex) post = fun r s => if p then post () r s else hd ex := by
  simp [VeilM.assert, MAlgLift.wp_lift, wpSimp]

@[wpSimp]
lemma VeilM.wp_get {_ : IsSubStateOf σₛ σ} :
  wp (get : VeilM m ρ σ σₛ) post = fun r s => post (getFrom s) r s := by
  simp only [get, getThe, MonadStateOf.get, MAlgLift.wp_lift, lift_cont_eq, monadLift_self]; ext
  erw [StateT.wp_get]

@[wpSimp low]
lemma VeilM.wp_get' :
  wp (get : VeilM m ρ σ σ) post = fun r s => post s r s := by
  simp only [get, getThe, MonadStateOf.get, MAlgLift.wp_lift, lift_cont_eq, monadLift_self]; ext
  erw [StateT.wp_get]

@[wpSimp]
lemma VeilM.wp_set {_ : IsSubStateOf σₛ σ} :
  wp (set s': VeilM m ρ σ Unit) post = fun r s => post () r (setIn s' s) := by
  simp only [set, modify, modifyGet, MonadStateOf.modifyGet, MAlgLift.wp_lift, lift_cont_eq,
    monadLift_self]; ext
  erw [StateT.wp_modifyGet]

@[wpSimp low]
lemma VeilM.wp_set' :
  wp (set s': VeilM m ρ σ Unit) post = fun r _s => post () r s' := by
  simp only [set, modify, modifyGet, MonadStateOf.modifyGet, MAlgLift.wp_lift, lift_cont_eq,
    monadLift_self]; ext
  erw [StateT.wp_modifyGet]; rfl

@[wpSimp]
lemma VeilM.wp_modifyGet {_ : IsSubStateOf σₛ σ} :
  wp (modifyGet f : VeilM m ρ σ α) post = fun r s => post (f (getFrom s)).1 r (setIn (f (getFrom s)).2 s) := by
  simp only [modifyGet, MonadStateOf.modifyGet, MAlgLift.wp_lift, lift_cont_eq, monadLift_self]; ext
  erw [StateT.wp_modifyGet]

@[wpSimp low]
lemma VeilM.wp_modifyGet' :
  wp (modifyGet f : VeilM m ρ σ α) post = fun r s => post (f s).1 r (f s).2 := by
  simp only [modifyGet, MonadStateOf.modifyGet, MAlgLift.wp_lift, lift_cont_eq, monadLift_self]; ext
  erw [StateT.wp_modifyGet]; rfl

@[wpSimp]
lemma VeilM.wp_read {_ : IsSubReaderOf ρₛ ρ} :
  wp (read : VeilM m ρ σ ρₛ) post = fun r s => post (readFrom r) r s := by
  simp only [read, readThe, MonadReaderOf.read, MAlgLift.wp_lift, monadLift_self]; ext
  erw [ReaderT.wp_read]

@[wpSimp low]
lemma VeilM.wp_read' :
  wp (read : VeilM m ρ σ ρ) post = fun r s => post r r s := by
  simp only [read, readThe, MonadReaderOf.read, MAlgLift.wp_lift, monadLift_self]; ext
  erw [ReaderT.wp_read]

@[wpSimp]
lemma VeilM.wp_pick :
  wp (pick τ : VeilM m ρ σ τ) post = fun r s => ∀ t, post t r s := by
  simp only [MonadNonDet.wp_pick, iInf, sInf, Set.mem_range, eq_iff_iff, Subtype.exists,
    exists_prop, exists_exists_eq_and, forall_exists_index]; aesop

@[wpSimp]
lemma VeilM.wp_pickSuchThat {m : Mode} {ρ σ τ : Type} {p : τ → Prop} {_ : ∀ x, Decidable (p x)} {post : τ → ρ → σ → Prop} :
  wp (VeilM.pickSuchThat τ p : VeilM m ρ σ τ) post = fun r s => ∀ t, p t -> post t r s := by
  simp only [VeilM.pickSuchThat, MonadNonDet.wp_pickSuchThat, iInf, sInf, himpE, himpPureE, Set.mem_range, eq_iff_iff,
    Subtype.exists, pureE, purePropE, exists_prop, exists_exists_eq_and, forall_exists_index]
  aesop

@[wpSimp]
lemma VeilM.wp_if [Decidable p] :
  wp (if p then a else b : VeilM m ρ σ τ) post =
  if p then wp a post else wp b post := by
  split_ifs <;> simp only

attribute [wpSimp] wp_pure wp_bind wp_map wp_bind

end Veil
