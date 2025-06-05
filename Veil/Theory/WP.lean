import Veil.Theory.Basic
import Veil.Theory.TwoState

open PartialCorrectness DemonicChoice

variable (hd : ExId -> Prop) [IsHandler hd]

/-- To support inter-operation between `action`s defined in different
Veil modules (which have different `State` types), we define a
sub-state relation on `State`s. This lets a module have a "part" of its
state correspond to another module's `State` type, and call `action`s
from that module by `lift`ing them into the appropriate State monad.

`IsSubState σ σ'` means that `σ` is a sub-state of `σ'`. This gives us:

- `setIn : σ -> σ' -> σ'`, which updates/sets the sub-state in the
bigger state
- `getFrom : σ' -> σ`, which extracts the sub-state from the bigger
state
- proofs that these methods are related to each other in the natural
way
-/
class IsSubStateOf (σ : outParam Type) (σ' : Type) where
  /-- Set the small state `σ` in the big one `σ'`, returning the new `σ'` -/
  setIn : σ -> σ' -> σ'
  /-- Get the small state `σ` from the big one `σ'` -/
  getFrom : σ' -> σ

  setIn_getFrom_idempotent : ∀ σ', setIn (getFrom σ') σ' = σ'
  getFrom_setIn_idempotent : ∀ σ σ', getFrom (setIn σ σ') = σ

export IsSubStateOf (setIn getFrom)

@[wpSimp, initSimp, actSimp] instance : IsSubStateOf σ σ where
  setIn := (fun σₛ σ => σₛ)
  getFrom := id
  setIn_getFrom_idempotent := by simp
  getFrom_setIn_idempotent := by simp

attribute [wpSimp, initSimp, actSimp] id IsSubStateOf.setIn_getFrom_idempotent IsSubStateOf.getFrom_setIn_idempotent

def IsSubStateOf.trans {σₛ σₘ σ : Type} (S₁ : IsSubStateOf σₛ σₘ) (S₂ : IsSubStateOf σₘ σ) : IsSubStateOf σₛ σ :=
{
  setIn := fun σₛ σ => let σₘ := (S₂.getFrom σ); S₂.setIn (S₁.setIn σₛ σₘ) σ
  getFrom := fun σ => S₁.getFrom (S₂.getFrom σ)
  setIn_getFrom_idempotent := by simp [S₁.setIn_getFrom_idempotent, S₂.setIn_getFrom_idempotent]
  getFrom_setIn_idempotent := by simp [S₁.getFrom_setIn_idempotent, S₂.getFrom_setIn_idempotent]
}

instance (priority := high + 1) [IsSubStateOf σₛ σ] [Monad m] : MonadStateOf σₛ (StateT σ m) where
  get         := getFrom <$> get
  set s       := modify <| setIn s
  modifyGet f := modifyGet fun s => let ⟨a, s'⟩ := f (getFrom s); (a, setIn s' s)

instance (priority := high + 1) [IsSubStateOf σₛ σ] [Monad m] : MonadReaderOf σₛ (ReaderT σ m) where
  read := getFrom <$> read

/- Languge constructs -/

def VeilExecM.assert (p : Prop) [Decidable p] (ex : ExId) : VeilExecM m ρ σ Unit := do
  if p then pure () else throw ex

def VeilM.assert (p : Prop) [Decidable p] (ex : ExId) : VeilM m ρ σ Unit := do
  liftM (@VeilExecM.assert m ρ σ p _ ex)

def VeilM.require (p : Prop) [Decidable p] (ex : ExId) : VeilM m ρ σ Unit := do
  match m with
  | .internal => VeilM.assert p ex
  | .external => assume p

@[wpSimp]
lemma VeilExecM.wp_assume :
  wp (assume p : VeilM m ρ σ PUnit) post = fun r s => p -> post .unit r s := by
  simp [MonadNonDet.wp_assume, loomLogicSimp, himp];

@[wpSimp]
lemma VeilM.wp_require (p : Prop) [Decidable p] (ex : ExId) :
  wp (require p ex : VeilM m ρ σ Unit) post =
    match m with
    | .internal => wp (VeilM.assert p ex : VeilM m ρ σ Unit) post
    | .external => wp (assume p : VeilM m ρ σ PUnit) post := by
  cases m <;> rfl


@[wpSimp]
lemma VeilExecM.wp_assert (p : Prop) {_ : Decidable p} (ex : ExId) :
  wp (@VeilExecM.assert m ρ σ p _ ex) post = fun r s => if p then post () r s else hd ex := by
  simp [VeilExecM.assert]; split
  { simp [wp_pure] }
  simp [throw, throwThe, ReaderT.instMonadExceptOf, StateT.instMonadExceptOf]
  have : ∀ (α σ : Type) (m : Type -> Type) [Monad m], StateT.lift (σ := σ) (α := α) (m := m) = liftM := by
    simp [liftM, monadLift, StateT.instMonadLift]
  simp [this, MPropLift.wp_lift]; erw [ExceptT.wp_throw]
  simp [loomLogicSimp]

@[wpSimp]
lemma VeilM.wp_assert (p : Prop) {_ : Decidable p} (ex : ExId) :
  wp (@VeilM.assert m ρ σ p _ ex) post = fun r s => if p then post () r s else hd ex := by
  simp [VeilM.assert, MPropLift.wp_lift, wpSimp]

@[wpSimp]
lemma VeilM.wp_get {_ : IsSubStateOf σₛ σ} :
  wp (get : VeilM m ρ σ σₛ) post = fun r s => post (getFrom s) r s := by
  simp [get, getThe, MonadStateOf.get, MPropLift.wp_lift]; ext
  erw [StateT.wp_get]

@[wpSimp]
lemma VeilM.wp_modifyGet {_ : IsSubStateOf σₛ σ} :
  wp (modifyGet f : VeilM m ρ σ α) post = fun r s => post (f (getFrom s)).1 r (setIn (f (getFrom s)).2 s) := by
  simp [modifyGet, MonadStateOf.modifyGet, MPropLift.wp_lift]; ext
  erw [StateT.wp_modifyGet]

@[wpSimp]
lemma VeilExecM.wp_read {_ : IsSubStateOf ρₛ ρ} :
  wp (read : VeilExecM m ρ σ ρₛ) post = fun r s => post (getFrom r) r s := by
  simp [read, getThe, MonadReaderOf.read, MPropLift.wp_lift]; ext
  erw [ReaderT.wp_read]

@[wpSimp]
lemma VeilM.wp_pick :
  wp (pick τ : VeilM m ρ σ τ) post = fun r s => ∀ t, post t r s := by
  simp [MonadNonDet.wp_pick, loomLogicSimp, himp, iInf, sInf]; aesop

@[wpSimp]
lemma VeilM.wp_pickSuchThat :
  wp (pickSuchThat τ p : VeilM m ρ σ τ) post = fun r s => ∀ t, p t -> post t r s := by
  simp [MonadNonDet.wp_pickSuchThat, loomLogicSimp, himp, iInf, sInf]; aesop

@[wpSimp]
lemma VeilM.wp_if [Decidable p] :
  wp (if p then a else b : VeilM m ρ σ τ) post =
  if p then wp a post else wp b post := by
  split_ifs <;> simp

attribute [wpSimp] wp_pure wp_bind wp_map wp_bind
