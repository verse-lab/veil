import Veil.Frontend.DSL.Infra.Simp

class IsSubReaderOf (ρ : outParam Type) (ρ' : Type) where
  /-- Get the small state `ρ` from the big one `ρ'` -/
  readFrom : ρ' -> ρ

export IsSubReaderOf (readFrom)

attribute [wpSimp, substateSimp ↓, actSimp] IsSubReaderOf.readFrom

instance (priority := high) [IsSubReaderOf σₛ σ] [Monad m] : MonadReaderOf σₛ (ReaderT σ m) where
  read := readFrom <$> read

@[wpSimp ↓, substateSimp ↓, actSimp]
instance instIsSubReaderOfRefl : IsSubReaderOf ρ ρ where
  readFrom := id

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

  setIn_getFrom_idempotent    : ∀ σ', setIn (getFrom σ') σ' = σ'
  setIn_setIn_last            : ∀ σ₁ σ₂ σ', setIn σ₂ (setIn σ₁ σ') = setIn σ₂ σ'
  getFrom_setIn_idempotent    : ∀ σ σ', getFrom (setIn σ σ') = σ

export IsSubStateOf (setIn getFrom)

attribute [wpSimp, substateSimp ↓, actSimp] id IsSubStateOf.setIn_getFrom_idempotent IsSubStateOf.setIn_setIn_last IsSubStateOf.getFrom_setIn_idempotent

@[wpSimp, substateSimp ↓, actSimp]
instance instIsSubStateOfRefl : IsSubStateOf σ σ where
  setIn := (fun σₛ σ => σₛ)
  getFrom := id
  setIn_getFrom_idempotent := by simp
  setIn_setIn_last         := by simp
  getFrom_setIn_idempotent := by simp

def IsSubStateOf.trans {σₛ σₘ σ : Type} (S₁ : IsSubStateOf σₛ σₘ) (S₂ : IsSubStateOf σₘ σ) : IsSubStateOf σₛ σ :=
{
  setIn := fun σₛ σ => let σₘ := (S₂.getFrom σ); S₂.setIn (S₁.setIn σₛ σₘ) σ
  getFrom := fun σ => S₁.getFrom (S₂.getFrom σ)
  setIn_getFrom_idempotent := by simp [setIn_getFrom_idempotent]
  setIn_setIn_last         := by simp [getFrom_setIn_idempotent, setIn_setIn_last]
  getFrom_setIn_idempotent := by simp [getFrom_setIn_idempotent]
}

instance (priority := high + 1) [IsSubStateOf σₛ σ] [Monad m] : MonadStateOf σₛ (StateT σ m) where
  get         := getFrom <$> get
  set s       := modify <| setIn s
  modifyGet f := modifyGet fun s => let ⟨a, s'⟩ := f (getFrom s); (a, setIn s' s)

/-- Used in transition-style goals to ensure the post-state is an
explicit hypothesis, so it gets included in models returned by SMT. -/
theorem setIn_makeExplicit {σₛ σ : Type} {S : IsSubStateOf σₛ σ} {x : σₛ} {pre : σ} (post : σ) :
  setIn x pre = post ↔ (∃ st', st' = x ∧ setIn st' pre = post) := by
    constructor
    { intro h; exists x }
    { rintro ⟨s₁, ⟨heq, h⟩⟩; rw [← heq]; apply h}
