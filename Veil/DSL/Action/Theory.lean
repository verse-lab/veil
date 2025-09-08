import Veil.DSL.Base

/-!
  # Action Language

  This file defines the semantics for the imperative language we use to
  define initializers and actions.
-/
section Veil
open Classical
/-! ## Types  -/
section Types

/-- Actions in Veil can be elaborated in two ways:

- `internal`: when we call an action, callee should ensure all
`require`s are satisfied. That is, under this interpretation, `require
P` is equivalent to `assert P`.

- `external`: when we call an action, it's the environment's
responsibility to ensure `require`s are satisfied. We treat `require`s
as `assume`s under this interpretation. Only top-level actions should
be interpreted as `external`.

See the definition of `Wp.require`.
-/
inductive Mode where
  | internal : Mode
  | external : Mode
deriving BEq

/-! Our language is parametric over the state and return type. -/
variable (m : Mode) (σ ρ : Type)

/-- One-state formula -/
@[inline] abbrev SProp := σ -> Prop
/-- One-state formula that also talks about the return value. -/
@[inline] abbrev RProp (ρ : Type u) := ρ → SProp σ
/-- Two-state formula -/
@[inline] abbrev TwoState := σ -> σ -> Prop


/-!
In Veil we use two different semantics:

- [Wp]: a weakest-precondition transformer expressed in [Omni
semantics](https://doi.org/10.1145/3579834) style; this relates a state
`s : σ` to set of the possible program outcomes `post : RProp σ`

- [BigStep]: standard big-step semantics, which relates a state `s : σ`
to a return value `r : ρ` and a post-state `s' : σ`; we use this to
cast Veil `action`s into two-state `transition`s
-/

set_option linter.unusedVariables false in
/-- Weakest precondition semantics in Omni style. This is a
specification monad which relates a state `s : σ` to the set of the
possible program outcomes `post : RProp σ`.

We have two modes for this monad:
- `internal`, for function calls, which treats `require` statements as
  `assert`'s

- `external`, for environment calls, which treats `require` statements as
  `assume`'s. It's the environment's responsibility to ensure `require`s are
  satisfied.
-/
abbrev Wp (m : Mode) (σ ρ : Type) := σ -> RProp σ ρ -> Prop

set_option linter.unusedVariables false in
-- /-- Weakest-liberal-precondition semantics. -/
abbrev Wlp (m : Mode) (σ ρ : Type) := σ -> RProp σ ρ -> Prop

/-- Standard big-step semantics, which relates a state `s : σ` to a
return value `r : ρ` and a post-state `s' : σ` -/
abbrev BigStep := σ -> ρ -> σ -> Prop

end Types

/-! ## Theory  -/
section Theory

variable {σ ρ : Type}

/-! ### Weakest Precondition Semantics -/

@[actSimp] def Wp.pure (r : ρ) : Wp m σ ρ := fun s post => post r s
@[actSimp] def Wp.bind (wp : Wp m σ ρ) (wp_cont : ρ -> Wp m σ ρ') : Wp m σ ρ' :=
  fun s post => wp s (fun r s' => wp_cont r s' post)

@[actSimp] def Wp.assume (asm : Prop) : Wp m σ PUnit := fun s post => asm → post () s
@[actSimp] def Wp.assert (ast : Prop) : Wp m σ PUnit := fun s post => ast ∧ post () s
@[actSimp] def Wp.require (rq : Prop) : Wp m σ PUnit :=
  match m with
  | Mode.internal => Wp.assert rq
  | Mode.external => Wp.assume rq

@[actSimp] def Wp.fresh (τ : Type) : Wp m σ τ := fun s post => ∀ t, post t s

@[actSimp] def Wp.get : Wp m σ σ := fun s post => post s s
@[actSimp] def Wp.set (s' : σ) : Wp m σ Unit := fun _ post => post () s'
@[actSimp] def Wp.modifyGet (act : σ -> ρ × σ) : Wp m σ ρ := fun s post => let (ret, s') := act s ; post ret s'

/-- `Wp.spec req ens` is the weakest precondition for a function with
  precondition `req` and postcondition `ens`.
-/
@[actSimp] def Wp.spec (req : SProp σ) (ens : σ -> RProp σ ρ) : Wp m σ ρ :=
  fun s post =>
    match m with
    | .internal => req s ∧ ∀ r' s', (ens s r' s' -> post r' s')
    | .external => ∀ r' s', req s -> ens s r' s' -> post r' s'

/-! #### Monad Instances -/

/-- `Wp` is a monad -/
instance : Monad (Wp m σ) where
  pure := Wp.pure
  bind := Wp.bind

/-- `Wp` is a state monad -/
instance : MonadStateOf σ (Wp m σ) where
  get := Wp.get
  set := Wp.set
  modifyGet := Wp.modifyGet

/-! #### State Monad Lifting-/

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
class IsSubStateOf (σ : semiOutParam Type) (σ' : Type) where
  /-- Set the small state `σ` in the big one `σ'`, returning the new `σ'` -/
  setIn : σ -> σ' -> σ'
  /-- Get the small state `σ` from the big one `σ'` -/
  getFrom : σ' -> σ

  setIn_getFrom_idempotent : ∀ σ', setIn (getFrom σ') σ' = σ'
  getFrom_setIn_idempotent : ∀ σ σ', getFrom (setIn σ σ') = σ

export IsSubStateOf (setIn getFrom)

/-- `Wp.lift act` lifts an action defined on a sub-state into an action
defined on the bigger state. -/
@[actSimp] def Wp.lift {σ σ'} [IsSubStateOf σ σ'] (act : Wp m σ ρ) : Wp m σ' ρ :=
  fun s' post => act (getFrom s') (fun r s => post r (setIn s s'))

/-- `Wp` supports lifting between different state monads. -/
instance [IsSubStateOf σ σ'] : MonadLift (Wp m σ) (Wp m σ') where
  monadLift := Wp.lift

/-! We want to unfold the monad definitions (e.g. for `pure`, `bind`,
`get`, `set`, `modifyGet`, `monadLift`) from Lean-elaborated monads
into our constructs. Unfolding them directly gives some nasty terms, so
we define custom "clean" unfolding lemmas under the `wpSimp` attribute.
-/
@[wpSimp] def pureE : pure = Wp.pure (σ := σ) (ρ := ρ) (m := m) := rfl
@[wpSimp] def bindE : bind = Wp.bind (σ := σ) (ρ := ρ) (ρ' := ρ') (m := m) := rfl
@[wpSimp] def getE : get = Wp.get (σ := σ) (m := m) := rfl
@[wpSimp] def setE : set = Wp.set (σ := σ) (m := m) := rfl
@[wpSimp] def modifyGetE : modifyGet = Wp.modifyGet (σ := σ) (ρ := ρ) (m := m) := rfl
@[wpSimp] def monadLiftE [IsSubStateOf σ σ'] : monadLift = Wp.lift (σ := σ) (σ' := σ') (ρ := ρ) (m := m) := rfl

/-! ### Big-Step Semantics -/

def BigStep.pure (r : ρ) : BigStep σ ρ := fun s r' s' => s' = s ∧ r' = r
def BigStep.bind (act : BigStep σ ρ) (act' : ρ -> BigStep σ ρ') : BigStep σ ρ' :=
  fun s r' s' => ∃ r s'', act s r s'' ∧ act' r s'' r' s'

def BigStep.assume (asm : Prop) : BigStep σ PUnit := fun s _ s' => asm ∧ s' = s
def BigStep.assert (ast : Prop) : BigStep σ PUnit := fun s _ s' => ast ∧ s' = s

def BigStep.fresh (τ : Type) : BigStep σ τ := fun s _r s' => s' = s

def BigStep.get : BigStep σ σ := fun s r s' => s' = s ∧ r = s
def BigStep.set (s : σ) : BigStep σ Unit := fun _s _r s' => s' = s
def BigStep.modifyGet (act : σ -> ρ × σ) : BigStep σ ρ := fun s r s' => let (ret, st) := act s; s' = st ∧ r = ret

def BigStep.spec (req : SProp σ) (ens : σ -> RProp σ ρ) : BigStep σ ρ :=
  fun s r s' => req s ∧ ens s r s'

def BigStep.lift [IsSubStateOf σ σ'] (act : BigStep σ ρ) : BigStep σ' ρ :=
  fun st r' st' => act (getFrom st) r' (getFrom st') ∧ st' = (setIn (@getFrom σ σ' _ st') st)

/-! ### Relation between `Wp`, `Wlp`, and `BigStep` -/

/-- Converting `Wp` to `Wlp` "drops" all non-terminating executions. It
is defined as follows:

  `wlp(P, φ, s) = ¬ wp(P, ¬φ, s)`

The intuition is:

1. `wp(P, φ, s)` gives you the set of "good" pre-states `S` such that
any execution from `S` terminates and reaches a state where `φ` holds;

2. `wp(P, ¬φ, s)` gives the set of "bad" pre-states, from which every
execution terminates and reaches a state where `φ` does not hold;

3. `¬ wp(P, ¬φ, s)` thus gives the set of states from which either the
execution does not terminate OR the execution terminates and reaches a
state where `φ` holds.
-/
@[actSimp]
abbrev Wp.toWlp {σ ρ : Type} {m : Mode} (wp : Wp m σ ρ) : Wlp m σ ρ :=
  -- `wlp(P, φ, s) = ¬ wp(P, ¬φ, s)`
  fun (s : σ) (post : RProp σ ρ) => ¬ wp s (fun r s' => ¬ post r s')

/-- This is an INCOMPLETE definition of the conversion from `Wp` to
`BigStep`, since it does NOT require `Wp.terminates` (see definition
below). Our soundness proof takes `Wp.terminates` as a precondition.

We nonetheless use this definition so as not to double the size of VCs
for BMC (`trace`) queries — but this means that in the current
implementation, these queries only make sense if the actions do not
`assert False` on any program path, i.e. they always succeed.

We will fix this in the near future, when we introduce execution
semantics.
-/
@[actSimp]
def Wp.toBigStep {σ} (wp : Wp m σ ρ) : BigStep σ ρ :=
  fun s r' s' =>
    wp.toWlp s (fun r₀ s₀ => r' = r₀ ∧ s' = s₀)

/-- Same as `Wp.toBigStep`, but ignores the return value. -/
@[actSimp]
def Wp.toTwoState {σ} (wp : Wp m σ ρ) : TwoState σ :=
  fun s s' =>
    wp.toWlp s (fun _ s₀ => (s' = s₀))

@[actSimp]
def BigStep.toWp {σ} (act : BigStep σ ρ) : Wp .internal σ ρ :=
  fun s post => ∀ r s', act s r s' -> post r s'

/-- Transforms any two-state formula into `Wp`. Used for casting
`transition`s into `action`s. -/
@[actSimp]
def Function.toWp (m : Mode) (r : TwoState σ) : Wp m σ Unit :=
  fun s post => ∀ s', r s s' -> post () s'

/-- This theorem lets us lift a transition in a way that does not introduce
quantification over `σ` in the lifted transition. -/
theorem lift_transition_big_step {σ σ'} [IsSubStateOf σ σ'] (m : Mode) (tr : BigStep σ ρ) :
  (@Wp.lift _  m σ σ' _ tr.toWp).toBigStep =
  fun st r' st' =>
    tr (getFrom st) r' (getFrom st') ∧
    st' = (setIn (@getFrom σ σ' _ st') st)
  := by
  unfold Wp.lift BigStep.toWp Wp.toBigStep Wp.toWlp
  funext st r' st'
  simp only [not_forall, Decidable.not_not, eq_iff_iff]
  constructor
  {
    rintro ⟨rr, rs, liftedR, heq⟩
    simp only [heq, IsSubStateOf.getFrom_setIn_idempotent, and_true]
    apply liftedR
  }
  · rintro ⟨baseR, heq⟩; exists r', (getFrom st'), baseR

/-- This theorem lets us lift a transition in a way that does not introduce
quantification over `σ` in the lifted transition. -/
theorem lift_transition {σ σ'} [IsSubStateOf σ σ'] (m : Mode) (tr : TwoState σ) :
  (@Wp.lift _  m σ σ' _ (tr.toWp m)).toTwoState =
  fun st st' =>
    tr (getFrom st) (getFrom st') ∧
    st' = (setIn (@getFrom σ σ' _ st') st)
  := by
  unfold Wp.lift Function.toWp Wp.toTwoState Wp.toWlp
  funext st st'
  simp only [not_forall, Decidable.not_not, eq_iff_iff]
  constructor
  {
    rintro ⟨rs, liftedR, heq⟩
    simp only [heq, IsSubStateOf.getFrom_setIn_idempotent, and_true]
    apply liftedR
  }
  · rintro ⟨baseR, heq⟩; exists (getFrom st'), baseR

/-! ### Soundness proof -/

abbrev refines {σ ρ} (act : Wp m σ ρ) (act' : Wp m σ ρ) : Prop :=
  ∀ s post, act s post -> act' s post

instance : LE (Wp m σ ρ) where
  le := refines

abbrev Wp.triple {σ ρ} (req : SProp σ) (act : Wp m σ ρ) (ens : RProp σ ρ) : Prop :=
  ∀ s, req s -> act s ens

/-- Always terminates without failure (i.e. without `assert False`) -/
abbrev Wp.alwaysSuccessfullyTerminates {σ } (req : SProp σ) (act : Wp m σ ρ)  : Prop :=
  ∀ s, req s -> act s (fun _ _ => True)

/- Partial correctness triple -/
abbrev TwoState.triple {σ } (req : SProp σ) (act : TwoState σ) (ens : SProp σ) : Prop :=
  ∀ s s', req s -> act s s' -> ens s'

/- Partial correctness triple -/
abbrev BigStep.triple {σ } (req : SProp σ) (act : BigStep σ ρ) (ens : RProp σ ρ) : Prop :=
  ∀ s r' s', req s -> act s r' s' -> ens r' s'


/-- `LawfulAction act` is the minimal set of conditions on `act`
that are required to prove the soundness of the `Wp.toBigStep`
conversion.

- `inter` is a generalization of the following statement:
  ```lean
    ∀ s post post', act s post -> act s post' ->
      act s fun r s => post r s ∧ post' r s
  ```

  In other words, if both `post` and `post'` overapproximate the behavior of `act`,
  then their intersection also overapproximates the behavior of `act`. `LawfulAction.inter`
  states that for the intersection of an arbitrary (possibly infinite) collection of
  predicates `post`

- `impl` states that we can always weaken the postcondition of `act` by
adding some of the possible outcomes.
-/
class LawfulAction {σ ρ : Type} (act : Wp m σ ρ) where
  inter {τ : Type} [Inhabited τ] (post : τ -> RProp σ ρ) :
    ∀ s : σ, (∀ t : τ, act s (post t)) -> act s (∀ t, post t · ·)

  impl (post post' : RProp σ ρ) : ∀ s,
    (∀ r s, post r s -> post' r s) -> act s post -> act s post'

/-- If an action satisfies two postconditions, then it satisfies their
conjunction. -/
theorem wp_and (act : Wp m σ ρ) [LawfulAction act] :
  act s post -> act s post' -> act s fun r s => post r s ∧ post' r s := by
  intro hact hact'
  let Post := fun (b : Bool) => if b then post' else post
  have post_eq : (fun r s => ∀ b, Post b r s) = fun r s => post r s ∧ post' r s := by
    unfold Post; simp
  rw [<-post_eq]; apply LawfulAction.inter ; simp [*, Post]

section TwoStateSoundness

/-- (Axiomatic) soundness of `toTwoState` conversion — if you don't have
a trivial post-condition, then anything provable after converting to
`TwoState` (two-state) semantics was provable in the `Wp` semantics. -/
theorem TwoState_sound [LawfulAction act] (req : SProp σ) (ens : SProp σ) :
  -- The post-condition is not trivial
  (¬ ∀ s, ens s) ->
  act.toTwoState.triple req ens -> act.triple req (fun _ => ens) := by
  intro ensTaut htriple s hreq
  have ens_impl : ∀ s, (∀ s' : { s' // ¬ ens s' }, ¬ (s'.val = s)) -> ens s := by
    simp; intro s impl
    false_or_by_contra
    specialize impl s; apply impl <;> simp_all
  apply LawfulAction.impl; intro _; apply ens_impl
  simp at ensTaut; rcases ensTaut with ⟨s', hens⟩
  have: Inhabited { s' // ¬ ens s' } := ⟨⟨_, hens⟩⟩
  apply LawfulAction.inter; rintro ⟨s', hens⟩
  apply LawfulAction.impl (post := fun r₀ s₀ => ¬s' = s₀) <;> (intros; try simp_all)
  false_or_by_contra
  specialize htriple _ s' ‹_› ‹_›; contradiction

/-- If something is provable in `Wp` semanticsm it is provable in
`TwoState` semantics. -/
theorem TwoState_sound' [LawfulAction act] (req : SProp σ) (ens : RProp σ ρ) :
  act.triple req ens → act.toTwoState.triple req (∃ r, ens r ·) := by
  intro htriple s s' hreq hact
  unfold Wp.triple at htriple
  specialize htriple _ hreq
  false_or_by_contra ; rename_i h ; simp at h
  apply hact ; apply LawfulAction.impl (post := ens) <;> try assumption
  intro r s hh heq ; subst_eqs ; apply h ; apply hh

theorem exists_over_PUnit (p : PUnit → Prop) : (∃ (u : PUnit), p u) = p () := by
  simp ; constructor ; intro ⟨⟨⟩, h⟩ ; assumption ; intro h ; exists PUnit.unit

theorem TwoState_sound'_ret_unit [LawfulAction act] (req : SProp σ) (ens : RProp σ PUnit) :
  act.triple req ens → act.toTwoState.triple req (ens () ·) := by
  have heq : (ens () ·) = (∃ r, ens r ·) := by ext ; rw [exists_over_PUnit]
  rw [heq] ; apply TwoState_sound'

/-- This is used by `#recover_invariants_in_tr` in `Rabia.lean`. -/
theorem TwoState_sound'_ret_unit' [LawfulAction act] {st : σ} (ens : RProp σ PUnit) :
  act st ens → (∀ st', act.toTwoState st st' → ens () st') := by
  have h := TwoState_sound'_ret_unit (act := act) (fun stt => stt = st) ens
  unfold Wp.triple TwoState.triple at h ; simp at h
  intro hq st' ; specialize h hq st st' rfl ; exact h

end TwoStateSoundness

section BigStepSoundness

attribute [-simp] not_and in
theorem big_step_sound [LawfulAction act] (req : SProp σ) (ens : RProp σ ρ) :
  (¬ ∀ r s, ens r s) ->
  act.toBigStep.triple req ens -> act.triple req ens := by
  intro ensTaut htriple s hreq
  have ens_impl : ∀ r s, (∀ rs' : { rs' : ρ × σ // ¬ ens rs'.1 rs'.2 }, ¬ (rs'.val.1 = r ∧ rs'.val.2 = s)) -> ens r s := by
    simp; intro r s impl
    false_or_by_contra
    specialize impl r s; apply impl <;> simp_all
  apply LawfulAction.impl; intro _; apply ens_impl
  simp at ensTaut; rcases ensTaut with ⟨r', s', hens⟩
  have: Inhabited { rs' : ρ × σ // ¬ ens rs'.1 rs'.2 } := ⟨⟨(r', s'), hens⟩⟩
  apply LawfulAction.inter; rintro ⟨⟨r', s'⟩, hens⟩
  apply LawfulAction.impl (post := fun r₀ s₀ => ¬(r' = r₀ ∧ s' = s₀)) <;> (intros; try simp_all)
  false_or_by_contra
  specialize htriple _ r' s' ‹_› ‹_›; contradiction

theorem big_step_sound' [LawfulAction act] (req : SProp σ) (ens : RProp σ ρ) :
  act.triple req ens → act.toBigStep.triple req ens := by
  intro htriple s r' s' hreq hact
  unfold Wp.triple at htriple
  specialize htriple _ hreq
  false_or_by_contra ; rename_i h ; simp at h
  apply hact ; apply LawfulAction.impl (post := ens) <;> try assumption
  intro r s hh ⟨heq,_⟩ ; subst_eqs ; apply h ; apply hh

theorem big_step_always_terminating_sound [LawfulAction act] (req : SProp σ) (ens : RProp σ ρ) :
  act.alwaysSuccessfullyTerminates req ->
  act.toBigStep.triple req ens -> act.triple req ens := by
  intro ensTaut htriple s hreq
  by_cases h: (¬ ∀ r s, ens r s)
  { solve_by_elim [big_step_sound] }
  apply LawfulAction.impl (post := fun _ _ => True) <;> try simp_all

theorem big_step_to_wp (act : Wp m σ ρ) [LawfulAction act] (req : SProp σ) :
  act.alwaysSuccessfullyTerminates req ->
  req s ->
  act s = act.toBigStep.toWp s := by
  intro hterm hreq; ext post; constructor
  { simp [BigStep.toWp]; intro _ _ _
    solve_by_elim [big_step_sound'] }
  simp [BigStep.toWp]
  intro h; apply big_step_always_terminating_sound (req := (s = ·)) <;> try simp
  { solve_by_elim }
  intro; simp_all

end BigStepSoundness

section LawfulActionInstances
/-! ### LawfulAction instances

These instances show that all our actions are `LawfulAction`s.
-/

instance pure_lawful : LawfulAction (Wp.pure (σ := σ) (m := m) r) where
  inter := by simp [actSimp]
  impl  := by intros; simp_all [actSimp]

instance bind_lawful (act : Wp m' σ ρ) (act' : ρ -> Wp m σ ρ') [LawfulAction act] [∀ r, LawfulAction (act' r)] : LawfulAction (Wp.bind (m := m) act act') where
  inter := by
    unfold Wp.bind
    intros τ _ post s hbind
    apply LawfulAction.impl (∀ t, act' · · <| post t) <;> solve_by_elim [LawfulAction.inter]
  impl := by
    unfold Wp.bind
    intros post post' s hpost hbind
    apply LawfulAction.impl (act' · · <| post) <;> (intros; solve_by_elim [LawfulAction.impl])

instance (priority := low) internal_sound (act : Wp m σ ρ) [inst : LawfulAction (m := .internal) act] : LawfulAction (m := .external) act where
  inter := inst.inter
  impl := inst.impl

instance assume_lawful : LawfulAction (Wp.assume (m := m) (σ := σ) rq) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]

instance assert_lawful : LawfulAction (Wp.assert (m := m) (σ := σ) rq) where
  inter := by intros; simp_all [actSimp]; rename_i h; specialize h default; simp [*]
  impl  := by intros; simp_all [actSimp]

instance require_lawful : LawfulAction (Wp.require (m := m) (σ := σ) rq) where
  inter := by
    cases m
    { intros; simp_all [actSimp]; rename_i h; specialize h default; simp [*] }
    intros; simp_all [actSimp]
  impl := by cases m <;> (intros; simp_all [actSimp])

instance fresh_lawful : LawfulAction (Wp.fresh (m := m) (σ := σ) τ) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]

instance spec_lawful : LawfulAction (Wp.spec (m := m) req ens) where
  inter := by
    cases m <;> (intros; simp_all [actSimp])
    rename_i h; intros; specialize h default; simp [*]
  impl := by
    cases m <;> (simp [actSimp]; intros)
    { constructor <;> (intros; solve_by_elim) }
    solve_by_elim

instance (r : σ -> σ -> Prop) : LawfulAction (r.toWp (m := m)) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]

instance get_lawful : LawfulAction (Wp.get (m := m) (σ := σ)) where
  inter := by intros; simp_all [Wp.get]
  impl := by intros; simp_all [Wp.get]

instance set_lawful (s : σ) : LawfulAction (Wp.set s (m := m)) where
  inter := by intros; simp_all [Wp.set]
  impl := by intros; simp_all [Wp.set]

instance modifyGet_lawful : LawfulAction (Wp.modifyGet f (m := m) (σ := σ) (ρ := ρ)) where
  inter := by intros; simp_all [Wp.modifyGet]
  impl := by intros; simp_all [Wp.modifyGet]

instance if_lawful [Decidable c] [instT: LawfulAction t] [instS : LawfulAction e] : LawfulAction (ite c t e) where
  inter := by
    intros; by_cases c <;> simp_all <;> solve_by_elim [instT.inter, instS.inter]
  impl := by
    intros; by_cases c <;> simp_all <;> solve_by_elim [instT.impl, instS.impl]

instance lift_lawful (act : Wp m σ ρ) [IsSubStateOf σ σ'] [LawfulAction act] :
  LawfulAction (act.lift (σ' := σ')) where
  inter := by
    intros; simp_all [Wp.lift]
    solve_by_elim [LawfulAction.inter]
  impl := by
    intros; simp_all [Wp.lift]
    solve_by_elim [LawfulAction.impl]

theorem check_spec_lawful [LawfulAction act] (req : SProp σ) (ens : σ -> RProp σ ρ) :
  (∀ s, req s -> act s (ens s)) ->
  Wp.spec (m := .internal) req ens <= act := by
  intro triple s post; simp [actSimp]; intros hreq hens
  solve_by_elim [LawfulAction.impl]

end LawfulActionInstances

section GenBigStepInstances
/-! ### GenBigStep instances

These instances show that we can soundly translate `LawfulAction`s that
always successfully terminate (under some precondition `pre`, which is
taken to be either `True` or the inductive invariant) into `BigStep`
semantics.
-/
class GenBigStep (σ ρ : Type) (wp : Wp .external σ ρ) (tr : outParam (BigStep σ ρ)) where
  lawful : LawfulAction wp
  equiv pre  :
    wp.alwaysSuccessfullyTerminates pre -> ∀ s, pre s -> tr s = wp.toBigStep s

instance : GenBigStep σ ρ (Wp.pure r) (BigStep.pure r) where
  lawful := inferInstance
  equiv := by
    unfold Wp.toBigStep BigStep.pure Wp.toWlp Wp.pure; simp; intros
    ext; constructor <;> simp <;> intros <;> simp_all

instance : GenBigStep σ PUnit (Wp.assume asm) (BigStep.assume asm) where
  lawful := inferInstance
  equiv := by
    unfold Wp.toBigStep BigStep.assume Wp.toWlp Wp.assume; simp

instance : GenBigStep σ PUnit (Wp.assert asm) (BigStep.assert asm) where
  lawful := inferInstance
  equiv := by
    unfold Wp.toBigStep BigStep.assert Wp.toWlp Wp.assert; simp
    rintro pre preAsm s hpre; ext
    have h := preAsm s hpre; simp_all

instance : GenBigStep σ PUnit (Wp.require rq) (BigStep.assume rq) where
  lawful := inferInstance
  equiv := by
    unfold Wp.toBigStep BigStep.assume Wp.toWlp Wp.require Wp.assume; simp

instance : GenBigStep σ τ (Wp.fresh τ) (BigStep.fresh τ) where
  lawful := inferInstance
  equiv := by
    unfold Wp.toBigStep BigStep.fresh Wp.toWlp Wp.fresh; simp

instance : GenBigStep σ Unit (Wp.set s) (BigStep.set s) where
  lawful := inferInstance
  equiv := by
    unfold Wp.toBigStep BigStep.set Wp.toWlp Wp.set; simp

instance : GenBigStep σ σ (Wp.get) (BigStep.get) where
  lawful := inferInstance
  equiv := by
    unfold Wp.toBigStep BigStep.get Wp.toWlp Wp.get; simp
    intros; ext; constructor<;> intros <;> simp_all

instance : GenBigStep σ ρ (Wp.modifyGet act) (BigStep.modifyGet act) where
  lawful := inferInstance
  equiv := by
    unfold Wp.toBigStep BigStep.modifyGet Wp.toWlp Wp.modifyGet; simp
    intros; ext; constructor<;> intros <;> simp_all

instance : GenBigStep σ ρ (Wp.spec req ens) (BigStep.spec req ens) where
  lawful := inferInstance
  equiv := by unfold Wp.toBigStep BigStep.spec Wp.toWlp Wp.spec; simp

instance [inst : GenBigStep σ ρ act actTr] : LawfulAction act := inst.lawful

/-- A specialized version of `lift_transition_big_step`, applied to
`LawfulAction`s. -/
theorem lift_transition_big_step' {σ σ'} [IsSubStateOf σ σ'] (m : Mode) (r : Wp m σ ρ) [LawfulAction r] (st : σ') :
  r.alwaysSuccessfullyTerminates (· = getFrom st) →
  (@Wp.lift _  m σ σ' _ r).toBigStep st =
  fun r' st' =>
    r.toBigStep (getFrom st) r' (getFrom st') ∧
    st' = (setIn (@getFrom σ σ' _ st') st) := by
  intro term
  have rEq : r.lift.toBigStep st = (r.toBigStep.toWp.lift.toBigStep st) := by {
    unfold Wp.lift Wp.toBigStep Wp.toWlp; ext; simp
    rw [big_step_to_wp (act := r) (req := (fun x => x = getFrom st))] <;> try simp [*]
    unfold Wp.toBigStep Wp.toWlp; simp }
  rw [rEq, lift_transition_big_step]

instance {σ σ'} [IsSubStateOf σ σ'] (act : Wp .external σ ρ) (actTr : BigStep σ ρ) [inst:GenBigStep σ ρ act actTr]
  : GenBigStep σ' ρ (Wp.lift (σ' := σ') act) (BigStep.lift (σ := σ) actTr) where
  lawful := inferInstance
  equiv pre := by
    intro term s hpre; ext; dsimp;
    have : Wp.alwaysSuccessfullyTerminates (· = getFrom s) act := by simp; solve_by_elim
    unfold BigStep.lift
    rw [inst.equiv (pre := (getFrom s = ·))] <;> try simp [*]
    rwa [lift_transition_big_step']


theorem bind_terminates m (act : Wp m σ ρ) (act' : ρ -> Wp m σ ρ') s [LawfulAction act] :
  pre s ->
  act.alwaysSuccessfullyTerminates pre →
  (act.bind act').alwaysSuccessfullyTerminates pre ->
  act.toBigStep s r' s' ->
  (act' r').alwaysSuccessfullyTerminates (· = s') := by
    unfold Wp.alwaysSuccessfullyTerminates Wp.toBigStep Wp.toWlp Wp.bind
    intros hpre actT act'T
    have actT := actT s hpre
    have act'T := act'T s hpre
    have act''T := big_step_sound' (act := act) (req := (· = s))
    unfold Wp.triple BigStep.triple Wp.toBigStep Wp.toWlp at act''T
    simp at act''T; specialize act''T _ act'T s r' s' rfl
    simp_all

attribute [-simp] not_and in
instance (act : Wp .external σ ρ) (act' : ρ -> Wp .external σ ρ')
  [inst: GenBigStep σ ρ act actTr] [inst' : ∀ r, GenBigStep σ ρ' (act' r) (actTr' r)] :
  GenBigStep σ ρ' (act.bind act') (actTr.bind actTr') where
  lawful := inferInstance
  equiv pre := by
      unfold Wp.bind; --simp
      intros term s hpre
      have := @inst.lawful
      have actTerm : act |>.alwaysSuccessfullyTerminates pre := by
        intro s' hpre'
        apply LawfulAction.impl _ _ _ _ (term _ hpre'); simp
      unfold BigStep.bind Wp.toBigStep Wp.toWlp; simp; ext r' s'
      rw [inst.equiv _ actTerm s hpre]
      unfold Wp.toBigStep Wp.toWlp; simp; constructor
      { simp; intros ret st htr htr' hwp
        apply htr; apply LawfulAction.impl <;> try assumption
        rintro s r _ ⟨⟩; subst_eqs
        rw [(inst' ret).equiv (pre := (· = st))] at htr' <;> try simp
        { solve_by_elim }
        have := @(inst' ret).lawful
        apply LawfulAction.impl <;> try assumption
        simp }
      intro hact; false_or_by_contra
      rename_i hact'; simp [not_and_iff_not_or_not] at hact'
      by_cases hex : ∀ ret st, act s (¬ret = · ∨ ¬st = ·)
      { apply hact
        apply LawfulAction.impl (post := fun r s => ∀ (ret : ρ) (st : σ), ret ≠ r ∨ st ≠ s)
        { rintro r s hf; specialize hf r s; simp at hf }
        by_cases nr : Nonempty ρ
        { have := inhabited_of_nonempty nr; have ns := Inhabited.mk s
          solve_by_elim [LawfulAction.inter] }
        apply LawfulAction.impl (post := fun _ _ => True) <;> simp [*]
        intro r; have : Nonempty ρ := by constructor; assumption
        contradiction }
      simp at hex; rcases hex with ⟨ret, st, hret⟩
      rcases hact' ret st with (hret' | hst) <;> try contradiction
      apply hact
      by_cases ∀ r s'_1, act' r s'_1 fun r s'_2 => ¬(r' = r ∧ s' = s'_2)
      { apply LawfulAction.impl <;> try solve_by_elim }
      apply big_step_sound (req := (· = s)) <;> try simp_all [BigStep.triple]
      rintro s'' ret' st' rfl
      unfold  Wp.toBigStep Wp.toWlp; simp [not_and_iff_not_or_not]; intro _
      rcases hact' ret' st' with (h | h) <;> try solve_by_elim
      rw [(inst' ret').equiv (pre := (· = st'))] at h <;> try simp
      { unfold Wp.toBigStep Wp.toWlp at h; simp_all [not_and_iff_not_or_not] }
      have := (inst' ret').lawful
      apply bind_terminates (act := act) (act' := fun ret => act' ret) (pre := pre) <;> try solve_by_elim
      unfold Wp.toBigStep Wp.toWlp; simp [not_and_iff_not_or_not, *]

end GenBigStepInstances

end Theory
