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
`require`s are satisfied. That is, under this interpretation, `require P`
is equivalent to `assert P`.

- `external`: when we call an action, it's the environment's responsibility
  to ensure `require`s are satisfied. We treat `require`s as `assume`s under
  this interpretation. Only top-level actions should be interpreted as
  `external`. -/
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
@[inline] abbrev ActProp := σ -> σ -> Prop



/-!
In Veil we will be using three different semantics:

- [Wp]: a weakest-precondition transformer expressed in [Omni
semantics](https://doi.org/10.1145/3579834) style; this relates a state
`s : σ` to set of the possible program outcomes `post : RProp σ`

- [Wlp]: liberal weakest-precondition semantics, which is similar to
`Wp`, but does not require termination of the program

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

/-! ### Languge statements -/

@[actSimp]
def Wp.pure (r : ρ) : Wp m σ ρ := fun s post => post r s
@[actSimp]
def Wp.bind (wp : Wp m σ ρ) (wp_cont : ρ -> Wp m σ ρ') : Wp m σ ρ' :=
  fun s post => wp s (fun r s' => wp_cont r s' post)

@[actSimp]
def Wp.assume (asm : Prop) : Wp m σ PUnit := fun s post => asm → post () s
@[actSimp]
def Wp.assert (ast : Prop) : Wp m σ PUnit := fun s post => ast ∧ post () s
@[actSimp]
def Wp.fresh (τ : Type) : Wp m σ τ := fun s post => ∀ t, post t s

@[actSimp]
def Wp.require (rq : Prop) : Wp m σ PUnit :=
  match m with
  | Mode.internal => Wp.assert rq
  | Mode.external => Wp.assume rq

/-- `Wp.spec req ens` is the weakest precondition for a function with
  precondition `req` and postcondition `ens`.
-/
@[actSimp]
def Wp.spec (req : SProp σ) (ens : σ -> RProp σ ρ) : Wp m σ ρ :=
  fun s post =>
    match m with
    | .internal => req s ∧ ∀ r' s', (ens s r' s' -> post r' s')
    | .external => ∀ r' s', req s -> ens s r' s' -> post r' s'

def BigStep.spec (req : SProp σ) (ens : σ -> RProp σ ρ) : BigStep σ ρ :=
  fun s r s' => req s ∧ (req s -> ens s r s')

@[actSimp]
def Wp.get : Wp m σ σ := fun s post => post s s
@[actSimp]
def Wp.set (s' : σ) : Wp m σ Unit := fun _ post => post () s'
@[actSimp]
def Wp.modifyGet (act : σ -> ρ × σ) : Wp m σ ρ := fun s post => let (ret, s') := act s ; post ret s'


-- def BigStep.choice : BigStep σ ρ -> BigStep σ ρ -> BigStep σ ρ :=
--   fun act act' s r s' => act s r s' ∨ act' s r s'

/- BAD: it duplicates post -/
-- def Wp.choice : Wp σ ρ -> Wp σ ρ -> Wp σ ρ :=
--   fun wp wp' s post => wp s post ∨ wp' s post

-- def Wp.choice (wp : Wp σ ρ) (wp' : Wp σ ρ) : Wp σ ρ :=
--   wp.toBigStep.choice wp'.toBigStep |>.toWp


/-! ### Relation between `Wp`, `Wlp`, and `BigStep`

[Comparing Weakest Precondition and Weakest Liberal Precondition](https://arxiv.org/abs/1512.04013)
gives an overview of the relation between `Wp` and `Wlp` (summarized below).

Assuming transition semantics $\text{tr}$ of changes to the program
variables induced by the different program constructs, we have the
following definitions of $\text{wp}$ and $\text{wlp}$ ($P$ is the
program, $s$ is the initial state, $\varphi$ is the postcondition):

$\text{wp}(P, \varphi, s) \coloneqq \exists s',  \text{tr}(s, s') \land \varphi(s')$

$\text{wlp}(P, \varphi, s) \coloneqq ∀ s',  \text{tr}(s, s') \rightarrow \varphi(s')$

$\text{wp}$ says "starting in state $x$, program $P$ terminates and
reaches state $x'$, and $\varphi(x')$ holds" $\text{wlp}$ says
"starting in state $x$, **if** program P terminates in some state $x'$,
then $\varphi(x')$ holds"

Given these definitions, the following holds: $\text{wlp}(P, \varphi,
s) = \lnot \text{wp}(P, \lnot \varphi, s)$

Note also that $\text{wp}(P, \top, s) = \exists s', \text{tr}(s, s')$,
i.e. this says "P terminates when starting on $s$"

----

Whereas in the paper above, the base semantics is `Tr` (the transition
meaning of program constructs), in Veil, as we explain in the tool
paper, we choose to use `Wp` as our base semantics. This let us avoid
existentially quantifying over the post-state `s'` when defining `Wp`
in terms of `Tr`.

Therefore, we define `Wlp` and `BigStep` (`Tr`) in terms of `Wp`, as
follows.
-/

/-- Converting `Wp` to `Wlp` "drops" all non-terminating executions. -/
@[actSimp]
abbrev Wp.toWlp {σ ρ : Type} (m : Mode) (wp : Wp m σ ρ) : Wlp m σ ρ :=
  -- `wlp(P, φ, s) = ¬ wp(P, ¬φ, s)`
  fun (s : σ) (post : RProp σ ρ) => ¬ wp s (fun r s' => ¬ post r s')

/-- Starting in state `s`, `wp` has a terminating execution. -/
abbrev Wp.hasTerminatingExecFromState {σ} (wp : Wp m σ ρ) (s : σ) : Prop :=
  wp s (fun _ _ => True)

/-- State `s` leads to post-state `s'` and return value `r'` under `wp`
if `wp` has a terminating execution starting from `s`, and all
executions starting from `s` end in `s'` with return value `r'`. -/
@[actSimp]
def Wp.toBigStep {σ} (wp : Wp m σ ρ) : BigStep σ ρ :=
  fun s r' s' =>
    wp.hasTerminatingExecFromState s ∧
    wp.toWlp m s (fun r₀ s₀ => r' = r₀ ∧ s' = s₀)

/-- States `s` and `s'` are related by `wp` if `wp` has a terminating
execution starting from `s`, and all executions starting from `s` end
in `s'`. -/
@[actSimp]
def Wp.toActProp {σ} (wp : Wp m σ ρ) : ActProp σ :=
  -- `tr(s, s') = wp(P, ⊤, s) ∧ wlp(P, φ, s)`
  fun s s' =>
    wp.hasTerminatingExecFromState s ∧
    wp.toWlp m s (fun _ s₀ => (s' = s₀))

/-- [BigStep.toWp] converts Big-step semantics to Omni one.

  Ideally, here we should also assert termination of `act`, but this will be handled
  via `Sound` condition later. -/
@[actSimp]
def BigStep.toWp {σ} (act : BigStep σ ρ) : Wp .internal σ ρ :=
  fun s post => ∀ r s', act s r s' -> post r s'


/-- Function which transforms any two-state formula into `Wp` -/
@[actSimp]
def Function.toWp (m : Mode) (r : σ -> σ -> Prop) : Wp m σ Unit :=
  fun s post => ∀ s', r s s' -> post () s'

/-! ### Monad Instances -/

instance : Monad (Wp m σ) where
  pure := Wp.pure
  bind := Wp.bind

instance : MonadStateOf σ (Wp m σ) where
  get := Wp.get
  set := Wp.set
  modifyGet := Wp.modifyGet

@[wpSimp]
def pureE : pure = Wp.pure (σ := σ) (ρ := ρ) (m := m) := rfl
@[wpSimp]
def bindE : bind = Wp.bind (σ := σ) (ρ := ρ) (ρ' := ρ') (m := m) := rfl
@[wpSimp]
def getE : get = Wp.get (σ := σ) (m := m) := rfl
@[wpSimp]
def modifyGetE : modifyGet = Wp.modifyGet (σ := σ) (ρ := ρ) (m := m) := rfl

/-- `σ` is a sub-state of `σ'` -/
class IsSubStateOf (σ : semiOutParam Type) (σ' : Type) where
  /-- Set the small state `σ` in the big one `σ'`, returning the new `σ'` -/
  setIn : σ -> σ' -> σ'
  /-- Get the small state `σ` from the big one `σ'` -/
  getFrom : σ' -> σ

  setIn_getFrom_idempotent : ∀ σ', setIn (getFrom σ') σ' = σ'
  getFrom_setIn_idempotent : ∀ σ σ', getFrom (setIn σ σ') = σ

export IsSubStateOf (setIn getFrom)

@[actSimp]
def Wp.lift {σ σ'} [IsSubStateOf σ σ'] (act : Wp m σ ρ) : Wp m σ' ρ :=
  fun s' post => act (getFrom s') (fun r s => post r (setIn s s'))

instance [IsSubStateOf σ σ'] : MonadLift (Wp m σ) (Wp m σ') where
  monadLift := Wp.lift

@[wpSimp]
def monadLiftE [IsSubStateOf σ σ'] : monadLift = Wp.lift (σ := σ) (σ' := σ') (ρ := ρ) (m := m) := rfl

/-! ### Lifting transitions -/

/-- This theorem lets us lift a transition in a way that does not introduce
quantification over `σ` in the lifted transition. -/
theorem lift_transition {σ σ'} [IsSubStateOf σ σ'] (m : Mode) (r : σ -> σ -> Prop) :
  (@Wp.lift _  m σ σ' _ (r.toWp m)).toActProp =
  fun st st' =>
    r (getFrom st) (getFrom st') ∧
    st' = (setIn (@getFrom σ σ' _ st') st)
  := by
  unfold Wp.lift Function.toWp Wp.toActProp Wp.toWlp Wp.hasTerminatingExecFromState
  funext st st'
  simp only [implies_true, not_forall, not_imp, Decidable.not_not, true_and, eq_iff_iff]
  constructor
  {
    rintro ⟨rs, liftedR, heq⟩
    simp only [heq, IsSubStateOf.setIn_getFrom_idempotent, IsSubStateOf.getFrom_setIn_idempotent, and_true]
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

/- Termination -/
abbrev Wp.terminates {σ } (req : SProp σ) (act : Wp m σ ρ)  : Prop :=
  ∀ s, req s -> act s (fun _ _ => True)


/- partial correctness triple -/
abbrev ActProp.triple {σ } (req : SProp σ) (act : ActProp σ) (ens : SProp σ) : Prop :=
  ∀ s s', req s -> act s s' -> ens s'



/-- `Sound act` states the set of minimal conditions on `act` that are required
  to prove the soundness of the `Wp.toBigStep` conversion.
  - first condition `inter` is a generalization of the following statement:
    ```lean
      ∀ s post post', act s post -> act s post' ->
        act s fun r s => post r s ∧ post' r s
    ```
    In other words, if both `post` and `post'` overapproximate the behavior of `act`,
    then their intersection also overapproximates the behavior of `act`. `Sound.inter`
    states that for the intersection of an arbitrary (possibly infinite) collection of
    predicates `post`
  - second condition `impl`, states that we can always weaken the postcondition of `act`
    by adding some of the possible outcomes.
  - third condition `call`, states that the `internal` mode of `act` refines the `external`
    one. In other words, if you have proven some striple for `internal` mode of `act`,
    the same one holds for its `external` version -/
class Sound {σ ρ : Type} (act : Wp m σ ρ) where
  inter {τ : Type} [Inhabited τ] (post : τ -> RProp σ ρ) :
    ∀ s : σ, (∀ t : τ, act s (post t)) -> act s (∀ t, post t · ·)
  impl (post post' : RProp σ ρ) : ∀ s,
    (∀ r s, post r s -> post' r s) -> act s post -> act s post'
  -- call : act .internal <= act .external

theorem sound_and (act : Wp m σ ρ) [Sound act] :
  act s post -> act s post' -> act s fun r s => post r s ∧ post' r s := by
  intro hact hact'
  let Post := fun (b : Bool) => if b then post' else post
  have post_eq : (fun r s => ∀ b, Post b r s) = fun r s => post r s ∧ post' r s := by
    unfold Post; simp
  rw [<-post_eq]; apply Sound.inter <;> simp [*, Post]

-- theorem sound_terminates [Sound act] : (∀ r s, post r s) -> act m s post := by
--   intro hpost
--   have post_eq : post = (fun _ _ => Empty -> True) := by ext; simp_all
--   rw [post_eq]; apply Sound.inter; rintro ⟨⟩

-- theorem wp_sound (act : ∀ m, Wp m σ ρ) [Sound act] :
--   ∀ s post, (act m).toBigStep.toWp (m := m) s post <-> act m s post := by
--   intro s post; constructor
--   { unfold Wp.toBigStep BigStep.toWp; simp
--     intro hact
--     have post_impl : ∀ r s, (∀ r' s', ¬ post r' s' -> ¬ (r' = r ∧ s' = s)) -> post r s := by
--       intro r s impl
--       false_or_by_contra
--       specialize impl r s; apply impl <;> simp_all
--     apply Sound.impl; apply post_impl
--     apply Sound.inter; intro r'
--     apply Sound.inter; intro s'
--     by_cases postrs : post r' s'
--     { apply sound_terminates; simp_all }
--     apply Sound.impl (post := fun r₀ s₀ => r' = r₀ → ¬s' = s₀) <;> simp_all
--     false_or_by_contra
--     specialize hact _ _ ‹_›; contradiction }
--   intro hact r' s' h
--   false_or_by_contra; apply h; apply Sound.impl (post := post)
--   { intros; intro _; simp_all }
--   assumption

theorem triple_sound [Sound act] (req : SProp σ) (ens : SProp σ) :
  (¬ ∀ s, ens s) ->
  act.terminates req →
  act.toActProp.triple req ens -> act.triple req (fun _ => ens) := by
  intro ensTaut term htriple s hreq
  have ens_impl : ∀ s, (∀ s' : { s' // ¬ ens s' }, ¬ (s'.val = s)) -> ens s := by
    simp; intro s impl
    false_or_by_contra
    specialize impl s; apply impl <;> simp_all
  apply Sound.impl; intro _; apply ens_impl
  simp at ensTaut; rcases ensTaut with ⟨s', hens⟩
  have: Inhabited { s' // ¬ ens s' } := ⟨⟨_, hens⟩⟩
  apply Sound.inter; rintro ⟨s', hens⟩
  apply Sound.impl (post := fun r₀ s₀ => ¬s' = s₀) <;> (intros; try simp_all)
  false_or_by_contra
  specialize htriple _ s' ‹_› ⟨term _ ‹_›,‹_›⟩; contradiction

theorem triple_sound' [Sound act] (req : SProp σ) (ens : RProp σ ρ) :
  act.triple req ens → act.toActProp.triple req (∃ r, ens r ·) := by
  intro htriple s s' hreq ⟨_, hact⟩
  unfold Wp.triple at htriple
  specialize htriple _ hreq
  false_or_by_contra ; rename_i h ; simp at h
  apply hact ; apply Sound.impl (post := ens) <;> try assumption
  intro r s hh heq ; subst_eqs ; apply h ; apply hh

theorem exists_over_PUnit (p : PUnit → Prop) : (∃ (u : PUnit), p u) = p () := by
  simp ; constructor ; intro ⟨⟨⟩, h⟩ ; assumption ; intro h ; exists PUnit.unit

theorem triple_sound'_ret_unit [Sound act] (req : SProp σ) (ens : RProp σ PUnit) :
  act.triple req ens → act.toActProp.triple req (ens () ·) := by
  have heq : (ens () ·) = (∃ r, ens r ·) := by ext ; rw [exists_over_PUnit]
  rw [heq] ; apply triple_sound'

theorem triple_sound'_ret_unit' [Sound act] {st : σ} (ens : RProp σ PUnit) :
  act st ens → (∀ st', act.toActProp st st' → ens () st') := by
  have h := triple_sound'_ret_unit (act := act) (fun stt => stt = st) ens
  unfold Wp.triple ActProp.triple at h ; simp at h
  intro hq st' ; specialize h hq st st' rfl ; exact h

instance pure_sound : Sound (Wp.pure (σ := σ) (m := m) r) where
  inter := by simp [pure, actSimp]
  impl  := by intros; simp_all [pure, actSimp]
  -- call  := by solve_by_elim

instance bind_sound (act : Wp m' σ ρ) (act' : ρ -> Wp m σ ρ') [Sound act] [∀ r, Sound (act' r)] : Sound (Wp.bind (m := m) act act') where
  inter := by
    unfold Wp.bind
    intros τ _ post s hbind
    apply Sound.impl (∀ t, act' · · <| post t) <;> solve_by_elim [Sound.inter]
  impl := by
    unfold Wp.bind
    intros post post' s hpost hbind
    apply Sound.impl (act' · · <| post) <;> (intros; solve_by_elim [Sound.impl])

instance (priority := low) internal_sound (act : Wp m σ ρ) [inst : Sound (m := .internal) act] : Sound (m := .external) act where
  inter := inst.inter
  impl := inst.impl

  -- call := by
  --   unfold Wp.bind
  --   intros s post hbind
  --   apply Sound.call; apply Sound.impl;
  --   { intros _ _; apply Sound.call }
  --   solve_by_elim

instance assume_sound : Sound (Wp.assume (m := m) (σ := σ) rq) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]
  -- call := by solve_by_elim

instance assert_sound : Sound (Wp.assert (m := m) (σ := σ) rq) where
  inter := by intros; simp_all [actSimp]; rename_i h; specialize h default; simp [*]
  impl  := by intros; simp_all [actSimp] <;> solve_by_elim
  -- call  := by solve_by_elim

instance require_sound : Sound (Wp.require (m := m) (σ := σ) rq) where
  inter := by
    cases m
    { intros; simp_all [actSimp]; rename_i h; specialize h default; simp [*] }
    intros; simp_all [actSimp]
  impl := by cases m <;> (intros; simp_all [actSimp] <;> solve_by_elim)
  -- call := by
  --  intros s post; unfold Wp.require; simp [Wp.assert, Wp.assume]; solve_by_elim


instance fresh_sound : Sound (Wp.fresh (m := m) (σ := σ) τ) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]
  -- call := by solve_by_elim


instance spec_sound : Sound (Wp.spec (m := m) req ens) where
  inter := by
    cases m <;> (intros; simp_all [actSimp])
    rename_i h; intros; specialize h default; simp [*]
  impl := by
    cases m <;> (simp [actSimp]; intros)
    { constructor <;> (intros; solve_by_elim) }
    solve_by_elim
  -- call := by intros _; simp_all [actSimp]

instance (r : σ -> σ -> Prop) : Sound (r.toWp (m := m)) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]
  -- call := by solve_by_elim

instance get_sound : Sound (Wp.get (m := m) (σ := σ)) where
  inter := by intros; simp_all [get, getThe,MonadStateOf.get, Wp.get]
  impl := by intros; simp_all [get, getThe,MonadStateOf.get,Wp.get]
  -- call := by solve_by_elim

instance set_sound (s : σ) : Sound (Wp.set s (m := m)) where
  inter := by intros; simp_all [Wp.set]
  impl := by intros; simp_all [Wp.set]
  -- call := by solve_by_elim

instance modifyGet_sound : Sound (Wp.modifyGet f (m := m) (σ := σ) (ρ := ρ)) where
  inter := by intros; simp_all [Wp.modifyGet]
  impl := by intros; simp_all [Wp.modifyGet]
  -- call := by solve_by_elim

instance if_sound [Decidable c] [instT: Sound t] [instS : Sound e] : Sound (ite c t e) where
  inter := by
    intros; by_cases c <;> simp_all <;> solve_by_elim [instT.inter, instS.inter]
  impl := by
    intros; by_cases c <;> simp_all <;> solve_by_elim [instT.impl, instS.impl]

instance (act : Wp m σ ρ) [IsSubStateOf σ σ'] [Sound act] :
  Sound (act.lift (σ' := σ')) where
  inter := by
    intros; simp_all [Wp.lift]
    solve_by_elim [Sound.inter]
  impl := by
    intros; simp_all [Wp.lift]
    solve_by_elim [Sound.impl]
  -- call := by
  --   intros; simp_all [monadLift, MonadLift.monadLift]
  --   solve_by_elim [Sound.call]

/-! ### Correctness of `checkSpec` -/

theorem wp_spec_to_big_step :
  (Wp.spec ens req).toBigStep (m := .internal) = BigStep.spec ens req := by
  ext s r' s'; unfold Wp.spec BigStep.spec Wp.toBigStep Wp.toWlp Wp.hasTerminatingExecFromState; simp

theorem check_spec_sound [Sound act] (req : SProp σ) (ens : σ -> RProp σ ρ) :
  (∀ s, req s -> act s (ens s)) ->
  Wp.spec (m := .internal) req ens <= act := by
  intro triple s post; simp [actSimp]; intros hreq hens
  solve_by_elim [Sound.impl]

end Theory
