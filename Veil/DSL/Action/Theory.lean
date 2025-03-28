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
  fun s r s' => req s ∧ ens s r s'

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
abbrev Wp.toWlp {σ ρ : Type} {m : Mode} (wp : Wp m σ ρ) : Wlp m σ ρ :=
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
    wp.toWlp s (fun r₀ s₀ => r' = r₀ ∧ s' = s₀)

/-- States `s` and `s'` are related by `wp` if `wp` has a terminating
execution starting from `s`, and all executions starting from `s` end
in `s'`. -/
@[actSimp]
def Wp.toActProp {σ} (wp : Wp m σ ρ) : ActProp σ :=
  -- `tr(s, s') = wp(P, ⊤, s) ∧ wlp(P, φ, s)`
  fun s s' =>
    wp.toWlp s (fun _ s₀ => (s' = s₀))

/-- [BigStep.toWp] converts Big-step semantics to Omni one.

  Ideally, here we should also assert termination of `act`, but this will be handled
  via `LawfulAction` condition later. -/
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
  unfold Wp.lift Function.toWp Wp.toActProp Wp.toWlp --Wp.hasTerminatingExecFromState
  funext st st'
  simp only [implies_true, not_forall, not_imp, Decidable.not_not, true_and, eq_iff_iff]
  constructor
  {
    rintro ⟨rs, liftedR, heq⟩
    simp only [heq, IsSubStateOf.setIn_getFrom_idempotent, IsSubStateOf.getFrom_setIn_idempotent, and_true]
    apply liftedR
  }
  · rintro ⟨baseR, heq⟩; exists (getFrom st'), baseR

/-- This theorem lets us lift a transition in a way that does not introduce
quantification over `σ` in the lifted transition. -/
theorem lift_transition_big_step {σ σ'} [IsSubStateOf σ σ'] (m : Mode) (r : BigStep σ ρ) :
  (@Wp.lift _  m σ σ' _ r.toWp).toBigStep =
  fun st r' st' =>
    r (getFrom st) r' (getFrom st') ∧
    st' = (setIn (@getFrom σ σ' _ st') st)
  := by
  unfold Wp.lift BigStep.toWp Wp.toBigStep Wp.toWlp --Wp.hasTerminatingExecFromState
  funext st r' st'
  simp only [implies_true, not_forall, not_imp, Decidable.not_not, true_and, eq_iff_iff]
  constructor
  {
    rintro ⟨rr, rs, liftedR, heq⟩
    simp only [heq, IsSubStateOf.setIn_getFrom_idempotent, IsSubStateOf.getFrom_setIn_idempotent, and_true]
    apply liftedR
  }
  · rintro ⟨baseR, heq⟩; exists r', (getFrom st'), baseR

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

/- partial correctness triple -/
abbrev BigStep.triple {σ } (req : SProp σ) (act : BigStep σ ρ) (ens : RProp σ ρ) : Prop :=
  ∀ s r' s', req s -> act s r' s' -> ens r' s'



/-- `LawfulAction act` states the set of minimal conditions on `act` that are required
  to prove the soundness of the `Wp.toBigStep` conversion.
  - first condition `inter` is a generalization of the following statement:
    ```lean
      ∀ s post post', act s post -> act s post' ->
        act s fun r s => post r s ∧ post' r s
    ```
    In other words, if both `post` and `post'` overapproximate the behavior of `act`,
    then their intersection also overapproximates the behavior of `act`. `LawfulAction.inter`
    states that for the intersection of an arbitrary (possibly infinite) collection of
    predicates `post`
  - second condition `impl`, states that we can always weaken the postcondition of `act`
    by adding some of the possible outcomes.
  - third condition `call`, states that the `internal` mode of `act` refines the `external`
    one. In other words, if you have proven some striple for `internal` mode of `act`,
    the same one holds for its `external` version -/
class LawfulAction {σ ρ : Type} (act : Wp m σ ρ) where
  inter {τ : Type} [Inhabited τ] (post : τ -> RProp σ ρ) :
    ∀ s : σ, (∀ t : τ, act s (post t)) -> act s (∀ t, post t · ·)
  impl (post post' : RProp σ ρ) : ∀ s,
    (∀ r s, post r s -> post' r s) -> act s post -> act s post'
  -- call : act .internal <= act .external

theorem sound_and (act : Wp m σ ρ) [LawfulAction act] :
  act s post -> act s post' -> act s fun r s => post r s ∧ post' r s := by
  intro hact hact'
  let Post := fun (b : Bool) => if b then post' else post
  have post_eq : (fun r s => ∀ b, Post b r s) = fun r s => post r s ∧ post' r s := by
    unfold Post; simp
  rw [<-post_eq]; apply LawfulAction.inter <;> simp [*, Post]

theorem triple_sound [LawfulAction act] (req : SProp σ) (ens : SProp σ) :
  (¬ ∀ s, ens s) ->
  act.toActProp.triple req ens -> act.triple req (fun _ => ens) := by
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

attribute [-simp] not_and in
theorem triple_sound_big_step [LawfulAction act] (req : SProp σ) (ens : RProp σ ρ) :
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

theorem triple_sound_terminate [LawfulAction act] (req : SProp σ) (ens : RProp σ ρ) :
  act.terminates req ->
  act.toBigStep.triple req ens -> act.triple req ens := by
  intro ensTaut htriple s hreq
  by_cases h: (¬ ∀ r s, ens r s)
  { solve_by_elim [triple_sound_big_step] }
  apply LawfulAction.impl (post := fun _ _ => True) <;> try simp_all

theorem triple_sound' [LawfulAction act] (req : SProp σ) (ens : RProp σ ρ) :
  act.triple req ens → act.toActProp.triple req (∃ r, ens r ·) := by
  intro htriple s s' hreq hact
  unfold Wp.triple at htriple
  specialize htriple _ hreq
  false_or_by_contra ; rename_i h ; simp at h
  apply hact ; apply LawfulAction.impl (post := ens) <;> try assumption
  intro r s hh heq ; subst_eqs ; apply h ; apply hh

theorem triple_sound_big_step' [LawfulAction act] (req : SProp σ) (ens : RProp σ ρ) :
  act.triple req ens → act.toBigStep.triple req ens := by
  intro htriple s r' s' hreq hact
  unfold Wp.triple at htriple
  specialize htriple _ hreq
  false_or_by_contra ; rename_i h ; simp at h
  apply hact ; apply LawfulAction.impl (post := ens) <;> try assumption
  intro r s hh ⟨heq,_⟩ ; subst_eqs ; apply h ; apply hh

theorem big_step_to_wp (act : Wp m σ ρ) [LawfulAction act] (req : SProp σ) :
  act.terminates req ->
  req s ->
  act s = act.toBigStep.toWp s := by
  intro hterm hreq; ext post; constructor
  { simp [BigStep.toWp]; intro _ _ _
    solve_by_elim [triple_sound_big_step'] }
  simp [BigStep.toWp]
  intro h; apply triple_sound_terminate (req := (s = ·)) <;> try simp
  { solve_by_elim }
  intro; simp_all

theorem exists_over_PUnit (p : PUnit → Prop) : (∃ (u : PUnit), p u) = p () := by
  simp ; constructor ; intro ⟨⟨⟩, h⟩ ; assumption ; intro h ; exists PUnit.unit

theorem triple_sound'_ret_unit [LawfulAction act] (req : SProp σ) (ens : RProp σ PUnit) :
  act.triple req ens → act.toActProp.triple req (ens () ·) := by
  have heq : (ens () ·) = (∃ r, ens r ·) := by ext ; rw [exists_over_PUnit]
  rw [heq] ; apply triple_sound'

theorem triple_sound'_ret_unit' [LawfulAction act] {st : σ} (ens : RProp σ PUnit) :
  act st ens → (∀ st', act.toActProp st st' → ens () st') := by
  have h := triple_sound'_ret_unit (act := act) (fun stt => stt = st) ens
  unfold Wp.triple ActProp.triple at h ; simp at h
  intro hq st' ; specialize h hq st st' rfl ; exact h

instance pure_sound : LawfulAction (Wp.pure (σ := σ) (m := m) r) where
  inter := by simp [pure, actSimp]
  impl  := by intros; simp_all [pure, actSimp]
  -- call  := by solve_by_elim

instance bind_sound (act : Wp m' σ ρ) (act' : ρ -> Wp m σ ρ') [LawfulAction act] [∀ r, LawfulAction (act' r)] : LawfulAction (Wp.bind (m := m) act act') where
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

  -- call := by
  --   unfold Wp.bind
  --   intros s post hbind
  --   apply LawfulAction.call; apply LawfulAction.impl;
  --   { intros _ _; apply LawfulAction.call }
  --   solve_by_elim

instance assume_sound : LawfulAction (Wp.assume (m := m) (σ := σ) rq) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]
  -- call := by solve_by_elim

instance assert_sound : LawfulAction (Wp.assert (m := m) (σ := σ) rq) where
  inter := by intros; simp_all [actSimp]; rename_i h; specialize h default; simp [*]
  impl  := by intros; simp_all [actSimp] <;> solve_by_elim
  -- call  := by solve_by_elim

instance require_sound : LawfulAction (Wp.require (m := m) (σ := σ) rq) where
  inter := by
    cases m
    { intros; simp_all [actSimp]; rename_i h; specialize h default; simp [*] }
    intros; simp_all [actSimp]
  impl := by cases m <;> (intros; simp_all [actSimp] <;> solve_by_elim)
  -- call := by
  --  intros s post; unfold Wp.require; simp [Wp.assert, Wp.assume]; solve_by_elim


instance fresh_sound : LawfulAction (Wp.fresh (m := m) (σ := σ) τ) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]
  -- call := by solve_by_elim


instance spec_sound : LawfulAction (Wp.spec (m := m) req ens) where
  inter := by
    cases m <;> (intros; simp_all [actSimp])
    rename_i h; intros; specialize h default; simp [*]
  impl := by
    cases m <;> (simp [actSimp]; intros)
    { constructor <;> (intros; solve_by_elim) }
    solve_by_elim
  -- call := by intros _; simp_all [actSimp]

instance (r : σ -> σ -> Prop) : LawfulAction (r.toWp (m := m)) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]
  -- call := by solve_by_elim

instance get_sound : LawfulAction (Wp.get (m := m) (σ := σ)) where
  inter := by intros; simp_all [get, getThe,MonadStateOf.get, Wp.get]
  impl := by intros; simp_all [get, getThe,MonadStateOf.get,Wp.get]
  -- call := by solve_by_elim

instance set_sound (s : σ) : LawfulAction (Wp.set s (m := m)) where
  inter := by intros; simp_all [Wp.set]
  impl := by intros; simp_all [Wp.set]
  -- call := by solve_by_elim

instance modifyGet_sound : LawfulAction (Wp.modifyGet f (m := m) (σ := σ) (ρ := ρ)) where
  inter := by intros; simp_all [Wp.modifyGet]
  impl := by intros; simp_all [Wp.modifyGet]
  -- call := by solve_by_elim

instance if_sound [Decidable c] [instT: LawfulAction t] [instS : LawfulAction e] : LawfulAction (ite c t e) where
  inter := by
    intros; by_cases c <;> simp_all <;> solve_by_elim [instT.inter, instS.inter]
  impl := by
    intros; by_cases c <;> simp_all <;> solve_by_elim [instT.impl, instS.impl]

instance (act : Wp m σ ρ) [IsSubStateOf σ σ'] [LawfulAction act] :
  LawfulAction (act.lift (σ' := σ')) where
  inter := by
    intros; simp_all [Wp.lift]
    solve_by_elim [LawfulAction.inter]
  impl := by
    intros; simp_all [Wp.lift]
    solve_by_elim [LawfulAction.impl]
  -- call := by
  --   intros; simp_all [monadLift, MonadLift.monadLift]
  --   solve_by_elim [LawfulAction.call]

/-! ### Correctness of `checkSpec` -/

-- theorem wp_spec_to_big_step :
--   (Wp.spec ens req).toBigStep (m := .internal) = BigStep.spec ens req := by
--   ext s r' s'; unfold Wp.spec BigStep.spec Wp.toBigStep Wp.toWlp; simp

theorem check_spec_sound [LawfulAction act] (req : SProp σ) (ens : σ -> RProp σ ρ) :
  (∀ s, req s -> act s (ens s)) ->
  Wp.spec (m := .internal) req ens <= act := by
  intro triple s post; simp [actSimp]; intros hreq hens
  solve_by_elim [LawfulAction.impl]

class GenBigStep (σ ρ : Type) (wp : Wp .external σ ρ) (tr : outParam (BigStep σ ρ)) where
  lawful : LawfulAction wp
  equiv pre  :
    wp.terminates pre -> ∀ s, pre s -> tr s = wp.toBigStep s

def BigStep.pure (r : ρ) : BigStep σ ρ := fun s r' s' => s' = s ∧ r' = r

def BigStep.bind (act : BigStep σ ρ) (act' : ρ -> BigStep σ ρ') : BigStep σ ρ' :=
  fun s r' s' => ∃ r s'', act s r s'' ∧ act' r s'' r' s'

def BigStep.assume (asm : Prop) : BigStep σ PUnit := fun s _ s' => asm ∧ s' = s
def BigStep.assert (ast : Prop) : BigStep σ PUnit := fun s _ s' => ast ∧ s' = s
def BigStep.fresh (τ : Type) : BigStep σ τ := fun s _r s' => s' = s
def BigStep.set (s : σ) : BigStep σ Unit := fun _s _r s' => s' = s
def BigStep.get : BigStep σ σ := fun s r s' => s' = s ∧ r = s
def BigStep.modifyGet (act : σ -> ρ × σ) : BigStep σ ρ := fun s r s' => let (ret, st) := act s; s' = st ∧ r = ret

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


/-- This theorem lets us lift a transition in a way that does not introduce
quantification over `σ` in the lifted transition. -/
theorem lift_transition_big_step' {σ σ'} [IsSubStateOf σ σ'] (m : Mode) (r : Wp m σ ρ) [LawfulAction r] (st : σ') :
  r.terminates (· = getFrom st) →
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

def BigStep.lift [IsSubStateOf σ σ'] (act : BigStep σ ρ) : BigStep σ' ρ :=
  fun st r' st' => act (getFrom st) r' (getFrom st') ∧ st' = (setIn (@getFrom σ σ' _ st') st)

instance {σ σ'} [IsSubStateOf σ σ'] (act : Wp .external σ ρ) (actTr : BigStep σ ρ) [inst:GenBigStep σ ρ act actTr]
  : GenBigStep σ' ρ (Wp.lift (σ' := σ') act) (BigStep.lift (σ := σ) actTr) where
  lawful := inferInstance
  equiv pre := by
    intro term s hpre; ext; dsimp;
    have : Wp.terminates (· = getFrom s) act := by simp; solve_by_elim
    unfold BigStep.lift
    rw [inst.equiv (pre := (getFrom s = ·))] <;> try simp [*]
    rwa [lift_transition_big_step']


theorem bind_terminates m (act : Wp m σ ρ) (act' : ρ -> Wp m σ ρ') s [LawfulAction act] :
  pre s ->
  act.terminates pre →
  (act.bind act').terminates pre ->
  act.toBigStep s r' s' ->
  (act' r').terminates (· = s') := by
    unfold Wp.terminates Wp.toBigStep Wp.toWlp Wp.bind
    intros hpre actT act'T
    have actT := actT s hpre
    have act'T := act'T s hpre
    have act''T := triple_sound_big_step' (act := act) (req := (· = s))
    unfold Wp.triple BigStep.triple Wp.toBigStep Wp.toWlp at act''T
    simp at act''T; specialize act''T _ act'T s r' s' rfl
    simp_all

attribute [-simp] not_and

instance (act : Wp .external σ ρ) (act' : ρ -> Wp .external σ ρ')
  [inst: GenBigStep σ ρ act actTr] [inst' : ∀ r, GenBigStep σ ρ' (act' r) (actTr' r)] :
  GenBigStep σ ρ' (act.bind act') (actTr.bind actTr') where
  lawful := inferInstance
  equiv pre := by
      unfold Wp.bind; --simp
      intros term s hpre
      have := @inst.lawful
      have actTerm : act |>.terminates pre := by
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
      rename_i hact'; simp [not_and_iff_or_not_not] at hact'
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
      apply triple_sound_big_step (req := (· = s)) <;> try simp_all [BigStep.triple]
      rintro s'' ret' st' rfl
      unfold  Wp.toBigStep Wp.toWlp; simp [not_and_iff_or_not_not]; intro _
      rcases hact' ret' st' with (h | h) <;> try solve_by_elim
      rw [(inst' ret').equiv (pre := (· = st'))] at h <;> try simp
      { unfold Wp.toBigStep Wp.toWlp at h; simp_all [not_and_iff_or_not_not] }
      have := (inst' ret').lawful
      apply bind_terminates (act := act) (act' := fun ret => act' ret) (pre := pre) <;> try solve_by_elim
      unfold Wp.toBigStep Wp.toWlp; simp [not_and_iff_or_not_not, *]

end Theory
