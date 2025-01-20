import Veil.DSL.Base

/-!
  # Action Language

  This file defines the syntax and semantics for the imperative language
  we use to define initializers and actions.
-/
section Veil

/-! ## Types  -/
section Types
/-! Our language is parametric over the state and return type. -/
variable (σ ρ : Type)

/-- One-state formula -/
@[inline] abbrev SProp := σ -> Prop
/-- One-state formula that also talks about the return value. -/
@[inline] abbrev RProp (ρ : Type u) := ρ → SProp σ
/-- Two-state formula -/
@[inline] abbrev ActProp := σ -> σ -> Prop

/- In Veil we will be using two different types of semantics:
  - [Wlp]: Omni semantics, which relates a state `s : σ` to set of the
    possible program outcomes `post : RProp σ`
  - [BigStep]: Standard big-step semantics, which relates a state `s : σ`
    to a return value `r : ρ` and a post-state `s' : σ`
-/

/-- Omni semantics, which relates a state `s : σ` to set of the possible program outcomes `post : RProp σ` -/
abbrev Wlp     := σ -> RProp σ ρ -> Prop
/-- [BigStep]: Standard big-step semantics, which relates a state `s : σ` to a return value `r : ρ` and a post-state `s' : σ` -/
abbrev BigStep := σ -> ρ -> σ -> Prop

end Types

/-! ## Theory  -/
section Theory

variable {σ ρ : Type}

/-! ### Relation between `BigStep` and `Wlp`  -/

/-- `Wlp.toBigStep` converts Omni semantics to a Big-step one. Note that, it only
  makes sence is `act` terminates, in other words, the following holds

  ```∀ s, ∃ Q, act s Q```

  If the statement above does not hold, then ```act s Q``` should be false for all `Q`.
  In this case, `act.toBigStep s r' s'` will be true for all `r'` and `s'`, which is
  not what we not.

  In theory we could add  ```∀ s, ∃ Q, act s Q``` condition to this definition, but
  this will duplicate the body of `act` twice, increasing the formula which we eventually
  send to the solver.

  Instead, we will add this condition to the `Sound` class, which will allow us to prove
  the soundness of the `Wlp.toBigStep` conversion for all `Sound` actions. And then we
  show that all actions we are using in our framework are `Sound`.
   -/
@[actSimp]
def Wlp.toBigStep {σ} (act : Wlp σ ρ) : BigStep σ ρ :=
  fun s r' s' => ¬ act s (fun r₀ s₀ => ¬ (r' = r₀ ∧ s' = s₀))

/-- [BigStep.toWlp] converts Big-step semantics to Omni one.

  Ideally, here we should also assert termination of `act`, but this will be handled
  via `Sound` condition later. -/
@[actSimp]
def BigStep.toWlp {σ} (act : BigStep σ ρ) : Wlp σ ρ :=
  fun s post => ∀ r s', act s r s' -> post r s'


/-- Function which transforms any two-state formula into `Wlp` -/
@[actSimp]
def Function.toWlp (r : σ -> σ -> Prop) : Wlp σ Unit :=
  fun s post => ∀ s', r s s' -> post () s'

/-- Function which transforms any `Wlp` into a two-state formula -/
@[actSimp]
def Wlp.toActProp {σ} (act : Wlp σ ρ) : ActProp σ :=
  fun s s' => ¬ act s (fun _ s₀ => ¬ (s' = s₀))

/-! ### Languge statements -/

@[actSimp]
def Wlp.pure (r : ρ) : Wlp σ ρ := fun s post => post r s
@[actSimp]
def Wlp.bind (wp : Wlp σ ρ) (wp_cont : ρ -> Wlp σ ρ') : Wlp σ ρ' :=
  fun s post => wp s (fun r s' => wp_cont r s' post)

@[actSimp]
def Wlp.assume (rq : Prop) : Wlp σ PUnit := fun s post => rq → post () s
-- @[actSimp]
-- def Wlp.assert (as : Prop) : Wlp σ PUnit := fun s post => as ∧ post () s
@[actSimp]
def Wlp.fresh (τ : Type) : Wlp σ τ := fun s post => ∀ t, post t s

/-- `Wlp.spec req ens` is the weakest precondition for a function with
  precondition `req` and postcondition `ens`.
  The intuition begind this definition is:
  - if `req s` holds in a current state `s`, then we it is equivalent to
    `∀ r' s', ens s r' s' -> post r' s'`, meaning that, we have to prove
    `post`, assuming that `ens` holds.
  - if `req s` does not hold, then we do not know anything about the behiavor
    of the function i.e. it can execute to any post-state `s'` and return any
    value `r'`. Hence we have to show `post` for all possible return values.
    `Wlp.spec` in this case is equivalent to `∀ r' s', post r' s'`.
-/
@[actSimp]
def Wlp.spec (req : SProp σ) (ens : σ -> RProp σ ρ) : Wlp σ ρ :=
  fun s post => ∀ r' s', (req s -> ens s r' s') -> post r' s'

def BigStep.spec (req : SProp σ) (ens : σ -> RProp σ ρ) : BigStep σ ρ :=
  fun s r s' => req s -> ens s r s'

-- def BigStep.choice : BigStep σ ρ -> BigStep σ ρ -> BigStep σ ρ :=
--   fun act act' s r s' => act s r s' ∨ act' s r s'

/- BAD: it duplicates post -/
-- def Wlp.choice : Wlp σ ρ -> Wlp σ ρ -> Wlp σ ρ :=
--   fun wp wp' s post => wp s post ∨ wp' s post

-- def Wlp.choice (wp : Wlp σ ρ) (wp' : Wlp σ ρ) : Wlp σ ρ :=
--   wp.toBigStep.choice wp'.toBigStep |>.toWlp

/-! ### Monad Instances -/

instance : Monad (Wlp σ) where
  pure := Wlp.pure
  bind := Wlp.bind

instance : MonadStateOf σ (Wlp σ) where
  get := fun s post => post s s
  set s' := fun _ post => post () s'
  modifyGet := fun act s post => let (ret, s') := act s ; post ret s'

class IsStateExtension (σ : semiOutParam Type) (σ' : Type) where
  extendWith : σ -> σ' -> σ'
  restrictTo : σ' -> σ

export IsStateExtension (extendWith restrictTo)
instance [IsStateExtension σ σ'] : MonadLift (Wlp σ) (Wlp σ') where
  monadLift := fun m s post => m (restrictTo s) (fun r s' => post r (extendWith s' s))

/-! ### Soundness proof -/

/-- `Sound act` states the set of minimal conditions on `act` that are required
  to prove the soundness of the `Wlp.toBigStep` conversion.
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

  Note that, as captured by `sound_terminates`, the `Sound act` ensures that `act`
  terminates.
-/
class Sound {σ ρ : Type} (act : Wlp σ ρ) where
  inter {τ : Type} (post : τ -> RProp σ ρ) :
    ∀ s : σ, (∀ t : τ, act s (post t)) -> act s (∀ t, post t · ·)
  impl (post post' : RProp σ ρ) : ∀ s,
    (∀ r s, post r s -> post' r s) -> act s post -> act s post'

theorem sound_and (act : Wlp σ ρ) [Sound act] :
  act s post -> act s post' -> act s fun r s => post r s ∧ post' r s := by
  intro hact hact'
  let Post := fun (b : Bool) => if b then post' else post
  have post_eq : (fun r s => ∀ b, Post b r s) = fun r s => post r s ∧ post' r s := by
    unfold Post; simp
  rw [<-post_eq]; apply Sound.inter <;> simp [*, Post]

theorem sound_terminates [Sound act] : (∀ r s, post r s) -> act s post := by
  intro hpost
  have post_eq : post = (fun _ _ => Empty -> True) := by ext; simp_all
  rw [post_eq]; apply Sound.inter; rintro ⟨⟩

theorem wlp_sound (act : Wlp σ ρ) [Sound act] :
  ∀ s post, act.toBigStep.toWlp s post <-> act s post := by
  intro s post; constructor
  { unfold Wlp.toBigStep BigStep.toWlp; simp
    intro hact
    have post_impl : ∀ r s, (∀ r' s', ¬ post r' s' -> ¬ (r' = r ∧ s' = s)) -> post r s := by
      intro r s impl
      false_or_by_contra
      specialize impl r s; apply impl <;> simp_all
    apply Sound.impl; apply post_impl
    apply Sound.inter; intro r'
    apply Sound.inter; intro s'
    by_cases postrs : post r' s'
    { apply sound_terminates; simp_all }
    apply Sound.impl (post := fun r₀ s₀ => r' = r₀ → ¬s' = s₀) <;> simp_all
    false_or_by_contra
    specialize hact _ _ ‹_›; contradiction }
  intro hact r' s' h
  false_or_by_contra; apply h; apply Sound.impl (post := post)
  { intros; intro _; simp_all }
  assumption

theorem triple_sound [Sound act] (req : SProp σ) (ens : SProp σ) :
  (∀ s s', req s -> act.toActProp s s' -> ens s') ->
  ∀ s, req s -> act s (fun _ => ens) := by
  intro htriple s hreq
  have ens_impl : ∀ s, (∀ s', ¬ ens s' -> ¬ (s' = s)) -> ens s := by
    intro s impl
    false_or_by_contra
    specialize impl s; apply impl <;> simp_all
  apply Sound.impl; intro _; apply ens_impl
  apply Sound.inter; intro s'
  by_cases hens : ens s'
  { apply sound_terminates; simp_all }
  apply Sound.impl (post := fun r₀ s₀ => ¬s' = s₀) <;> (intros; try simp_all)
  false_or_by_contra
  specialize htriple _ _ ‹_› ‹_›; contradiction

instance : Sound (Wlp.pure (σ := σ) r) where
  inter := by simp [actSimp]
  impl := by intros; simp_all [actSimp]

instance [Sound act] [∀ r, Sound (act' r)] : Sound (Wlp.bind act act') where
  inter := by
    unfold Wlp.bind
    intros τ post s hbind
    apply Sound.impl (∀ t, act' · · <| post t) <;> solve_by_elim [Sound.inter]
  impl := by
    unfold Wlp.bind
    intros post post' s hpost hbind
    apply Sound.impl (act' · · <| post) <;> (intros; solve_by_elim [Sound.impl])

instance : Sound (Wlp.assume (σ := σ) rq) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]

instance : Sound (Wlp.fresh (σ := σ) τ) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]

instance : Sound (Wlp.spec req ens) where
  inter := by intros; simp_all [actSimp]
  impl := by simp [actSimp]; intros; solve_by_elim

instance (r : σ -> σ -> Prop) : Sound (r.toWlp) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]

instance : Sound (get (σ := σ)) where
  inter := by intros; simp_all [get, getThe,MonadStateOf.get]
  impl := by intros; simp_all [get, getThe,MonadStateOf.get]

instance (s : σ) : Sound (set s : Wlp σ PUnit) where
  inter := by intros; simp_all [set,MonadStateOf.set]
  impl := by intros; simp_all [set,MonadStateOf.set]

instance : Sound (modifyGet (σ := σ) f) where
  inter := by intros; simp_all [modifyGet,MonadStateOf.modifyGet]
  impl := by intros; simp_all [modifyGet,MonadStateOf.modifyGet]

instance (act : Wlp σ ρ) [IsStateExtension σ σ'] [Sound act] :
  Sound (monadLift act : Wlp σ' ρ) where
  inter := by
    intros; simp_all [monadLift, MonadLift.monadLift]
    solve_by_elim [Sound.inter]
  impl := by
    intros; simp_all [monadLift, MonadLift.monadLift]
    solve_by_elim [Sound.impl]

/-! ### Correctness of `checkSpec` -/

theorem wlp_spec_to_big_step :
  (Wlp.spec ens req).toBigStep = BigStep.spec ens req := by
  ext s r' s'; unfold Wlp.spec BigStep.spec Wlp.toBigStep; simp

theorem check_spec_sound [Sound act] (req : SProp σ) (ens : σ -> RProp σ ρ) :
  (∀ s, req s -> act s (ens s)) ->
  (∀ s post, Wlp.spec req ens s post -> act s post) := by
  intro triple s post hspec
  apply Sound.impl; apply hspec
  have: ∀ r' s', ({t : Unit // req s} → ens s r' s') ->  (req s → ens s r' s') := by
    intro r' s' h hreq; apply h; exact ⟨(), hreq⟩
  apply Sound.impl; apply this
  apply Sound.inter; rintro ⟨_, hreq⟩
  solve_by_elim

end Theory
