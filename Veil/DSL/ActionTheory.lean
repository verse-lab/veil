import Veil.DSL.Base

/-!
  # Action Language

  This file defines the syntax and semantics for the imperative language
  we use to define initializers and actions.
-/
section Veil
open Classical
/-! ## Types  -/
section Types

inductive Mode where
  | internal : Mode
  | external : Mode

/-! Our language is parametric over the state and return type. -/
variable (m : Mode) (σ ρ : Type)

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

set_option linter.unusedVariables false in
/-- Omni semantics, which relates a state `s : σ` to set of the possible program outcomes `post : RProp σ`
  We have two modes for this monad:
  - `internal` for function calls. When we call an action, callee should ensure all assertions are satisfied
    To model that we treat all `require` statements as `assert`'s.
  - `external` for enviorment calls. In this case envioremnt should provide a necessary conditions to
    satisfy all `require`'s. To model that we treat all `require` statements as `assume`'s. -/
abbrev Wlp (m : Mode) (σ ρ : Type) := σ -> RProp σ ρ -> Prop
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
   -/
@[actSimp]
def Wlp.toBigStep {σ} (act : Wlp m σ ρ) : BigStep σ ρ :=
  fun s r' s' => ¬ act s (fun r₀ s₀ => ¬ (r' = r₀ ∧ s' = s₀))

/-- [BigStep.toWlp] converts Big-step semantics to Omni one.

  Ideally, here we should also assert termination of `act`, but this will be handled
  via `Sound` condition later. -/
@[actSimp]
def BigStep.toWlp {σ} (act : BigStep σ ρ) : Wlp .internal σ ρ :=
  fun s post => ∀ r s', act s r s' -> post r s'


/-- Function which transforms any two-state formula into `Wlp` -/
@[actSimp]
def Function.toWlp (r : σ -> σ -> Prop) : Wlp .internal σ Unit :=
  fun s post => ∀ s', r s s' -> post () s'

/-- Function which transforms any `Wlp` into a two-state formula -/
@[actSimp]
def Wlp.toActProp {σ} (act : Wlp m σ ρ) : ActProp σ :=
  fun s s' => ¬ act s (fun _ s₀ => ¬ (s' = s₀))

/-! ### Languge statements -/

@[actSimp]
def Wlp.pure (r : ρ) : Wlp m σ ρ := fun s post => post r s
@[actSimp]
def Wlp.bind (wp : Wlp m σ ρ) (wp_cont : ρ -> Wlp m σ ρ') : Wlp m σ ρ' :=
  fun s post => wp s (fun r s' => wp_cont r s' post)

@[actSimp]
def Wlp.assume (asm : Prop) : Wlp m σ PUnit := fun s post => asm → post () s
@[actSimp]
def Wlp.assert (ast : Prop) : Wlp m σ PUnit := fun s post => ast ∧ post () s
@[actSimp]
def Wlp.fresh (τ : Type) : Wlp m σ τ := fun s post => ∀ t, post t s

@[actSimp]
def Wlp.require (rq : Prop) : Wlp m σ PUnit :=
  match m with
  | Mode.internal => Wlp.assert rq
  | Mode.external => Wlp.assume rq

/-- `Wlp.spec req ens` is the weakest precondition for a function with
  precondition `req` and postcondition `ens`.
-/
@[actSimp]
def Wlp.spec (req : SProp σ) (ens : σ -> RProp σ ρ) : Wlp m σ ρ :=
  fun s post =>
    match m with
    | .internal => req s ∧ ∀ r' s', (ens s r' s' -> post r' s')
    | .external => ∀ r' s', req s -> ens s r' s' -> post r' s'



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

instance : Monad (Wlp m σ) where
  pure := Wlp.pure
  bind := Wlp.bind

instance : MonadStateOf σ (Wlp m σ) where
  get := fun s post => post s s
  set s' := fun _ post => post () s'
  modifyGet := fun act s post => let (ret, s') := act s ; post ret s'

class IsStateExtension (σ : semiOutParam Type) (σ' : Type) where
  extendWith : σ -> σ' -> σ'
  restrictTo : σ' -> σ

export IsStateExtension (extendWith restrictTo)
instance [IsStateExtension σ σ'] : MonadLift (Wlp m σ) (Wlp m σ') where
  monadLift := fun m s post => m (restrictTo s) (fun r s' => post r (extendWith s' s))

/-! ### Soundness proof -/

abbrev refines {σ ρ} (act : Wlp m σ ρ) (act' : Wlp m σ ρ) : Prop :=
  ∀ s post, act s post -> act' s post

instance : LE (Wlp m σ ρ) where
  le := refines

abbrev Wlp.triple {σ ρ} (req : SProp σ) (act : Wlp m σ ρ) (ens : RProp σ ρ) : Prop :=
  ∀ s, req s -> act s ens

abbrev ActProp.triple {σ } (req : SProp σ) (act : ActProp σ) (ens : SProp σ) : Prop :=
  ∀ s s', req s -> act s s' -> ens s'


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
  - third condition `call`, states that the `internal` mode of `act` refines the `external`
    one. In other words, if you have proven some striple for `internal` mode of `act`,
    the same one holds for its `external` version -/
class Sound {σ ρ : Type} (act : (m : Mode) -> Wlp m σ ρ) where
  inter {m} {τ : Type} [Inhabited τ] (post : τ -> RProp σ ρ) :
    ∀ s : σ, (∀ t : τ, act m s (post t)) -> act m s (∀ t, post t · ·)
  impl (post post' : RProp σ ρ) : ∀ s,
    (∀ r s, post r s -> post' r s) -> act m s post -> act m s post'
  call : act .internal <= act .external

theorem sound_and (act : ∀ m, Wlp m σ ρ) [Sound act] :
  act m s post -> act m s post' -> act m s fun r s => post r s ∧ post' r s := by
  intro hact hact'
  let Post := fun (b : Bool) => if b then post' else post
  have post_eq : (fun r s => ∀ b, Post b r s) = fun r s => post r s ∧ post' r s := by
    unfold Post; simp
  rw [<-post_eq]; apply Sound.inter <;> simp [*, Post]

-- theorem sound_terminates [Sound act] : (∀ r s, post r s) -> act m s post := by
--   intro hpost
--   have post_eq : post = (fun _ _ => Empty -> True) := by ext; simp_all
--   rw [post_eq]; apply Sound.inter; rintro ⟨⟩

-- theorem wlp_sound (act : ∀ m, Wlp m σ ρ) [Sound act] :
--   ∀ s post, (act m).toBigStep.toWlp (m := m) s post <-> act m s post := by
--   intro s post; constructor
--   { unfold Wlp.toBigStep BigStep.toWlp; simp
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
  (act m).toActProp.triple req ens -> (act m).triple req (fun _ => ens) := by
  intro ensTaut htriple s hreq
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
  specialize htriple _ _ ‹_› ‹_›; contradiction

instance : Sound (Wlp.pure (m := ·) (σ := σ) r) where
  inter := by simp [actSimp]
  impl  := by intros; simp_all [actSimp]
  call  := by solve_by_elim

instance (act' : ρ -> ∀ m, Wlp m σ ρ) [Sound act] [∀ r, Sound (act' r)] : Sound (fun m => Wlp.bind (act m) (act' · m)) where
  inter := by
    unfold Wlp.bind
    intros m τ _ post s hbind
    apply Sound.impl (∀ t, act' · m · <| post t) <;> solve_by_elim [Sound.inter]
  impl := by
    unfold Wlp.bind
    intros m post post' s hpost hbind
    apply Sound.impl (act' · m · <| post) <;> (intros; solve_by_elim [Sound.impl])
  call := by
    unfold Wlp.bind
    intros s post hbind
    apply Sound.call; apply Sound.impl;
    { intros _ _; apply Sound.call }
    solve_by_elim

instance : Sound (Wlp.assume (m := ·) (σ := σ) rq) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]
  call := by solve_by_elim

instance : Sound (Wlp.assert (m := ·) (σ := σ) rq) where
  inter := by intros; simp_all [actSimp]; rename_i h; specialize h default; simp [*]
  impl  := by intros; simp_all [actSimp] <;> solve_by_elim
  call  := by solve_by_elim

instance : Sound (Wlp.require (m := ·) (σ := σ) rq) where
  inter := by
    intros m; cases m
    { intros; simp_all [actSimp]; rename_i h; specialize h default; simp [*] }
    intros; simp_all [actSimp]
  impl := by intros m; cases m <;> (intros; simp_all [actSimp] <;> solve_by_elim)
  call := by
   intros s post; unfold Wlp.require; simp [Wlp.assert, Wlp.assume]; solve_by_elim


instance : Sound (Wlp.fresh (m := ·) (σ := σ) τ) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]
  call := by solve_by_elim


instance : Sound (Wlp.spec (m := ·) req ens) where
  inter := by
    intro m; cases m <;> (intros; simp_all [actSimp])
    rename_i h; intros; specialize h default; simp [*]
  impl := by
    intro m; cases m <;> (simp [actSimp]; intros)
    { constructor <;> (intros; solve_by_elim) }
    solve_by_elim
  call := by intros _; simp_all [actSimp]

instance (r : σ -> σ -> Prop) : Sound (fun _ => r.toWlp) where
  inter := by intros; simp_all [actSimp]
  impl := by intros; simp_all [actSimp]
  call := by solve_by_elim

instance : Sound (get (m := Wlp · σ)) where
  inter := by intros; simp_all [get, getThe,MonadStateOf.get]
  impl := by intros; simp_all [get, getThe,MonadStateOf.get]
  call := by solve_by_elim

instance (s : σ) : Sound (set s (m := Wlp · σ)) where
  inter := by intros; simp_all [set,MonadStateOf.set]
  impl := by intros; simp_all [set,MonadStateOf.set]
  call := by solve_by_elim

instance : Sound (modifyGet f (m := Wlp · σ)) where
  inter := by intros; simp_all [modifyGet,MonadStateOf.modifyGet]
  impl := by intros; simp_all [modifyGet,MonadStateOf.modifyGet]
  call := by solve_by_elim

instance (act : ∀ m, Wlp m σ ρ) [IsStateExtension σ σ'] [Sound act] :
  Sound (fun m => monadLift (m := Wlp m σ) (n := Wlp m σ') (act m)) where
  inter := by
    intros; simp_all [monadLift, MonadLift.monadLift]
    solve_by_elim [Sound.inter]
  impl := by
    intros; simp_all [monadLift, MonadLift.monadLift]
    solve_by_elim [Sound.impl]
  call := by
    intros; simp_all [monadLift, MonadLift.monadLift]
    solve_by_elim [Sound.call]

/-! ### Correctness of `checkSpec` -/

theorem wlp_spec_to_big_step :
  (Wlp.spec ens req).toBigStep (m := .internal) = BigStep.spec ens req := by
  ext s r' s'; unfold Wlp.spec BigStep.spec Wlp.toBigStep; simp

theorem check_spec_sound [Sound act] (req : SProp σ) (ens : σ -> RProp σ ρ) :
  (∀ s, req s -> act m s (ens s)) ->
  Wlp.spec (m := .internal) req ens <= act m := by
  intro triple s post; simp [actSimp]; intros hreq hens
  solve_by_elim [Sound.impl]

end Theory
