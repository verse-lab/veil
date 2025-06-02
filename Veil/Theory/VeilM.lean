import Veil.DSL.Base
import Loom.MonadAlgebras.NonDetT'.Extract

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

instance : ToString Mode where
  toString := fun m => match m with
  | .internal => "internal"
  | .external => "external"

abbrev ExId := Int

/-! Our language is parametric over the mutable state, immutable state, and return type. -/

set_option linter.unusedVariables false in
abbrev VeilExecM (m : Mode) (σ ρ α : Type) := ReaderT ρ (StateT σ (ExceptT ExId DivM)) α

abbrev VeilM (m : Mode) (σ ρ α : Type) := NonDetT (VeilExecM m σ ρ) α
abbrev BigStep (ρ σ α : Type) := ρ -> σ -> α -> σ -> Prop
abbrev SProp (ρ σ : Type) := ρ -> σ -> Prop
abbrev RProp (α ρ σ : Type) := α -> SProp ρ σ
abbrev TwoState (ρ σ : Type) := ρ -> σ -> σ -> Prop

end Types

/-! ## Theory  -/
section Theory


macro "[DemonSucc|" t:term "]" : term =>  `(open PartialCorrectness DemonicChoice ExceptionAsSuccess in $t)
macro "[DemonFail|" t:term "]" : term =>  `(open PartialCorrectness DemonicChoice ExceptionAsFailure in $t)
macro "[AngelFail|" t:term "]" : term =>  `(open TotalCorrectness AngelicChoice ExceptionAsFailure in $t)


variable {m : Mode} {σ ρ α : Type}

def VeilM.succesfullyTerminates (act : VeilM m σ ρ α) (pre : SProp ρ σ) : Prop :=
  [DemonFail| triple pre act ⊤]

def VeilM.preservesInvariantsOnSuccesful (act : VeilM m σ ρ α) (inv : SProp ρ σ) : Prop :=
  [DemonSucc| triple inv act (fun _ => inv)]

def VeilM.succeedsAndPreservesInvariants (act : VeilM m σ ρ α) (inv : SProp ρ σ) : Prop :=
  [DemonFail| triple inv act (fun _ => inv)]

def VeilM.assumptions (act : VeilM m σ ρ α) (ex : ExtractNonDet WeakFindable act) : SProp ρ σ :=
  [DemonFail| ex.prop]

def VeilM.toTwoState (act : VeilM m σ ρ α) : TwoState ρ σ :=
  fun r₀ s₀ s₁ =>
    [AngelFail| triple (fun r s => r = r₀ ∧ s = s₀) act (fun _ r s => r = r₀ ∧ s = s₁)]

def VeilExecM.operational (act : VeilExecM m σ ρ α) (r₀ : ρ) (s₀ : σ) (res : Except ExId σ) : Prop :=
  match act r₀ s₀ with
  | .div => False
  | .res (.error i) => res = .error i
  | .res (.ok (_, s)) => .ok s = res

def VeilExecM.axiomatic (act : VeilExecM m σ ρ α) (r₀ : ρ) (s₀ : σ) (post : RProp α ρ σ) : Prop :=
  match act r₀ s₀ with
  | .div => False
  | .res (.error _) => False
  | .res (.ok (a, s)) => post a r₀ s

def VeilExecM.operationalTriple (act : VeilExecM m σ ρ α) (pre : SProp ρ σ) (post : SProp ρ σ) : Prop :=
  ∀ r₀ s₀ res,
    pre r₀ s₀ ->
    act.operational r₀ s₀ res ->
    match res with
    | .ok s₁ => post r₀ s₁
    | .error _ => False

def TwoState.triple (act : TwoState ρ σ) (pre : SProp ρ σ) (post : SProp ρ σ) : Prop :=
  ∀ r₀ s₀ s₁,
    pre r₀ s₀ ->
    act r₀ s₀ s₁ ->
    post r₀ s₁

def TwoState.preservesInvariantsOnSuccesful (act : TwoState ρ σ) (inv : SProp ρ σ) : Prop :=
  act.triple inv inv

section WpSoundness
open PartialCorrectness

lemma VeilExecM.terminates_preservesInvariants_wp (act : VeilExecM m σ ρ α) :
  [DemonFail| wp act inv'] ⊓ [DemonSucc| wp act inv] = [DemonFail| wp act (inv' ⊓ inv)] := by
    simp only [ReaderT.wp_eq, StateT.wp_eq, wp_tot_eq, «Prop».bot_eq_false, wp_part_eq, Pi.inf_apply]
    ext; simp only [«Prop».top_eq_true, Pi.inf_apply, <-wp_and]; congr! 1; ext (_|_) <;> simp


lemma VeilM.terminates_preservesInvariants_wp (act : VeilM m σ ρ α) :
  [DemonFail| wp act inv₁] ⊓ [DemonSucc| wp act inv₂] <= [DemonFail| wp act (inv₁ ⊓ inv₂)] := by
    unhygienic induction act <;> simp [-le_iInf_iff]
    { rw [x.terminates_preservesInvariants_wp];
      open ExceptionAsFailure in apply wp_cons
      solve_by_elim }
    rw [← @iInf_inf_eq];  simp only [meet_himp _ _ _ _ rfl]
    apply iInf_mono; intro; (expose_names; exact himp_le_himp (fun i_1 i_2 a => a) (f_ih i))


lemma VeilM.terminates_preservesInvariants (act : VeilM m σ ρ α) (inv : SProp ρ σ) :
  act.succesfullyTerminates inv ->
  act.preservesInvariantsOnSuccesful inv ->
  act.succeedsAndPreservesInvariants inv := by
  unfold VeilM.succesfullyTerminates VeilM.preservesInvariantsOnSuccesful VeilM.succeedsAndPreservesInvariants triple
  intros h₁ h₂; apply le_trans
  apply le_inf h₁ h₂; apply le_trans; apply VeilM.terminates_preservesInvariants_wp
  simp

lemma VeilM.triple_sound
  (act : VeilM m σ ρ α) (inv : SProp ρ σ) (ex : ExtractNonDet WeakFindable act) :
  act.succesfullyTerminates inv ->
  act.preservesInvariantsOnSuccesful inv ->
  (act.runWeak ex).operationalTriple (inv ⊓ act.assumptions ex) inv := by
    intros term invs
    have : [DemonFail| triple (inv ⊓ act.assumptions ex) (act.runWeak ex) (fun _ => inv)] := by
      simp [VeilM.assumptions]
      open DemonicChoice ExceptionAsFailure in
      apply ExtractNonDet.extract_refines_triple_weak
      apply le_trans';
      { apply VeilM.terminates_preservesInvariants <;> simp [*] }
      all_goals simp
    revert this; simp [triple]
    generalize (act.runWeak ex) = act
    introv h r hinv;
    have := h _ _ hinv; revert this
    simp [VeilExecM.operational, ReaderT.wp_eq, StateT.wp_eq, wp_tot_eq]
    simp [wp, liftM, monadLift, MProp.lift, MPropOrdered.μ, Functor.map]
    cases act r s₀ <;> simp; split <;> intros <;> (try subst_vars) <;> simp_all


end WpSoundness

section BigStepSoundness

lemma VeilExecM.total_imp_partial (act : VeilExecM m σ ρ α) :
  [AngelFail| wp act post] <= [DemonFail| wp act post] := by
  simp [ReaderT.wp_eq, StateT.wp_eq, wp_tot_eq, wp_part_eq]
  intro r s; simp [wp, liftM, monadLift, MProp.lift, Functor.map,
    PartialCorrectness.instMPropOrderedDivMProp, TotalCorrectness.instMPropOrderedDivMProp]
  cases (act r s) <;> simp; split <;> simp [loomLogicSimp]

instance (x : VeilM m σ ρ α) : Nonempty (ExtractNonDet WeakFindable x) := by
  unhygienic induction x;
  { constructor; exact (ExtractNonDet.pure _) }
  { constructor
    exact (ExtractNonDet.vis _ _ (fun a => f_ih a |>.some)) }
  constructor
  apply ExtractNonDet.pickSuchThat
  { refine ⟨.none, by simp⟩ }
  exact fun t => f_ih t |>.some

noncomputable
instance (x : VeilM m σ ρ α) : Inhabited (ExtractNonDet WeakFindable x) := by
  exact inhabited_of_nonempty'

lemma VeilM.angel_fail_imp_assumptions (act : VeilM m σ ρ α) :
  [AngelFail| wp act post r s] <= ∃ ex, act.assumptions ex r s ∧ (act.runWeak ex).axiomatic r s post := by
  unhygienic induction act generalizing r s <;> simp [VeilM.assumptions, ExtractNonDet.prop, -top_le_iff]
  { intro; exists (ExtractNonDet.pure _); }
  { open TotalCorrectness ExceptionAsFailure in
    rw [ReaderT.wp_eq]; simp [StateT.wp_eq, wp_tot_eq, wp_part_eq, DivM.wp_eq]
    split; simp; split; <;> (try simp); intro h
    rename_i bs _
    specialize f_ih _ h; rcases f_ih with ⟨ex, h⟩
    exists (ExtractNonDet.vis _ _ (fun b => if h : b = bs.1 then by rw [h]; exact ex else default))
    simp [ExtractNonDet.prop]; constructor
    { open PartialCorrectness DemonicChoice ExceptionAsFailure in apply wp_wlp x
      open PartialCorrectness ExceptionAsFailure in
      simp [ReaderT.wp_eq, StateT.wp_eq, wp_tot_eq, wp_part_eq, PartialCorrectness.DivM.wp_eq, *]
      apply h.1 }
    simp [VeilExecM.axiomatic, NonDetT.runWeak, NonDetT.extractWeak,
      bind, ReaderT.bind, StateT.bind, StateT.map, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    simp [*]; apply h.2 }
  simp [loomLogicSimp]; intros x px h
  specialize f_ih _ h; rcases f_ih with ⟨ex, h⟩
  exists (@ExtractNonDet.pickSuchThat _ _ _ _ _ _ ?_ ?_)
  { refine ⟨.some x, by simp [*]⟩ }
  { exact fun b => if h : b = x then by rw [h]; exact ex else default }
  simp [ExtractNonDet.prop]; constructor; apply h.1
  simp [VeilExecM.axiomatic, NonDetT.runWeak, NonDetT.extractWeak]
  apply h.2

lemma VeilM.toTwoState_sound (act : VeilM m σ ρ α) :
  act.toTwoState r₀ s₀ s₁ ->
  ∃ ex,
    act.assumptions ex r₀ s₀ ∧
    (act.runWeak ex).operational r₀ s₀ (Except.ok s₁) := by
  intro h;
  specialize h r₀ s₀; simp at h
  have h := act.angel_fail_imp_assumptions h
  rcases h with ⟨ex, h⟩; exists ex; constructor; apply h.1
  revert h; simp [VeilExecM.axiomatic, VeilExecM.operational]
  -- split <;> simp [*]


lemma VeilExecM.wlp_eq (act : VeilExecM m σ ρ α) (post : RProp α ρ σ) :
  [AngelFail| wlp act post] = [DemonFail| wlp act post] := by
  open ExceptionAsFailure in
  simp [ReaderT.wlp_eq, StateT.wlp_eq]
  simp [wlp, wp_tot_eq, TotalCorrectness.DivM.wp_eq, PartialCorrectness.DivM.wp_eq]
  ext; split <;> simp [loomLogicSimp]

lemma VeilM.assumptions_eq (act : VeilM m σ ρ α) (ex : ExtractNonDet WeakFindable act) :
  [DemonFail| ExtractNonDet.prop act ex] = [AngelFail| ExtractNonDet.prop act ex] := by
  induction ex <;> simp [ExtractNonDet.prop, -top_le_iff, VeilExecM.wlp_eq, *]

lemma VeilM.toBigStep_complete (act : VeilM m σ ρ α) (ex : ExtractNonDet WeakFindable act) :
  act.assumptions ex r₀ s₀ ->
  (act.runWeak ex).operational r₀ s₀ (Except.ok s₁) ->
  act.toTwoState r₀ s₀ s₁ := by
  intro h₁ h₂
  open AngelicChoice TotalCorrectness ExceptionAsFailure in
  apply ExtractNonDet.extract_refines_triple (inst := ex)
  { intro r s; simp; rintro rfl rfl
    revert h₂; simp [triple, VeilExecM.operational, ReaderT.wp_eq, StateT.wp_eq, wp_tot_eq,
      TotalCorrectness.DivM.wp_eq]
    simp [NonDetT.runWeak]
    cases (NonDetT.extractWeak act ex r s) <;> simp [*]
    split <;> aesop }
  intro r s; simp; rintro rfl rfl
  revert h₁; simp [VeilM.assumptions, VeilM.assumptions_eq];

end BigStepSoundness

section Deriving

macro "[Raises" ex:term "|" t:term "]" : term =>  `(open PartialCorrectness DemonicChoice in let _ : IsHandler $ex := ⟨⟩; $t)

def VeilM.raises (ex : Set ExId) (act : VeilM m σ ρ α) (pre : SProp ρ σ) : Prop :=
  [Raises ex| triple pre act (fun _ => ⊤)]

def VeilM.toBigStepDerived (act : VeilM m σ ρ α) : TwoState ρ σ :=
  fun r₀ s₀ s₁ =>
    [Raises (fun (_ : ExId) => True)| iwp act (fun _ r s => r = r₀ ∧ s = s₁) r₀ s₀]

open PartialCorrectness in
lemma VeilExecM.not_raises_imp_terminates_wp (act : VeilExecM m σ ρ α)
  (invEx : ExId -> RProp α ρ σ) :
  ⨅ ex, [Raises (· ≠ ex)| wp act (invEx ex)] <= [DemonFail| wp act (iInf invEx)] := by
  simp [ReaderT.wp_eq, StateT.wp_eq, wp_tot_eq, wp_except_handler_eq]
  intro x y; simp [iInf_apply, wp, liftM, monadLift, MProp.lift, MPropOrdered.μ, Functor.map]
  cases (act x y) <;> simp; split <;> simp [loomLogicSimp]

open PartialCorrectness in
lemma VeilM.not_raises_imp_terminates_wp (act : VeilM m σ ρ α)
  (invEx : ExId -> RProp α ρ σ) :
  ⨅ ex, [Raises (· ≠ ex)| wp act (invEx ex)] <= [DemonFail| wp act (iInf invEx)] := by
  dsimp; unhygienic induction act <;> simp [-le_iInf_iff]
  { apply le_trans; apply VeilExecM.not_raises_imp_terminates_wp;
    open ExceptionAsFailure in apply wp_cons; intro y
    simp; apply f_ih }
  rw [iInf_comm]; apply iInf_mono; intro i
  by_cases h : p i <;> simp [h,f_ih]

lemma VeilM.not_raises_imp_terminates (act : VeilM m σ ρ α) (pre : SProp ρ σ) :
  (∀ ex, act.raises (· ≠ ex) pre) ->
  act.succesfullyTerminates pre := by
  unfold VeilM.raises VeilM.succesfullyTerminates triple
  simp; rw [<-le_iInf_iff (ι := ExId)]; intro h;
  have : (⊤ : RProp α ρ σ) = iInf (fun (_ : ExId) => ⊤) := by simp
  rw [this]
  solve_by_elim [VeilM.not_raises_imp_terminates_wp, le_trans']


lemma VeilM.preservesInvariantsOnSuccesful_of_raises_true (act : VeilM m σ ρ α) (inv : SProp ρ σ) :
  [Raises (fun (_ : ExId) => True)| triple inv act (fun _ => inv)] ->
  act.preservesInvariantsOnSuccesful inv := by intro h; apply h

lemma VeilExecM.raises_true_imp_wp_eq_angel_fail_iwp (act : VeilExecM m σ ρ α) (post : RProp α ρ σ) :
  [Raises (fun (_ : ExId) => True)| iwp act post] = [AngelFail| wp act post] := by
  simp [iwp, ReaderT.wp_eq, StateT.wp_eq, wp_tot_eq, wp_part_eq]
  ext r s; simp [wp, liftM, monadLift, MProp.lift, Functor.map,
    PartialCorrectness.instMPropOrderedDivMProp, TotalCorrectness.instMPropOrderedDivMProp]
  cases (act r s) <;> simp; split <;> simp [loomLogicSimp]


lemma VeilM.raises_true_imp_wp_eq_angel_fail_iwp (act : VeilM m σ ρ α) (post : RProp α ρ σ) :
  [Raises (fun (_ : ExId) => True)| iwp act post] = [AngelFail| wp act post] := by
  unhygienic induction act <;> simp [iwp]
  { rw [<-VeilExecM.raises_true_imp_wp_eq_angel_fail_iwp]
    simp [iwp, <-f_ih, @Pi.compl_def] }
  simp [@compl_iInf, himp_eq, <-f_ih, inf_comm]

lemma VeilM.toBigStepDerived_sound (act : VeilM m σ ρ α) :
  act.toTwoState = act.toBigStepDerived := by
    unfold VeilM.toTwoState VeilM.toBigStepDerived
    simp [<-VeilM.raises_true_imp_wp_eq_angel_fail_iwp, triple, LE.le]

open PartialCorrectness DemonicChoice ExceptionAsSuccess in
lemma VeilM.wp_iInf {ι : Type} (act : VeilM m σ ρ α) (post : ι -> RProp α ρ σ) :
  wp act (fun a r s => iInf (fun i => post i a r s)) = ⨅ i, wp act (post i) := by
  by_cases h: Nonempty ι
  { rw [<-NonDetT.wp_iInf]; simp [iInf, sInf] }
  simp at h; simp [iInf_of_empty]; erw [wp_top]


lemma VeilExecM.wp_r_eq (act : VeilExecM m σ ρ α) (post : RProp α ρ σ) :
  [DemonSucc| wp act (fun a _ => post a r₀) r₀ = wp act post r₀] := by
  simp [ReaderT.wp_eq]


lemma VeilM.wp_r_eq (act : VeilM m σ ρ α) (post : RProp α ρ σ) :
  [DemonSucc| wp act (fun a _ => post a r₀) r₀ = wp act post r₀] := by
  induction act <;> simp [wp_pure, <-VeilExecM.wp_r_eq, *]


lemma TwoState.preservesInvariantsOnSuccesful_eq [Inhabited α] (act : VeilM m σ ρ α) (inv : SProp ρ σ) :
  act.toTwoState.preservesInvariantsOnSuccesful inv = act.preservesInvariantsOnSuccesful inv := by
  simp [TwoState.preservesInvariantsOnSuccesful, triple,
    VeilM.toBigStepDerived_sound,
    VeilM.toBigStepDerived, _root_.triple,
    VeilM.preservesInvariantsOnSuccesful, LE.le]; constructor
  { intro hwp r s hinv; rw [<-VeilM.wp_r_eq]
    have : inv r = ⨅ x : { s // ¬ inv r s }, (· ≠ x.val) := by {
      ext s; simp; constructor; aesop
      intro; false_or_by_contra; aesop }
    erw [this, wp_iInf]; simp; intro s' inv'
    false_or_by_contra; apply inv'; apply hwp r s s' hinv
    intro hwp; rename_i h; apply h;
    rw [<-VeilM.wp_r_eq] at hwp; simp at hwp
    open PartialCorrectness DemonicChoice ExceptionAsSuccess in
    apply wp_cons act; rotate_left; apply hwp;
    intro; simp [LE.le] }
  introv hwp  hinv hwp'
  false_or_by_contra; apply hwp';
  open PartialCorrectness DemonicChoice ExceptionAsSuccess in
  apply wp_cons act; rotate_left; apply hwp _ _ hinv
  intro _ _ _; aesop


end Deriving

#exit
/-! ### State Monad Lifting-/

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

instance [IsSubStateOf σₛ σ] : MonadStateOf σₛ (Wp m σ) where
  get := fun s post => post (getFrom s) s
  set := fun sₛ s post => post () (setIn sₛ s)
  modifyGet := fun act s post => let (ret, s') := act (getFrom s) ; post ret (setIn s' s)

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

-- only works if `σ` is `semiOutParam`
-- @[always_inline] instance IsSubStateOf_transitive [S₁ : IsSubStateOf σₛ σₘ] [S₂ : IsSubStateOf σₘ σ] : IsSubStateOf σₛ σ :=
--   IsSubStateOf.trans S₁ S₂

-- /-- This tries to transitively infer an `IsSubStateOf` instance between two states. -/
-- syntax "infer_substate" : tactic
-- macro_rules
-- | `(tactic| infer_substate) => do
--   `(tactic| (first | infer_instance | (apply IsSubStateOf.trans; rotate_left ; infer_instance ; infer_substate)))

/-- `Wp.lift act` lifts an action defined on a sub-state into an action
defined on the bigger state. -/
@[actSimp] def Wp.lift {σ σ'} [IsSubStateOf σ σ'] (act : Wp m σ ρ) : Wp m σ' ρ :=
  fun s' post => act (getFrom s') (fun r s => post r (setIn s s'))

/-- `Wp` supports lifting between different state monads. -/
instance [IsSubStateOf σ σ'] : MonadLift (Wp m σ) (Wp m σ') where
  monadLift := Wp.lift

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
@[actSimp] def Wp.spec {σ : Type} {m : Mode} {σ' ρ : Type} [IsSubStateOf σ σ'] (req : SProp σ) (ens : σ -> RProp σ ρ) : Wp m σ' ρ :=
  fun s post =>
    match m with
    | .internal => req (getFrom s) ∧ ∀ r' s', (ens (getFrom s) r' s' -> post r' (setIn s' s))
    | .external => ∀ r' s', req (getFrom s) -> ens (getFrom s) r' s' -> post r' (setIn s' s)

/-! #### Monad Instances -/

/-- `Wp` is a monad -/
instance : Monad (Wp m σ) where
  pure := Wp.pure
  bind := Wp.bind

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
@[initSimp, actSimp]
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
@[initSimp,actSimp]
def Wp.toBigStep {σ} (wp : Wp m σ ρ) : BigStep σ ρ :=
  fun s r' s' =>
    wp.toWlp s (fun r₀ s₀ => r' = r₀ ∧ s' = s₀)

/-- Same as `Wp.toBigStep`, but ignores the return value. -/
@[initSimp, actSimp]
def Wp.toTwoState {σ} (wp : Wp m σ ρ) : TwoState σ :=
  fun s s' =>
    wp.toWlp s (fun _ s₀ => (s' = s₀))

@[initSimp, actSimp]
def BigStep.toWp {σ} (act : BigStep σ ρ) : Wp .internal σ ρ :=
  fun s post => ∀ r s', act s r s' -> post r s'

/-- Transforms any two-state formula into `Wp`. Used for casting
`transition`s into `action`s. -/
@[initSimp,actSimp]
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
  simp only [implies_true, not_forall, not_imp, Decidable.not_not, true_and, eq_iff_iff]
  constructor
  {
    rintro ⟨rr, rs, liftedR, heq⟩
    simp only [heq, IsSubStateOf.setIn_getFrom_idempotent, IsSubStateOf.getFrom_setIn_idempotent, and_true]
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
  inter := by simp [pure, actSimp]
  impl  := by intros; simp_all [pure, actSimp]

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
  inter := by intros; simp_all [get, getThe,MonadStateOf.get, Wp.get]
  impl := by intros; simp_all [get, getThe,MonadStateOf.get,Wp.get]

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

-- instance : GenBigStep σ ρ (Wp.spec req ens) (BigStep.spec req ens) where
--   lawful := inferInstance
--   equiv := by unfold Wp.toBigStep BigStep.spec Wp.toWlp Wp.spec; simp

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

attribute [default_instance low] instIsSubStateOf
