import Veil.Frontend.DSL.Action.Semantics.Definitions
import Veil.Frontend.DSL.Action.Extract

open Loom.Order
open scoped Loom.Order

namespace Veil

private theorem pi_compl_def {α β : Type} [Loom.Order.BooleanAlgebra β] (f : α → β) :
    compl f = fun a => compl (f a) := rfl
private theorem pi_inf_def {α β : Type} [Loom.Order.Lattice β] (f g : α → β) :
    (f ⊓ₗ g) = fun a => f a ⊓ₗ g a := rfl

theorem VeilExecM.wp_eq (act : VeilExecM m ρ σ α) (post : RProp α ρ σ) :
  [DemonFail| wp act post = fun r s => wp (m := DivM) (act r s) (fun | (.ok a, s) => post a r s | (.error _, _) => False)] ∧
  [DemonSucc| wp act post = fun r s => wp (m := DivM) (act r s) (fun | (.ok a, s) => post a r s | (.error _, _) => True)] ∧
  [AngelFail| wp act post = fun r s => wp (m := DivM) (act r s) (fun | (.ok a, s) => post a r s | (.error _, _) => False)] ∧
  (∀ hd, [IgnoreEx hd| wp act post = fun r s => wp (m := DivM) (act r s) (fun | (.ok a, s) => post a r s | (.error e, _) => hd e)]) := by
    simp only [ReaderT.wp_eq, StateT.wp_eq, wp_tot_eq, wp_part_eq, wp_except_handler_eq, loomLogicSimp]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (try intro)
    all_goals funext r s; congr 1; funext ⟨ea, s'⟩; cases ea <;> rfl

theorem VeilExecM.wlp_eq (act : VeilExecM m ρ σ α) (post : RProp α ρ σ) :
  [AngelFail| wlp act post] = [DemonFail| wlp act post] := by
  simp [wlp, VeilExecM.wp_eq, TotalCorrectness.DivM.wp_eq, PartialCorrectness.DivM.wp_eq]
  ext r s; simp; cases (act r s) <;> simp [loomLogicSimp]

theorem VeilExecM.total_imp_partial (act : VeilExecM m ρ σ α) :
  [AngelFail| wp act post] ⊑ₗ [DemonFail| wp act post] := by
  simp [VeilExecM.wp_eq, PartialCorrectness.DivM.wp_eq, TotalCorrectness.DivM.wp_eq]
  intro r s; cases (act r s) <;> aesop (add safe simp loomLogicSimp)

-- theorem VeilM.assumptions_eq (act : VeilM m ρ σ α) (ex : ExtractNonDet WeakFindable act) :
--   [DemonFail| ExtractNonDet.prop act ex] = [AngelFail| ExtractNonDet.prop act ex] := by
--   induction ex <;> simp [ExtractNonDet.prop, -top_le_iff, VeilExecM.wlp_eq, *]

theorem VeilExecM.raises_true_imp_wp_eq_angel_fail_iwp (act : VeilExecM m ρ σ α) (post : RProp α ρ σ) :
  [IgnoreEx (fun _ => True)| iwp act post] = [AngelFail| wp act post] := by
  simp [Id, iwp, VeilExecM.wp_eq, TotalCorrectness.DivM.wp_eq, PartialCorrectness.DivM.wp_eq]
  ext r s; simp; cases (act r s) <;> simp [loomLogicSimp]
  rename_i x; rcases x with ⟨_ | _, _⟩ <;> simp

theorem VeilM.raises_true_imp_wp_eq_angel_fail_iwp (act : VeilM m ρ σ α) (post : RProp α ρ σ) :
  [IgnoreEx (fun _ => True)| iwp act post] = [AngelFail| wp act post] := by
  unhygienic induction act <;> simp [iwp]
  { rw [←VeilExecM.raises_true_imp_wp_eq_angel_fail_iwp]
    simp [iwp, ←f_ih, pi_compl_def] }
  simp [@compl_iInf, himp_eq, ←f_ih]

open PartialCorrectness DemonicChoice ExceptionAsSuccess in
theorem VeilM.wp_iInf {ι : Type} (act : VeilM m ρ σ α) (post : ι -> RProp α ρ σ) :
  wp act (iInf post) = iInf (fun i => wp act (post i)) := by
  classical
  by_cases h : Nonempty ι
  · letI := h
    exact NonDetT.wp_iInf act post
  · have empty : ι → False := fun i => h ⟨i⟩
    rw [iInf_of_empty empty post, iInf_of_empty empty]
    exact wp_top act

theorem VeilExecM.wp_r_eq (act : VeilExecM m ρ σ α) (post : RProp α ρ σ) :
  [DemonSucc| wp act (fun a _ => post a r₀) r₀ = wp act post r₀] := by
  simp [ReaderT.wp_eq]

theorem VeilM.wp_r_eq (act : VeilM m ρ σ α) (post : RProp α ρ σ) :
  [DemonSucc| wp act (fun a _ => post a r₀) r₀ = wp act post r₀] := by
  induction act <;> simp [←VeilExecM.wp_r_eq, *]

section PartialCorrectnessTheorems
open PartialCorrectness

theorem VeilExecM.terminates_preservesInvariants_wp (act : VeilExecM m ρ σ α) :
  [DemonFail| wp act inv'] ⊓ₗ [DemonSucc| wp act inv] = [DemonFail| wp act (inv' ⊓ₗ inv)] := by
    funext r s
    simp only [VeilExecM.wp_eq, pi_inf_apply, ←wp_and]
    congr 1
    funext x
    rcases x with ⟨(_ | a), s'⟩ <;> simp

theorem VeilM.terminates_preservesInvariants_wp (act : VeilM m ρ σ α) :
  [DemonFail| wp act inv₁] ⊓ₗ [DemonSucc| wp act inv₂] = [DemonFail| wp act (inv₁ ⊓ₗ inv₂)] := by
    unhygienic induction act <;> simp [-le_iInf_iff]
    { simp [x.terminates_preservesInvariants_wp, pi_inf_def, *] }
    funext r s
    simp only [pi_inf_apply, prop_inf, pi_iInf_apply, prop_iInf,
      pi_himp_apply, prop_himp, pureE, purePropE]
    have ih : ∀ a, ([DemonFail| wp (f a) inv₁ r s] ∧ [DemonSucc| wp (f a) inv₂ r s]) ↔
        [DemonFail| wp (f a) (inv₁ ⊓ₗ inv₂) r s] := by
      intro a; exact Iff.of_eq (congrFun (congrFun (f_ih a) r) s)
    apply propext
    constructor
    · rintro ⟨h1, h2⟩ a ha
      exact (ih a).mp ⟨h1 a ha, h2 a ha⟩
    · intro h
      exact ⟨fun a ha => ((ih a).mpr (h a ha)).1, fun a ha => ((ih a).mpr (h a ha)).2⟩

theorem VeilM.terminates_preservesInvariants (act : VeilM m ρ σ α) (inv : SProp ρ σ) :
  act.doesNotThrow inv ->
  act.preservesInvariantsIfSuccesful inv ->
  act.succeedsAndPreservesInvariants inv := by
  unfold VeilM.doesNotThrow VeilM.preservesInvariantsIfSuccesful VeilM.succeedsAndPreservesInvariants
    VeilM.succeedsAndMeetsSpecification VeilM.meetsSpecificationIfSuccessful triple
  intros h₁ h₂; apply le_trans
  apply le_inf h₁ h₂; simp [VeilM.terminates_preservesInvariants_wp]

-- theorem VeilM.triple_sound
--   (act : VeilM m ρ σ α) (inv : SProp ρ σ) (chs : act.choices) :
--   act.doesNotThrow inv ->
--   act.preservesInvariantsIfSuccesful inv ->
--   (act.run chs).operationalTriple inv (fun _ => inv) := by
--     intros term invs
--     have : [DemonFail| triple inv (act.run chs) (fun _ => inv)] := by
--       open DemonicChoice ExceptionAsFailure in
--       apply ExtractNonDet.extract_refines_triple_weak;
--       apply VeilM.terminates_preservesInvariants <;> simp [*]
--     revert this; simp [triple]
--     generalize (act.run chs) = act
--     introv h r hinv;
--     have := h _ _ hinv; revert this
--     simp [VeilExecM.operational, VeilExecM.wp_eq, DivM.wp_eq]
--     cases act r s₀ <;> aesop

theorem VeilExecM.not_raises_imp_terminates_wp (act : VeilExecM m ρ σ α)
  (invEx : ExId -> RProp α ρ σ) :
  ⨅ₗ ex, [IgnoreEx (· ≠ ex)| wp act (invEx ex)] ⊑ₗ [DemonFail| wp act (iInf invEx)] := by
  intro r s; simp [VeilExecM.wp_eq, DivM.wp_eq]
  cases (act r s) <;> aesop (add safe simp loomLogicSimp)

theorem VeilM.not_raises_imp_terminates_wp (act : VeilM m ρ σ α)
  (invEx : ExId -> RProp α ρ σ) :
  ⨅ₗ ex, [IgnoreEx (· ≠ ex)| wp act (invEx ex)] ⊑ₗ [DemonFail| wp act (iInf invEx)] := by
  dsimp; unhygienic induction act <;> simp [-le_iInf_iff]
  { apply le_trans; apply VeilExecM.not_raises_imp_terminates_wp;
    open ExceptionAsFailure in apply wp_cons; intro y
    simp; apply f_ih }
  rw [iInf_comm]; apply iInf_mono; intro i
  by_cases h : p i <;> simp [h,f_ih]

theorem VeilM.not_raises_imp_terminates (act : VeilM m ρ σ α) (pre : SProp ρ σ) :
  (∀ ex, act.succeedsWhenIgnoring (· ≠ ex) pre) ->
  act.doesNotThrow pre := by
  unfold VeilM.succeedsWhenIgnoring VeilM.doesNotThrow triple
  simp; rw [←le_iInf_iff (ι := ExId)]; intro h;
  have : (⊤ₗ : RProp α ρ σ) = iInf (fun (_ : ExId) => ⊤ₗ) := by simp
  rw [this]
  solve_by_elim [VeilM.not_raises_imp_terminates_wp, le_trans']

end PartialCorrectnessTheorems

section DerivingSemanticsTheorems
variable (act : VeilM m ρ σ α)
  (genWp : (ExId -> Prop) -> VeilSpecM ρ σ α)
  (genWp_sound : ∀ hd, genWp hd ⊑ₗ [IgnoreEx hd| wp act])

include genWp_sound

theorem VeilM.succesfullyTerminates_derived (pre : SProp ρ σ) :
  (∀ ex, pre ⊑ₗ genWp (· ≠ ex) (fun _ => ⊤ₗ)) ->
  act.doesNotThrow pre := by
    intro h; apply VeilM.not_raises_imp_terminates
    solve_by_elim [le_trans]

theorem VeilM.preservesInvariantsOnSuccesful_derived (inv : SProp ρ σ) :
  (inv ⊑ₗ genWp (fun _ => True) (fun _ => inv)) ->
  act.preservesInvariantsIfSuccesful inv := by
    intro h; solve_by_elim [le_trans]

end DerivingSemanticsTheorems

section TransitionSemanticsTheorems

-- instance (act : VeilM m ρ σ α) : Nonempty act.choices := by
--   unhygienic induction act <;> constructor
--   { exact (ExtractNonDet.pure _) }
--   { exact (ExtractNonDet.vis _ _ (fun a => f_ih a |>.some)) }
--   apply ExtractNonDet.pickSuchThat;  refine ⟨fun _ => .none, by simp⟩
--   exact fun t => f_ih t |>.some

-- noncomputable instance (act : VeilM m ρ σ α) : Inhabited act.choices := by
--   exact Classical.inhabited_of_nonempty'

-- open Classical in
-- theorem VeilM.angel_fail_imp_assumptions (act : VeilM m ρ σ α) :
--   [AngelFail| wp act post r s] ⊑ₗ ∃ chs, (act.run chs).axiomatic r s post := by
--   unhygienic induction act generalizing r s <;> simp [-top_le_iff]
--   { intro; exists (ExtractNonDet.pure _); }
--   { open TotalCorrectness ExceptionAsFailure in
--     rw [ReaderT.wp_eq]; simp only [StateT.wp_eq, wp_tot_eq, DivM.wp_eq]
--     split; simp
--     rename_i bs heq
--     rcases bs with ⟨(_ | b), s'⟩ <;> simp; intro h
--     specialize f_ih _ h; rcases f_ih with ⟨ex, h⟩
--     exists (ExtractNonDet.vis _ _ (fun b' => if hb : b' = b then by rw [hb]; exact ex else default))
--     simp only [eq_mpr_eq_cast]
--     simp only [VeilExecM.axiomatic, run, NonDetT.runWeak, NonDetT.extractWeak, NonDetT.extractGen,
--       bind, ReaderT.bind, StateT.bind, ExceptT.bind, ExceptT.mk, monadLift_self, ExceptT.bindCont]
--     simp [*]; apply h }
--   simp [loomLogicSimp]; intros x px h
--   specialize f_ih _ h; rcases f_ih with ⟨ex, h⟩
--   exists (@ExtractNonDet.pickSuchThat _ _ _ _ _ _ ?_ ?_)
--   { refine ⟨fun _ => .some x, by simp [*]⟩ }
--   { exact fun b => if h : b = x then by rw [h]; exact ex else default }
--   simp only [VeilExecM.axiomatic, run, NonDetT.runWeak, NonDetT.extractWeak, NonDetT.extractGen,
--     ↓reduceDIte, eq_mpr_eq_cast, cast_eq]
--   apply h

-- theorem VeilM.toTransition_sound (act : VeilM m ρ σ α) :
--   act.toTransition r₀ s₀ s₁ ->
--   ∃ chs a, (act.run chs).operational r₀ s₀ s₁ (Except.ok a) := by
--   intro h; specialize h r₀ s₀
--   simp only [and_self, le_Prop_eq, forall_const] at h
--   have h := act.angel_fail_imp_assumptions h
--   rcases h with ⟨chs, h⟩;
--   simp [VeilExecM.axiomatic] at h
--   exists chs; revert h
--   simp only [VeilExecM.operational]
--   rcases act.run chs r₀ s₀ with ((⟨_|a, s⟩)|_) <;> simp only [IsEmpty.forall_iff]
--   rintro rfl; exists a

-- theorem VeilM.toTransition_complete (act : VeilM m ρ σ α) (chs : act.choices) :
--   (act.run chs).operational r₀ s₀ s₁ (Except.ok a) ->
--   act.toTransition r₀ s₀ s₁ := by
--   intro h
--   open AngelicChoice TotalCorrectness ExceptionAsFailure in
--   apply ExtractNonDet.extract_refines_triple (inst := chs)
--   intro r s; simp; rintro rfl rfl
--   revert h; simp only [VeilExecM.operational, run, NonDetT.runWeak, reduceCtorEq, false_and,
--     Except.ok.injEq, VeilExecM.wp_eq, true_and, DivM.wp_eq]
--   cases (NonDetT.extractWeak act chs r s) <;> simp [*]
--   split <;> aesop

theorem VeilM.toTransitionDerived_sound (act : VeilM m ρ σ α) :
  act.toTransition = act.toTransitionDerived := by
    unfold VeilM.toTransition VeilM.toTransitionDerived VeilSpecM.toTransitionDerived
    simp [←VeilM.raises_true_imp_wp_eq_angel_fail_iwp, triple, Loom.Order.LE.le,]

-- theorem VeilM.toTransitionDerived_complete (act : VeilM m ρ σ α) (chs : act.choices) :
--   (act.run chs).operational r₀ s₀ s₁ (Except.ok a) ->
--   act.toTransitionDerived r₀ s₀ s₁ := by
--   intro h
--   rw [← VeilM.toTransitionDerived_sound]
--   apply VeilM.toTransition_complete act chs h

theorem Transition.meetsSpecificationIfSuccessful_eq [Inhabited α] (act : VeilM m ρ σ α) (pre post : SProp ρ σ) :
  act.toTransition.meetsSpecificationIfSuccessful pre post = act.meetsSpecificationIfSuccessful pre (fun _ => post) := by
  simp [Transition.meetsSpecificationIfSuccessful, VeilM.meetsSpecificationIfSuccessful,
    VeilM.toTransitionDerived_sound, VeilM.toTransitionDerived, VeilSpecM.toTransitionDerived,
    triple, _root_.triple, Loom.Order.LE.le, _root_.triple]
  constructor
  { intro hwp r s hinv; rw [← VeilM.wp_r_eq]
    have : post r = ⨅ₗ x : { s // ¬ post r s }, (· ≠ x.val) := by {
      ext s; simp; constructor; aesop
      intro; false_or_by_contra; aesop }
    rw [this]
    have hpost : (fun (_ : α) (_ : ρ) => iInf (fun x : {s // ¬post r s} => (fun s => s ≠ x.val))) =
        iInf (fun (x : {s // ¬post r s}) (_ : α) (_ : ρ) s => s ≠ x.val) := by
      funext a r' s'; simp
    rw [hpost, VeilM.wp_iInf]; simp; intro s' inv'
    false_or_by_contra; apply inv'; apply hwp r s s' hinv
    intro hwp; rename_i h; apply h;
    rw [← VeilM.wp_r_eq] at hwp; simp at hwp
    open PartialCorrectness DemonicChoice ExceptionAsSuccess in
    apply wp_cons act; rotate_left; apply hwp;
    intro; simp [Loom.Order.LE.le] }
  introv hwp hpre hwp'
  false_or_by_contra; apply hwp';
  open PartialCorrectness DemonicChoice ExceptionAsSuccess in
  apply wp_cons act; rotate_left; apply hwp _ _ hpre
  intro _ _ _; aesop

theorem Transition.preservesInvariantsOnSuccesful_eq [Inhabited α] (act : VeilM m ρ σ α) (inv : SProp ρ σ) :
  act.toTransition.preservesInvariantsIfSuccesful inv = act.preservesInvariantsIfSuccesful inv := by
  apply Transition.meetsSpecificationIfSuccessful_eq

end TransitionSemanticsTheorems

section VCTheorems
/-! # Theorems for relating VCs -/

theorem VeilM.meetsSpecificationIfSuccessful_preserves_assumptions (act : VeilM m ρ σ α) (assu : ρ → Prop) (inv inv' : SProp ρ σ) :
  act.meetsSpecificationIfSuccessful (fun rd st => assu rd ∧ inv rd st) (fun _ => inv') ↔
  act.meetsSpecificationIfSuccessful (fun rd st => assu rd ∧ inv rd st) (fun _ rd st => assu rd ∧ inv' rd st) := by
  constructor <;> (
    unfold VeilM.meetsSpecificationIfSuccessful triple;
    intro h rd₀ st ; specialize h rd₀ st ; dsimp at h ⊢;
    intro h' ; specialize h h' ; rcases h' with ⟨h1, h2⟩;
    rw [← VeilM.wp_r_eq] at h ⊢;
    have hq : assu rd₀ = True := by simp_all)
  · rw [hq] ; simp ; assumption
  · open PartialCorrectness DemonicChoice ExceptionAsSuccess in
    apply wp_cons act (fun a x st => assu rd₀ ∧ inv' rd₀ st)
    · intro _ _ _ ⟨hassu, hinv⟩; assumption
    · assumption

theorem VeilM.doesNotThrow_preservesInvariantsAssuming (act : VeilM m ρ σ α) (assu : ρ → Prop) (inv : SProp ρ σ) :
  act.doesNotThrowAssuming assu inv ->
  act.preservesInvariantsIfSuccessfulAssuming assu inv ->
  act.succeedsAndPreservesInvariantsAssuming assu inv := by
  unfold VeilM.doesNotThrowAssuming VeilM.preservesInvariantsIfSuccessfulAssuming VeilM.succeedsAndPreservesInvariantsAssuming
    VeilM.succeedsAndMeetsSpecification VeilM.meetsSpecificationIfSuccessfulAssuming triple
  intros h₁ h₂; apply le_trans
  apply le_inf h₁ h₂; simp [VeilM.terminates_preservesInvariants_wp]

theorem VeilM.succeeds_decompose' (act : VeilM m ρ σ α)
  (assu : ρ → Prop) (inv : SProp ρ σ) :
  (∀ ex, act.succeedsWhenIgnoring (· ≠ ex) (fun rd st => assu rd ∧ inv rd st)) →
  act.preservesInvariantsIfSuccessfulAssuming assu inv →
  act.succeedsAndPreservesInvariantsAssuming assu inv := by
  intro hterm hpres; replace hterm := VeilM.not_raises_imp_terminates act _ hterm
  apply VeilM.doesNotThrow_preservesInvariantsAssuming _ _ _ hterm hpres

open PartialCorrectness DemonicChoice ExceptionAsSuccess in
theorem triple_weaken_postcondition (act : VeilM m ρ σ α) (pre post post' : SProp ρ σ) :
  triple pre act (fun _ => post) →
  post ⊑ₗ post' →
  triple pre act (fun _ => post') := by
  intro htriple hpost
  apply triple_cons act (le_refl pre) (fun _ => hpost) htriple

end VCTheorems

section ExecutableNonDeterministicSemanticsTheorems
open MultiExtractor

open AngelicChoice TotalCorrectness in
instance
  {hd : ε → Prop}
  [IsHandler hd]
  : LawfulMonadPersistentLog κ (VeilMultiExecM κ ε ρ σ) (ρ → σ → Prop) where
  log_sound := by
    introv ; ext r st
    simp +instances +unfoldPartialApp [Id, wp, liftM, monadLift, MAlg.lift, Functor.map,
      MAlgOrdered.μ, OfHd, MAlgExcept, pointwiseSup,
      ExceptT.map, ExceptT.mk, Except.getD, TsilTCore.op,
      StateT.map, StateT.pure, StateT.bind,
      MonadPersistentLog.log, MonadLift.monadLift, StateT.lift, ExceptT.lift, PeDivM.log,
      PeDivM.prepend, pure, bind, Loom.Order.embed]

open AngelicChoice TotalCorrectness in
theorem VeilM.extract_list_eq_wp (s : VeilM m ρ σ α)
  (h : ExtractConstraint κ
    (VeilExecM m ρ σ)
    (VeilMultiExecM κ ExId ρ σ) (fun p (ec : ExtCandidates Candidates κ p) => ec.core.find) s s')
  (hd : Int → Prop) [IsHandler hd] :
  wp s post = wp s' post := by
  apply MultiExtractor.AngelicChoice.extract_list_eq_wp κ ; assumption

-- a state is in the extraction result iff it is a possible next state
theorem important1
  (act : VeilM m ρ σ α)
  (h : ExtractConstraint κ
    (VeilExecM m ρ σ)
    (VeilMultiExecM κ ExId ρ σ) (fun p (ec : ExtCandidates Candidates κ p) => ec.core.find) act s') :
  letI res := s' r₀ s₀
  (∃ a log, (log, DivM.res (Except.ok a, s₁)) ∈ res) ↔
  act.toTransition r₀ s₀ s₁ := by
  unfold VeilM.toTransition triple
  -- TODO this is a mess. needs to be cleaned up
  rw [VeilM.extract_list_eq_wp act h]
  simp [Loom.Order.LE.le]
  simp [ReaderT.wp_eq, StateT.wp_eq, AngelicChoice.TsilT.wp_eq, wp_except_handler_eq, PeDivM.wp_eq_DivM, TotalCorrectness.DivM.wp_eq]
  simp [pointwiseSup]
  constructor
  · rintro ⟨a, log, h⟩ --r s hrs
    exists _ , h
  · rintro ⟨a, hin, h⟩
    rcases a with ⟨k, ⟨e | a, ps⟩ | _⟩ <;> simp at h
    subst_eqs ; exists a , k

-- an exception is in the extraction result iff it can be raised
theorem important2
  (e : ExId)
  (act : VeilM m ρ σ α)
  (h : ExtractConstraint κ
    (VeilExecM m ρ σ)
    (VeilMultiExecM κ ExId ρ σ) (fun p (ec : ExtCandidates Candidates κ p) => ec.core.find) act s') :
  let _ : IsHandler (· = e) := ⟨⟩
  letI res := s' r₀ s₀
  letI tmp := (open AngelicChoice TotalCorrectness in
    wp act ⊥ₗ r₀ s₀)
  (∃ log ps, (log, DivM.res (Except.error e, ps)) ∈ res) ↔ tmp := by
  intro hd
  rw [VeilM.extract_list_eq_wp act h]
  simp [ReaderT.wp_eq, StateT.wp_eq, AngelicChoice.TsilT.wp_eq, wp_except_handler_eq, PeDivM.wp_eq_DivM, TotalCorrectness.DivM.wp_eq]
  simp [pointwiseSup]
  constructor
  · rintro ⟨log, ps, h⟩ --r s hrs
    exists _ , h ; simp
  · rintro ⟨a, hin, h⟩
    rcases a with ⟨k, ⟨e | a, ps⟩ | _⟩ <;> simp [Loom.Order.embed] at h
    split at h <;> simp at h
    subst_eqs ; exists k , ps

end ExecutableNonDeterministicSemanticsTheorems

end Veil
