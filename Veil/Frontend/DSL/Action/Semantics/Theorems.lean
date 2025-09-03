import Veil.Frontend.DSL.Action.Semantics.Definitions

namespace Veil

lemma VeilExecM.wp_eq (act : VeilExecM m ρ σ α) (post : RProp α ρ σ) :
  [DemonFail| wp act post = fun r s => wp (m := DivM) (act r s) (fun | .ok as => post as.1 r as.2 | .error _ => False)] ∧
  [DemonSucc| wp act post = fun r s => wp (m := DivM) (act r s) (fun | .ok as => post as.1 r as.2 | .error _ => True)] ∧
  [AngelFail| wp act post = fun r s => wp (m := DivM) (act r s) (fun | .ok as => post as.1 r as.2 | .error _ => False)] ∧
  (∀ hd, [IgnoreEx hd| wp act post = fun r s => wp (m := DivM) (act r s) (fun | .ok as => post as.1 r as.2 | .error e => hd e)]) := by
    simp [ReaderT.wp_eq, StateT.wp_eq, wp_tot_eq, wp_part_eq, wp_except_handler_eq, loomLogicSimp];
    (repeat' constructor) <;> congr! <;> ext <;> split <;> simp

lemma VeilExecM.wlp_eq (act : VeilExecM m ρ σ α) (post : RProp α ρ σ) :
  [AngelFail| wlp act post] = [DemonFail| wlp act post] := by
  simp [wlp, VeilExecM.wp_eq, TotalCorrectness.DivM.wp_eq, PartialCorrectness.DivM.wp_eq]
  ext r s; simp; cases (act r s) <;> simp [loomLogicSimp]

lemma VeilExecM.total_imp_partial (act : VeilExecM m ρ σ α) :
  [AngelFail| wp act post] <= [DemonFail| wp act post] := by
  simp [VeilExecM.wp_eq, PartialCorrectness.DivM.wp_eq, TotalCorrectness.DivM.wp_eq]
  intro r s; cases (act r s) <;> aesop (add safe simp loomLogicSimp)

lemma VeilM.assumptions_eq (act : VeilM m ρ σ α) (ex : ExtractNonDet WeakFindable act) :
  [DemonFail| ExtractNonDet.prop act ex] = [AngelFail| ExtractNonDet.prop act ex] := by
  induction ex <;> simp [ExtractNonDet.prop, -top_le_iff, VeilExecM.wlp_eq, *]

lemma VeilExecM.raises_true_imp_wp_eq_angel_fail_iwp (act : VeilExecM m ρ σ α) (post : RProp α ρ σ) :
  [IgnoreEx (fun _ => True)| iwp act post] = [AngelFail| wp act post] := by
  simp [iwp, VeilExecM.wp_eq, TotalCorrectness.DivM.wp_eq, PartialCorrectness.DivM.wp_eq]
  ext r s; simp; cases (act r s) <;> simp [loomLogicSimp]
  rename_i x; cases x <;> simp

lemma VeilM.raises_true_imp_wp_eq_angel_fail_iwp (act : VeilM m ρ σ α) (post : RProp α ρ σ) :
  [IgnoreEx (fun _ => True)| iwp act post] = [AngelFail| wp act post] := by
  unhygienic induction act <;> simp [iwp]
  { rw [←VeilExecM.raises_true_imp_wp_eq_angel_fail_iwp]
    simp [iwp, ←f_ih, @Pi.compl_def] }
  simp [@compl_iInf, himp_eq, ←f_ih, inf_comm]

open PartialCorrectness DemonicChoice ExceptionAsSuccess in
lemma VeilM.wp_iInf {ι : Type} (act : VeilM m ρ σ α) (post : ι -> RProp α ρ σ) :
  wp act (fun a r s => iInf (fun i => post i a r s)) = ⨅ i, wp act (post i) := by
  by_cases h: Nonempty ι
  { rw [←NonDetT.wp_iInf]; simp [iInf, sInf] }
  simp at h; simp [iInf_of_empty]; erw [wp_top]

lemma VeilExecM.wp_r_eq (act : VeilExecM m ρ σ α) (post : RProp α ρ σ) :
  [DemonSucc| wp act (fun a _ => post a r₀) r₀ = wp act post r₀] := by
  simp [ReaderT.wp_eq]

lemma VeilM.wp_r_eq (act : VeilM m ρ σ α) (post : RProp α ρ σ) :
  [DemonSucc| wp act (fun a _ => post a r₀) r₀ = wp act post r₀] := by
  induction act <;> simp [wp_pure, ←VeilExecM.wp_r_eq, *]

section PartialCorrectnessTheorems
open PartialCorrectness

lemma VeilExecM.terminates_preservesInvariants_wp (act : VeilExecM m ρ σ α) :
  [DemonFail| wp act inv'] ⊓ [DemonSucc| wp act inv] = [DemonFail| wp act (inv' ⊓ inv)] := by
    ext; simp only [VeilExecM.wp_eq, Pi.inf_apply, ←wp_and]
    congr! 1; ext (_|_) <;> simp

lemma VeilM.terminates_preservesInvariants_wp (act : VeilM m ρ σ α) :
  [DemonFail| wp act inv₁] ⊓ [DemonSucc| wp act inv₂] = [DemonFail| wp act (inv₁ ⊓ inv₂)] := by
    unhygienic induction act <;> simp [-le_iInf_iff]
    { simp [x.terminates_preservesInvariants_wp, Pi.inf_def, *] }
    rw [← @iInf_inf_eq]; simp only [meet_himp _ _ _ _ rfl, *]

lemma VeilM.terminates_preservesInvariants (act : VeilM m ρ σ α) (inv : SProp ρ σ) :
  act.doesNotThrow inv ->
  act.preservesInvariantsIfSuccesful inv ->
  act.succeedsAndPreservesInvariants inv := by
  unfold VeilM.doesNotThrow VeilM.preservesInvariantsIfSuccesful VeilM.succeedsAndPreservesInvariants
    VeilM.succeedsAndMeetsSpecification VeilM.meetsSpecificationIfSuccessful triple
  intros h₁ h₂; apply le_trans
  apply le_inf h₁ h₂; simp [VeilM.terminates_preservesInvariants_wp]

lemma VeilM.triple_sound
  (act : VeilM m ρ σ α) (inv : SProp ρ σ) (chs : act.choices) :
  act.doesNotThrow inv ->
  act.preservesInvariantsIfSuccesful inv ->
  (act.run chs).operationalTriple inv (fun _ => inv) := by
    intros term invs
    have : [DemonFail| triple inv (act.run chs) (fun _ => inv)] := by
      open DemonicChoice ExceptionAsFailure in
      apply ExtractNonDet.extract_refines_triple_weak;
      apply VeilM.terminates_preservesInvariants <;> simp [*]
    revert this; simp [triple]
    generalize (act.run chs) = act
    introv h r hinv;
    have := h _ _ hinv; revert this
    simp [VeilExecM.operational, VeilExecM.wp_eq, DivM.wp_eq]
    cases act r s₀ <;> aesop

lemma VeilExecM.not_raises_imp_terminates_wp (act : VeilExecM m ρ σ α)
  (invEx : ExId -> RProp α ρ σ) :
  ⨅ ex, [IgnoreEx (· ≠ ex)| wp act (invEx ex)] <= [DemonFail| wp act (iInf invEx)] := by
  intro r s; simp [VeilExecM.wp_eq, DivM.wp_eq]
  cases (act r s) <;> aesop (add safe simp loomLogicSimp)

lemma VeilM.not_raises_imp_terminates_wp (act : VeilM m ρ σ α)
  (invEx : ExId -> RProp α ρ σ) :
  ⨅ ex, [IgnoreEx (· ≠ ex)| wp act (invEx ex)] <= [DemonFail| wp act (iInf invEx)] := by
  dsimp; unhygienic induction act <;> simp [-le_iInf_iff]
  { apply le_trans; apply VeilExecM.not_raises_imp_terminates_wp;
    open ExceptionAsFailure in apply wp_cons; intro y
    simp; apply f_ih }
  rw [iInf_comm]; apply iInf_mono; intro i
  by_cases h : p i <;> simp [h,f_ih]

lemma VeilM.not_raises_imp_terminates (act : VeilM m ρ σ α) (pre : SProp ρ σ) :
  (∀ ex, act.succeedsWhenIgnoring (· ≠ ex) pre) ->
  act.doesNotThrow pre := by
  unfold VeilM.succeedsWhenIgnoring VeilM.doesNotThrow triple
  simp; rw [←le_iInf_iff (ι := ExId)]; intro h;
  have : (⊤ : RProp α ρ σ) = iInf (fun (_ : ExId) => ⊤) := by simp
  rw [this]
  solve_by_elim [VeilM.not_raises_imp_terminates_wp, le_trans']

end PartialCorrectnessTheorems

section DerivingSemanticsTheorems
variable (act : VeilM m ρ σ α)
  (genWp : (ExId -> Prop) -> VeilSpecM ρ σ α)
  (genWp_sound : ∀ hd, genWp hd <= [IgnoreEx hd| wp act])

include genWp_sound

lemma VeilM.succesfullyTerminates_derived (pre : SProp ρ σ) :
  (∀ ex, pre <= genWp (· ≠ ex) (fun _ => ⊤)) ->
  act.doesNotThrow pre := by
    intro h; apply VeilM.not_raises_imp_terminates
    solve_by_elim [le_trans]

lemma VeilM.preservesInvariantsOnSuccesful_derived (inv : SProp ρ σ) :
  (inv <= genWp (fun _ => True) (fun _ => inv)) ->
  act.preservesInvariantsIfSuccesful inv := by
    intro h; solve_by_elim [le_trans]

end DerivingSemanticsTheorems

section TransitionSemanticsTheorems

instance (act : VeilM m ρ σ α) : Nonempty act.choices := by
  unhygienic induction act <;> constructor
  { exact (ExtractNonDet.pure _) }
  { exact (ExtractNonDet.vis _ _ (fun a => f_ih a |>.some)) }
  apply ExtractNonDet.pickSuchThat;  refine ⟨fun _ => .none, by simp⟩
  exact fun t => f_ih t |>.some

noncomputable instance (act : VeilM m ρ σ α) : Inhabited act.choices := by
  exact Classical.inhabited_of_nonempty'

open Classical in
lemma VeilM.angel_fail_imp_assumptions (act : VeilM m ρ σ α) :
  [AngelFail| wp act post r s] <= ∃ chs, (act.run chs).axiomatic r s post := by
  unhygienic induction act generalizing r s <;> simp [ExtractNonDet.prop, -top_le_iff]
  { intro; exists (ExtractNonDet.pure _); }
  { open TotalCorrectness ExceptionAsFailure in
    rw [ReaderT.wp_eq]; simp [StateT.wp_eq, wp_tot_eq, wp_part_eq, DivM.wp_eq]
    split; simp; split; <;> (try simp); intro h
    rename_i bs _
    specialize f_ih _ h; rcases f_ih with ⟨ex, h⟩
    exists (ExtractNonDet.vis _ _ (fun b => if h : b = bs.1 then by rw [h]; exact ex else default))
    simp [ExtractNonDet.prop];
    simp [VeilExecM.axiomatic, VeilM.run, NonDetT.runWeak, NonDetT.extractWeak,
      bind, ReaderT.bind, StateT.bind, StateT.map, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    simp [*]; apply h }
  simp [loomLogicSimp]; intros x px h
  specialize f_ih _ h; rcases f_ih with ⟨ex, h⟩
  exists (@ExtractNonDet.pickSuchThat _ _ _ _ _ _ ?_ ?_)
  { refine ⟨fun _ => .some x, by simp [*]⟩ }
  { exact fun b => if h : b = x then by rw [h]; exact ex else default }
  simp [ExtractNonDet.prop, VeilExecM.axiomatic, VeilM.run, NonDetT.runWeak, NonDetT.extractWeak]
  apply h

lemma VeilM.toTransition_sound (act : VeilM m ρ σ α) :
  act.toTransition r₀ s₀ s₁ ->
  ∃ chs a, (act.run chs).operational r₀ s₀ s₁ (Except.ok a) := by
  intro h; specialize h r₀ s₀
  simp [VeilM.toTransition, VeilSpecM.toTransition] at h
  have h := act.angel_fail_imp_assumptions h
  rcases h with ⟨chs, h⟩;
  simp [VeilExecM.axiomatic] at h
  exists chs; revert h
  simp only [VeilExecM.axiomatic, VeilExecM.operational]
  rcases act.run chs r₀ s₀ with ((_|⟨a, s₁⟩)|_) <;> simp only [IsEmpty.forall_iff]
  rintro rfl; exists a

lemma VeilM.toTransition_complete (act : VeilM m ρ σ α) (chs : act.choices) :
  (act.run chs).operational r₀ s₀ s₁ (Except.ok a) ->
  act.toTransition r₀ s₀ s₁ := by
  intro h
  open AngelicChoice TotalCorrectness ExceptionAsFailure in
  apply ExtractNonDet.extract_refines_triple (inst := chs)
  intro r s; simp; rintro rfl rfl
  revert h; simp [triple, VeilExecM.operational, VeilM.run, NonDetT.runWeak, VeilExecM.wp_eq,
    TotalCorrectness.DivM.wp_eq]
  cases (NonDetT.extractWeak act chs r s) <;> simp [*]
  split <;> aesop

lemma VeilM.toTransitionDerived_sound (act : VeilM m ρ σ α) :
  act.toTransition = act.toTransitionDerived := by
    unfold VeilM.toTransition VeilM.toTransitionDerived VeilSpecM.toTransitionDerived
    simp [←VeilM.raises_true_imp_wp_eq_angel_fail_iwp, triple, LE.le,]

lemma VeilM.toTransitionDerived_complete (act : VeilM m ρ σ α) (chs : act.choices) :
  (act.run chs).operational r₀ s₀ s₁ (Except.ok a) ->
  act.toTransitionDerived r₀ s₀ s₁ := by
  intro h
  rw [← VeilM.toTransitionDerived_sound]
  apply VeilM.toTransition_complete act chs h

lemma Transition.meetsSpecificationIfSuccessful_eq [Inhabited α] (act : VeilM m ρ σ α) (pre post : SProp ρ σ) :
  act.toTransition.meetsSpecificationIfSuccessful pre post = act.meetsSpecificationIfSuccessful pre (fun _ => post) := by
  simp [Transition.meetsSpecificationIfSuccessful, VeilM.meetsSpecificationIfSuccessful,
    VeilM.toTransitionDerived_sound, VeilM.toTransitionDerived, VeilSpecM.toTransitionDerived,
    triple, _root_.triple, LE.le, _root_.triple]
  constructor
  { intro hwp r s hinv; rw [← VeilM.wp_r_eq]
    have : post r = ⨅ x : { s // ¬ post r s }, (· ≠ x.val) := by {
      ext s; simp; constructor; aesop
      intro; false_or_by_contra; aesop }
    erw [this, VeilM.wp_iInf]; simp; intro s' inv'
    false_or_by_contra; apply inv'; apply hwp r s s' hinv
    intro hwp; rename_i h; apply h;
    rw [← VeilM.wp_r_eq] at hwp; simp at hwp
    open PartialCorrectness DemonicChoice ExceptionAsSuccess in
    apply wp_cons act; rotate_left; apply hwp;
    intro; simp [LE.le] }
  introv hwp hpre hwp'
  false_or_by_contra; apply hwp';
  open PartialCorrectness DemonicChoice ExceptionAsSuccess in
  apply wp_cons act; rotate_left; apply hwp _ _ hpre
  intro _ _ _; aesop

lemma Transition.preservesInvariantsOnSuccesful_eq [Inhabited α] (act : VeilM m ρ σ α) (inv : SProp ρ σ) :
  act.toTransition.preservesInvariantsIfSuccesful inv = act.preservesInvariantsIfSuccesful inv := by
  apply Transition.meetsSpecificationIfSuccessful_eq

end TransitionSemanticsTheorems

section VCTheorems
/-! # Theorems for relating VCs -/

lemma VeilM.meetsSpecificationIfSuccessful_preserves_assumptions (act : VeilM m ρ σ α) (assu : ρ → Prop) (inv inv' : SProp ρ σ) :
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
    VeilM.succeedsAndMeetsSpecification VeilM.meetsSpecificationIfSuccessful triple
  intros h₁ h₂; apply le_trans
  apply le_inf h₁ h₂; simp [VeilM.terminates_preservesInvariants_wp]

lemma VeilM.succeeds_decompose' (act : VeilM m ρ σ α)
  (assu : ρ → Prop) (inv : SProp ρ σ) :
  (∀ ex, act.succeedsWhenIgnoring (· ≠ ex) (fun rd st => assu rd ∧ inv rd st)) →
  act.preservesInvariantsIfSuccessfulAssuming assu inv →
  act.succeedsAndPreservesInvariantsAssuming assu inv := by
  intro hterm hpres; apply VeilM.not_raises_imp_terminates at hterm
  apply VeilM.doesNotThrow_preservesInvariantsAssuming _ _ _ hterm hpres

end VCTheorems

end Veil
