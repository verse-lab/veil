import Veil.Theory.Defs
import Veil.Theory.Basic

lemma VeilExecM.total_imp_partial (act : VeilExecM m ρ σ α) :
  [AngelFail| wp act post] <= [DemonFail| wp act post] := by
  simp [VeilExecM.wp_eq, PartialCorrectness.DivM.wp_eq, TotalCorrectness.DivM.wp_eq]
  intro r s; cases (act r s) <;> aesop (add safe simp loomLogicSimp)


instance (act : VeilM m ρ σ α) : Nonempty act.choices := by
  unhygienic induction act <;> constructor
  { exact (ExtractNonDet.pure _) }
  { exact (ExtractNonDet.vis _ _ (fun a => f_ih a |>.some)) }
  apply ExtractNonDet.pickSuchThat;  refine ⟨fun _ => .none, by simp⟩
  exact fun t => f_ih t |>.some

noncomputable
instance (act : VeilM m ρ σ α) : Inhabited act.choices := by
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

lemma VeilExecM.wlp_eq (act : VeilExecM m ρ σ α) (post : RProp α ρ σ) :
  [AngelFail| wlp act post] = [DemonFail| wlp act post] := by
  simp [wlp, VeilExecM.wp_eq, TotalCorrectness.DivM.wp_eq, PartialCorrectness.DivM.wp_eq]
  ext r s; simp; cases (act r s) <;> simp [loomLogicSimp]

lemma VeilM.assumptions_eq (act : VeilM m ρ σ α) (ex : ExtractNonDet WeakFindable act) :
  [DemonFail| ExtractNonDet.prop act ex] = [AngelFail| ExtractNonDet.prop act ex] := by
  induction ex <;> simp [ExtractNonDet.prop, -top_le_iff, VeilExecM.wlp_eq, *]

lemma VeilM.toTwoState_sound (act : VeilM m ρ σ α) :
  act.toTwoState r₀ s₀ s₁ ->
  ∃ chs a, (act.run chs).operational r₀ s₀ s₁ (Except.ok a) := by
  intro h; specialize h r₀ s₀
  simp [VeilM.toTwoState, VeilSpecM.toTwoState] at h
  have h := act.angel_fail_imp_assumptions h
  rcases h with ⟨chs, h⟩;
  simp [VeilExecM.axiomatic] at h
  exists chs; revert h
  simp only [VeilExecM.axiomatic, VeilExecM.operational]
  rcases act.run chs r₀ s₀ with ((_|⟨a, s₁⟩)|_) <;> simp only [IsEmpty.forall_iff]
  rintro rfl; exists a

lemma VeilM.toTwoState_complete (act : VeilM m ρ σ α) (chs : act.choices) :
  (act.run chs).operational r₀ s₀ s₁ (Except.ok a) ->
  act.toTwoState r₀ s₀ s₁ := by
  intro h
  open AngelicChoice TotalCorrectness ExceptionAsFailure in
  apply ExtractNonDet.extract_refines_triple (inst := chs)
  intro r s; simp; rintro rfl rfl
  revert h; simp [triple, VeilExecM.operational, VeilM.run, NonDetT.runWeak, VeilExecM.wp_eq,
    TotalCorrectness.DivM.wp_eq]
  cases (NonDetT.extractWeak act chs r s) <;> simp [*]
  split <;> aesop

lemma VeilExecM.raises_true_imp_wp_eq_angel_fail_iwp (act : VeilExecM m ρ σ α) (post : RProp α ρ σ) :
  [CanRaise (fun _ => True)| iwp act post] = [AngelFail| wp act post] := by
  simp [iwp, VeilExecM.wp_eq, TotalCorrectness.DivM.wp_eq, PartialCorrectness.DivM.wp_eq]
  ext r s; simp; cases (act r s) <;> simp [loomLogicSimp]
  rename_i x; cases x <;> simp

lemma VeilM.raises_true_imp_wp_eq_angel_fail_iwp (act : VeilM m ρ σ α) (post : RProp α ρ σ) :
  [CanRaise (fun _ => True)| iwp act post] = [AngelFail| wp act post] := by
  unhygienic induction act <;> simp [iwp]
  { rw [<-VeilExecM.raises_true_imp_wp_eq_angel_fail_iwp]
    simp [iwp, <-f_ih, @Pi.compl_def] }
  simp [@compl_iInf, himp_eq, <-f_ih, inf_comm]

lemma VeilM.toTwoStateDerived_sound (act : VeilM m ρ σ α) :
  act.toTwoState = act.toTwoStateDerived := by
    unfold VeilM.toTwoState VeilM.toTwoStateDerived VeilSpecM.toTwoStateDerived
    simp [<-VeilM.raises_true_imp_wp_eq_angel_fail_iwp, triple, LE.le,]

lemma VeilM.toTwoStateDerived_complete (act : VeilM m ρ σ α) (chs : act.choices) :
  (act.run chs).operational r₀ s₀ s₁ (Except.ok a) ->
  act.toTwoStateDerived r₀ s₀ s₁ := by
  intro h
  rw [← VeilM.toTwoStateDerived_sound]
  apply VeilM.toTwoState_complete act chs h

open PartialCorrectness DemonicChoice ExceptionAsSuccess in
lemma VeilM.wp_iInf {ι : Type} (act : VeilM m ρ σ α) (post : ι -> RProp α ρ σ) :
  wp act (fun a r s => iInf (fun i => post i a r s)) = ⨅ i, wp act (post i) := by
  by_cases h: Nonempty ι
  { rw [<-NonDetT.wp_iInf]; simp [iInf, sInf] }
  simp at h; simp [iInf_of_empty]; erw [wp_top]

lemma VeilExecM.wp_r_eq (act : VeilExecM m ρ σ α) (post : RProp α ρ σ) :
  [DemonSucc| wp act (fun a _ => post a r₀) r₀ = wp act post r₀] := by
  simp [ReaderT.wp_eq]

lemma VeilM.wp_r_eq (act : VeilM m ρ σ α) (post : RProp α ρ σ) :
  [DemonSucc| wp act (fun a _ => post a r₀) r₀ = wp act post r₀] := by
  induction act <;> simp [wp_pure, <-VeilExecM.wp_r_eq, *]

lemma TwoState.meetsSpecificationIfSuccessful_eq [Inhabited α] (act : VeilM m ρ σ α) (pre post : SProp ρ σ) :
  act.toTwoState.meetsSpecificationIfSuccessful pre post = act.meetsSpecificationIfSuccessful pre (fun _ => post) := by
  simp [TwoState.meetsSpecificationIfSuccessful, VeilM.meetsSpecificationIfSuccessful,
    VeilM.toTwoStateDerived_sound, VeilM.toTwoStateDerived, VeilSpecM.toTwoStateDerived,
    triple, _root_.triple, LE.le, _root_.triple]
  constructor
  { intro hwp r s hinv; rw [<-VeilM.wp_r_eq]
    have : post r = ⨅ x : { s // ¬ post r s }, (· ≠ x.val) := by {
      ext s; simp; constructor; aesop
      intro; false_or_by_contra; aesop }
    erw [this, VeilM.wp_iInf]; simp; intro s' inv'
    false_or_by_contra; apply inv'; apply hwp r s s' hinv
    intro hwp; rename_i h; apply h;
    rw [<-VeilM.wp_r_eq] at hwp; simp at hwp
    open PartialCorrectness DemonicChoice ExceptionAsSuccess in
    apply wp_cons act; rotate_left; apply hwp;
    intro; simp [LE.le] }
  introv hwp hpre hwp'
  false_or_by_contra; apply hwp';
  open PartialCorrectness DemonicChoice ExceptionAsSuccess in
  apply wp_cons act; rotate_left; apply hwp _ _ hpre
  intro _ _ _; aesop

lemma TwoState.preservesInvariantsOnSuccesful_eq [Inhabited α] (act : VeilM m ρ σ α) (inv : SProp ρ σ) :
  act.toTwoState.preservesInvariantsIfSuccesful inv = act.preservesInvariantsIfSuccesful inv := by
  apply TwoState.meetsSpecificationIfSuccessful_eq

section DerivingSemantics

variable (act : VeilM m ρ σ α)
  (genWp : (ExId -> Prop) -> VeilSpecM ρ σ α)
  (genWp_sound : ∀ hd, genWp hd <= [CanRaise hd| wp act])

include genWp_sound

lemma TwoState.preservesInvariantsOnSuccesful_derived (inv : SProp ρ σ) :
  (genWp (fun _ => True) |>.toTwoStateDerived.triple inv inv) ->
  act.toTwoState.preservesInvariantsIfSuccesful inv := by
    intro h
    rw [VeilM.toTwoStateDerived_sound]
    simp [TwoState.preservesInvariantsIfSuccesful,
      triple, VeilM.toTwoStateDerived, VeilSpecM.toTwoStateDerived, _root_.triple, LE.le]
    intro r₀ s₀ s₁ hinv hwp; have h := h r₀ s₀ s₁ hinv
    solve_by_elim


end DerivingSemantics
