import Veil.Theory.Defs


lemma VeilExecM.wp_eq (act : VeilExecM m ρ σ α) (post : RProp α ρ σ) :
  [DemonFail| wp act post = fun r s => wp (m := DivM) (act r s) (fun | .ok as => post as.1 r as.2 | .error _ => False)] ∧
  [DemonSucc| wp act post = fun r s => wp (m := DivM) (act r s) (fun | .ok as => post as.1 r as.2 | .error _ => True)] ∧
  [AngelFail| wp act post = fun r s => wp (m := DivM) (act r s) (fun | .ok as => post as.1 r as.2 | .error _ => False)] ∧
  (∀ hd, [CanRaise hd| wp act post = fun r s => wp (m := DivM) (act r s) (fun | .ok as => post as.1 r as.2 | .error e => hd e)]) := by
    simp [ReaderT.wp_eq, StateT.wp_eq, wp_tot_eq, wp_part_eq, wp_except_handler_eq, loomLogicSimp];
    (repeat' constructor) <;> congr! <;> ext <;> split <;> simp

open PartialCorrectness

lemma VeilExecM.terminates_preservesInvariants_wp (act : VeilExecM m ρ σ α) :
  [DemonFail| wp act inv'] ⊓ [DemonSucc| wp act inv] = [DemonFail| wp act (inv' ⊓ inv)] := by
    ext; simp only [VeilExecM.wp_eq, Pi.inf_apply, <-wp_and]
    congr! 1; ext (_|_) <;> simp


  lemma VeilM.terminates_preservesInvariants_wp (act : VeilM m ρ σ α) :
  [DemonFail| wp act inv₁] ⊓ [DemonSucc| wp act inv₂] = [DemonFail| wp act (inv₁ ⊓ inv₂)] := by
    unhygienic induction act <;> simp [-le_iInf_iff]
    { simp [x.terminates_preservesInvariants_wp, Pi.inf_def, *] }
    rw [← @iInf_inf_eq]; simp only [meet_himp _ _ _ _ rfl, *]

lemma VeilM.terminates_preservesInvariants (act : VeilM m ρ σ α) (inv : SProp ρ σ) :
  act.succesfullyTerminates inv ->
  act.preservesInvariantsOnSuccesful inv ->
  act.succeedsAndPreservesInvariants inv := by
  unfold VeilM.succesfullyTerminates VeilM.preservesInvariantsOnSuccesful VeilM.succeedsAndPreservesInvariants triple
  intros h₁ h₂; apply le_trans
  apply le_inf h₁ h₂; simp [VeilM.terminates_preservesInvariants_wp]

lemma VeilM.triple_sound
  (act : VeilM m ρ σ α) (inv : SProp ρ σ) (chs : act.choices) :
  act.succesfullyTerminates inv ->
  act.preservesInvariantsOnSuccesful inv ->
  (act.run chs).operationalTriple (inv ⊓ act.assumptions chs) (fun _ => inv) := by
    intros term invs
    have : [DemonFail| triple (inv ⊓ act.assumptions chs) (act.run chs) (fun _ => inv)] := by
      simp [VeilM.assumptions]
      open DemonicChoice ExceptionAsFailure in
      apply ExtractNonDet.extract_refines_triple_weak
      apply le_trans';
      { apply VeilM.terminates_preservesInvariants <;> simp [*] }
      all_goals simp
    revert this; simp [triple]
    generalize (act.run chs) = act
    introv h r hinv;
    have := h _ _ hinv; revert this
    simp [VeilExecM.operational, VeilExecM.wp_eq, DivM.wp_eq]
    cases act r s₀ <;> aesop

lemma VeilExecM.not_raises_imp_terminates_wp (act : VeilExecM m ρ σ α)
  (invEx : ExId -> RProp α ρ σ) :
  ⨅ ex, [CanRaise (· ≠ ex)| wp act (invEx ex)] <= [DemonFail| wp act (iInf invEx)] := by
  intro r s; simp [VeilExecM.wp_eq, DivM.wp_eq]
  cases (act r s) <;> aesop (add safe simp loomLogicSimp)

lemma VeilM.not_raises_imp_terminates_wp (act : VeilM m ρ σ α)
  (invEx : ExId -> RProp α ρ σ) :
  ⨅ ex, [CanRaise (· ≠ ex)| wp act (invEx ex)] <= [DemonFail| wp act (iInf invEx)] := by
  dsimp; unhygienic induction act <;> simp [-le_iInf_iff]
  { apply le_trans; apply VeilExecM.not_raises_imp_terminates_wp;
    open ExceptionAsFailure in apply wp_cons; intro y
    simp; apply f_ih }
  rw [iInf_comm]; apply iInf_mono; intro i
  by_cases h : p i <;> simp [h,f_ih]

lemma VeilM.not_raises_imp_terminates (act : VeilM m ρ σ α) (pre : SProp ρ σ) :
  (∀ ex, act.canRaise (· ≠ ex) pre) ->
  act.succesfullyTerminates pre := by
  unfold VeilM.canRaise VeilM.succesfullyTerminates triple
  simp; rw [<-le_iInf_iff (ι := ExId)]; intro h;
  have : (⊤ : RProp α ρ σ) = iInf (fun (_ : ExId) => ⊤) := by simp
  rw [this]
  solve_by_elim [VeilM.not_raises_imp_terminates_wp, le_trans']

section DerivingSemantics

variable (act : VeilM m ρ σ α)
  (genWp : (ExId -> Prop) -> VeilSpecM ρ σ α)
  (genWp_sound : ∀ hd, genWp hd <= [CanRaise hd| wp act])

include genWp_sound

lemma VeilM.succesfullyTerminates_derived (pre : SProp ρ σ) :
  (∀ ex, pre <= genWp (· ≠ ex) (fun _ => ⊤)) ->
  act.succesfullyTerminates pre := by
    intro h; apply VeilM.not_raises_imp_terminates
    solve_by_elim [le_trans]

lemma VeilM.preservesInvariantsOnSuccesful_derived (inv : SProp ρ σ) :
  (inv <= genWp (fun _ => True) (fun _ => inv)) ->
  act.preservesInvariantsOnSuccesful inv := by
    intro h; solve_by_elim [le_trans]

end DerivingSemantics
