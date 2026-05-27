-- skip eval
import Veil
import Examples.Rabia.Rabia

-- adapted from [weak_mvc.v](https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/coq/weak_mvc.v)

inductive state_value where
  | v0 | v1 | vquestion
deriving DecidableEq, Nonempty

instance : Inhabited state_value := ⟨state_value.vquestion⟩

instance : ThreeValuedType state_value where
  v0 := state_value.v0
  v1 := state_value.v1
  vquestion := state_value.vquestion
  ax1 := by simp
  ax2 := by simp
  ax3 := by simp
  ax4 := by
    intro x
    cases x <;> simp

instance : TotalOrderWithMinimum Nat where
  le := Nat.le
  le_refl := by simp
  le_trans := by
    simp
    omega
  le_antisymm := by
    simp
    omega
  le_total := by
    simp
    omega

  lt := Nat.lt
  le_lt := by
    simp
    omega

  next x y := y = x + 1
  next_def := by
    simp
    intro x y
    apply Iff.intro
    · intro
      subst_vars
      apply And.intro <;> omega
    · intro ⟨h1, h2⟩
      specialize h2 (x + 1) (by omega)
      omega

  zero := 0
  zero_lt := by simp

veil module Rabia


end Rabia

set_option maxHeartbeats 8000000

namespace Veil.RelationalTransitionSystem

def isInvariant {ρ σ l : Type} (sys : RelationalTransitionSystem ρ σ l) (p : σ → Prop) : Prop :=
  ∀ th st, sys.reachable th st → p st

end Veil.RelationalTransitionSystem

namespace Rabia

@[reducible] noncomputable local instance classicalDecidableEq (α : Type) : DecidableEq α :=
  Classical.decEq α

@[reducible] noncomputable local instance classicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {node : Type} [node_ne : Inhabited node]
  {set_majority : Type} [set_majority_ne : Inhabited set_majority]
  {set_f_plus_1 : Type} [set_f_plus_1_ne : Inhabited set_f_plus_1]
  [bg : Background node set_majority set_f_plus_1]
  {proposal_value : Type} [proposal_value_ne : Inhabited proposal_value]

abbrev phase := Nat

abbrev Theory' node set_majority set_f_plus_1 proposal_value :=
  Theory node set_majority set_f_plus_1 phase proposal_value state_value

abbrev Field' node set_majority set_f_plus_1 proposal_value :=
  FieldAbstractType node set_majority set_f_plus_1 phase proposal_value state_value

abbrev State' node set_majority set_f_plus_1 proposal_value :=
  State (Field' node set_majority set_f_plus_1 proposal_value)

abbrev Label' node set_majority set_f_plus_1 proposal_value :=
  Label node set_majority set_f_plus_1 phase proposal_value state_value

-- Same fields as `relationalTransitionSystem`, instantiated with the local
-- reducible classical instances so generated TR theorems line up by reduction.
noncomputable abbrev System' :
    Veil.RelationalTransitionSystem
      (Theory' node set_majority set_f_plus_1 proposal_value)
      (State' node set_majority set_f_plus_1 proposal_value)
      (Label' node set_majority set_f_plus_1 proposal_value) where
  assumptions :=
    Assumptions (Theory' node set_majority set_f_plus_1 proposal_value)
      node set_majority set_f_plus_1 phase proposal_value state_value
  init :=
    Init (Theory' node set_majority set_f_plus_1 proposal_value)
      (State' node set_majority set_f_plus_1 proposal_value)
      node set_majority set_f_plus_1 phase proposal_value state_value
      (Field' node set_majority set_f_plus_1 proposal_value)
  tr :=
    Next (Theory' node set_majority set_f_plus_1 proposal_value)
      (State' node set_majority set_f_plus_1 proposal_value)
      node set_majority set_f_plus_1 phase proposal_value state_value
      (Field' node set_majority set_f_plus_1 proposal_value)

def ConcreteInv
    (inv :
      Theory' node set_majority set_f_plus_1 proposal_value →
        State' node set_majority set_f_plus_1 proposal_value → Prop) :
    State' node set_majority set_f_plus_1 proposal_value → Prop :=
  fun st => inv {} st

def ConcreteInvariants :
    State' node set_majority set_f_plus_1 proposal_value → Prop :=
  ConcreteInv (fun th st =>
    Invariants
      (Theory' node set_majority set_f_plus_1 proposal_value)
      (State' node set_majority set_f_plus_1 proposal_value)
      node set_majority set_f_plus_1 phase proposal_value state_value
      (Field' node set_majority set_f_plus_1 proposal_value)
      th st)

abbrev InitializerTr (s : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  initializer.ext.tr
    (Theory' node set_majority set_f_plus_1 proposal_value)
    (State' node set_majority set_f_plus_1 proposal_value)
    node set_majority set_f_plus_1 phase proposal_value state_value
    (Field' node set_majority set_f_plus_1 proposal_value) {} default s

abbrev InitialProposalTr
    (s s' : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  initial_proposal.ext.tr
    (Theory' node set_majority set_f_plus_1 proposal_value)
    (State' node set_majority set_f_plus_1 proposal_value)
    node set_majority set_f_plus_1 phase proposal_value state_value
    (Field' node set_majority set_f_plus_1 proposal_value) {} s s'

abbrev DecideFullValTr
    (s s' : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  decide_bc_decide_full_val.ext.tr
    (Theory' node set_majority set_f_plus_1 proposal_value)
    (State' node set_majority set_f_plus_1 proposal_value)
    node set_majority set_f_plus_1 phase proposal_value state_value
    (Field' node set_majority set_f_plus_1 proposal_value) {} s s'

abbrev DecideFullNoValTr
    (s s' : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  decide_bc_decide_full_noval.ext.tr
    (Theory' node set_majority set_f_plus_1 proposal_value)
    (State' node set_majority set_f_plus_1 proposal_value)
    node set_majority set_f_plus_1 phase proposal_value state_value
    (Field' node set_majority set_f_plus_1 proposal_value) {} s s'

abbrev InitialVote1Tr
    (s s' : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  initial_vote1.ext.tr
    (Theory' node set_majority set_f_plus_1 proposal_value)
    (State' node set_majority set_f_plus_1 proposal_value)
    node set_majority set_f_plus_1 phase proposal_value state_value
    (Field' node set_majority set_f_plus_1 proposal_value) {} s s'

abbrev PhaseRnd1Tr
    (s s' : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  phase_rnd1.ext.tr
    (Theory' node set_majority set_f_plus_1 proposal_value)
    (State' node set_majority set_f_plus_1 proposal_value)
    node set_majority set_f_plus_1 phase proposal_value state_value
    (Field' node set_majority set_f_plus_1 proposal_value) {} s s'

abbrev PhaseRnd2Tr
    (s s' : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  phase_rnd2.ext.tr
    (Theory' node set_majority set_f_plus_1 proposal_value)
    (State' node set_majority set_f_plus_1 proposal_value)
    node set_majority set_f_plus_1 phase proposal_value state_value
    (Field' node set_majority set_f_plus_1 proposal_value) {} s s'

private theorem invariants_initial
    {s : State' node set_majority set_f_plus_1 proposal_value}
    (htr : InitializerTr (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s) :
    ConcreteInvariants (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s := by
  dsimp [InitializerTr] at htr
  dsimp [ConcreteInvariants, ConcreteInv, Invariants]
  repeat' constructor
  all_goals solve_by_elim [
    Rabia.initializer_decision_bc_same_round_agree_tr,
    Rabia.initializer_decision_bc_started_tr,
    Rabia.initializer_decision_bc_vote_rnd1_tr,
    Rabia.initializer_decision_full_noval_inv_tr,
    Rabia.initializer_decision_full_val_agree_tr,
    Rabia.initializer_decision_full_val_inv_tr,
    Rabia.initializer_decision_full_val_validity_tr,
    Rabia.initializer_good_succ_good_tr,
    Rabia.initializer_good_zero_tr,
    Rabia.initializer_inv_0_tr,
    Rabia.initializer_inv_10_tr,
    Rabia.initializer_inv_11_tr,
    Rabia.initializer_inv_12_tr,
    Rabia.initializer_inv_13_tr,
    Rabia.initializer_inv_14_tr,
    Rabia.initializer_inv_15_tr,
    Rabia.initializer_inv_16_tr,
    Rabia.initializer_inv_17_tr,
    Rabia.initializer_inv_18_tr,
    Rabia.initializer_inv_19_tr,
    Rabia.initializer_inv_20_tr,
    Rabia.initializer_inv_21_tr,
    Rabia.initializer_inv_22_tr,
    Rabia.initializer_inv_23_tr,
    Rabia.initializer_inv_24_tr,
    Rabia.initializer_inv_25_tr,
    Rabia.initializer_inv_26_tr,
    Rabia.initializer_inv_27_tr,
    Rabia.initializer_inv_28_tr,
    Rabia.initializer_inv_2_tr,
    Rabia.initializer_inv_30_tr,
    Rabia.initializer_inv_31_tr,
    Rabia.initializer_inv_32_tr,
    Rabia.initializer_inv_33_tr,
    Rabia.initializer_inv_34_tr,
    Rabia.initializer_inv_35_tr,
    Rabia.initializer_inv_36_tr,
    Rabia.initializer_inv_37_tr,
    Rabia.initializer_inv_39_tr,
    Rabia.initializer_inv_41_tr,
    Rabia.initializer_inv_6_tr,
    Rabia.initializer_inv_7_tr,
    Rabia.initializer_inv_8_tr,
    Rabia.initializer_inv_9_tr,
    Rabia.initializer_started_pred_tr,
    Rabia.initializer_vl_decision_bc_agree_tr,
    Rabia.initializer_vote_rnd1_pred_rnd_tr,
    Rabia.initializer_vote_rnd2_vote_rnd1_tr]

private theorem invariants_initial_proposal
    {s s' : State' node set_majority set_f_plus_1 proposal_value}
    (hinv : ConcreteInvariants (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s)
    (htr : InitialProposalTr (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s s') :
    ConcreteInvariants (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s' := by
  have hinv' : Invariants
      (Theory' node set_majority set_f_plus_1 proposal_value)
      (State' node set_majority set_f_plus_1 proposal_value)
      node set_majority set_f_plus_1 phase proposal_value state_value
      (Field' node set_majority set_f_plus_1 proposal_value) {} s := hinv
  dsimp [InitialProposalTr] at htr
  dsimp [ConcreteInvariants, ConcreteInv, Invariants]
  repeat' constructor
  all_goals solve_by_elim [
    Rabia.initial_proposal_decision_bc_same_round_agree_tr,
    Rabia.initial_proposal_decision_bc_started_tr,
    Rabia.initial_proposal_decision_bc_vote_rnd1_tr,
    Rabia.initial_proposal_decision_full_noval_inv_tr,
    Rabia.initial_proposal_decision_full_val_agree_tr,
    Rabia.initial_proposal_decision_full_val_inv_tr,
    Rabia.initial_proposal_decision_full_val_validity_tr,
    Rabia.initial_proposal_good_succ_good_tr,
    Rabia.initial_proposal_good_zero_tr,
    Rabia.initial_proposal_inv_0_tr,
    Rabia.initial_proposal_inv_10_tr,
    Rabia.initial_proposal_inv_11_tr,
    Rabia.initial_proposal_inv_12_tr,
    Rabia.initial_proposal_inv_13_tr,
    Rabia.initial_proposal_inv_14_tr,
    Rabia.initial_proposal_inv_15_tr,
    Rabia.initial_proposal_inv_16_tr,
    Rabia.initial_proposal_inv_17_tr,
    Rabia.initial_proposal_inv_18_tr,
    Rabia.initial_proposal_inv_19_tr,
    Rabia.initial_proposal_inv_20_tr,
    Rabia.initial_proposal_inv_21_tr,
    Rabia.initial_proposal_inv_22_tr,
    Rabia.initial_proposal_inv_23_tr,
    Rabia.initial_proposal_inv_24_tr,
    Rabia.initial_proposal_inv_25_tr,
    Rabia.initial_proposal_inv_26_tr,
    Rabia.initial_proposal_inv_27_tr,
    Rabia.initial_proposal_inv_28_tr,
    Rabia.initial_proposal_inv_2_tr,
    Rabia.initial_proposal_inv_30_tr,
    Rabia.initial_proposal_inv_31_tr,
    Rabia.initial_proposal_inv_32_tr,
    Rabia.initial_proposal_inv_33_tr,
    Rabia.initial_proposal_inv_34_tr,
    Rabia.initial_proposal_inv_35_tr,
    Rabia.initial_proposal_inv_36_tr,
    Rabia.initial_proposal_inv_37_tr,
    Rabia.initial_proposal_inv_39_tr,
    Rabia.initial_proposal_inv_41_tr,
    Rabia.initial_proposal_inv_6_tr,
    Rabia.initial_proposal_inv_7_tr,
    Rabia.initial_proposal_inv_8_tr,
    Rabia.initial_proposal_inv_9_tr,
    Rabia.initial_proposal_started_pred_tr,
    Rabia.initial_proposal_vl_decision_bc_agree_tr,
    Rabia.initial_proposal_vote_rnd1_pred_rnd_tr,
    Rabia.initial_proposal_vote_rnd2_vote_rnd1_tr]

private theorem invariants_decide_full_val
    {s s' : State' node set_majority set_f_plus_1 proposal_value}
    (hinv : ConcreteInvariants (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s)
    (htr : DecideFullValTr (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s s') :
    ConcreteInvariants (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s' := by
  have hinv' : Invariants
      (Theory' node set_majority set_f_plus_1 proposal_value)
      (State' node set_majority set_f_plus_1 proposal_value)
      node set_majority set_f_plus_1 phase proposal_value state_value
      (Field' node set_majority set_f_plus_1 proposal_value) {} s := hinv
  dsimp [DecideFullValTr] at htr
  dsimp [ConcreteInvariants, ConcreteInv, Invariants]
  repeat' constructor
  all_goals solve_by_elim [
    Rabia.decide_bc_decide_full_val_decision_bc_same_round_agree_tr,
    Rabia.decide_bc_decide_full_val_decision_bc_started_tr,
    Rabia.decide_bc_decide_full_val_decision_bc_vote_rnd1_tr,
    Rabia.decide_bc_decide_full_val_decision_full_noval_inv_tr,
    Rabia.decide_bc_decide_full_val_decision_full_val_agree_tr,
    Rabia.decide_bc_decide_full_val_decision_full_val_inv_tr,
    Rabia.decide_bc_decide_full_val_decision_full_val_validity_tr,
    Rabia.decide_bc_decide_full_val_good_succ_good_tr,
    Rabia.decide_bc_decide_full_val_good_zero_tr,
    Rabia.decide_bc_decide_full_val_inv_0_tr,
    Rabia.decide_bc_decide_full_val_inv_10_tr,
    Rabia.decide_bc_decide_full_val_inv_11_tr,
    Rabia.decide_bc_decide_full_val_inv_12_tr,
    Rabia.decide_bc_decide_full_val_inv_13_tr,
    Rabia.decide_bc_decide_full_val_inv_14_tr,
    Rabia.decide_bc_decide_full_val_inv_15_tr,
    Rabia.decide_bc_decide_full_val_inv_16_tr,
    Rabia.decide_bc_decide_full_val_inv_17_tr,
    Rabia.decide_bc_decide_full_val_inv_18_tr,
    Rabia.decide_bc_decide_full_val_inv_19_tr,
    Rabia.decide_bc_decide_full_val_inv_20_tr,
    Rabia.decide_bc_decide_full_val_inv_21_tr,
    Rabia.decide_bc_decide_full_val_inv_22_tr,
    Rabia.decide_bc_decide_full_val_inv_23_tr,
    Rabia.decide_bc_decide_full_val_inv_24_tr,
    Rabia.decide_bc_decide_full_val_inv_25_tr,
    Rabia.decide_bc_decide_full_val_inv_26_tr,
    Rabia.decide_bc_decide_full_val_inv_27_tr,
    Rabia.decide_bc_decide_full_val_inv_28_tr,
    Rabia.decide_bc_decide_full_val_inv_2_tr,
    Rabia.decide_bc_decide_full_val_inv_30_tr,
    Rabia.decide_bc_decide_full_val_inv_31_tr,
    Rabia.decide_bc_decide_full_val_inv_32_tr,
    Rabia.decide_bc_decide_full_val_inv_33_tr,
    Rabia.decide_bc_decide_full_val_inv_34_tr,
    Rabia.decide_bc_decide_full_val_inv_35_tr,
    Rabia.decide_bc_decide_full_val_inv_36_tr,
    Rabia.decide_bc_decide_full_val_inv_37_tr,
    Rabia.decide_bc_decide_full_val_inv_39_tr,
    Rabia.decide_bc_decide_full_val_inv_41_tr,
    Rabia.decide_bc_decide_full_val_inv_6_tr,
    Rabia.decide_bc_decide_full_val_inv_7_tr,
    Rabia.decide_bc_decide_full_val_inv_8_tr,
    Rabia.decide_bc_decide_full_val_inv_9_tr,
    Rabia.decide_bc_decide_full_val_started_pred_tr,
    Rabia.decide_bc_decide_full_val_vl_decision_bc_agree_tr,
    Rabia.decide_bc_decide_full_val_vote_rnd1_pred_rnd_tr,
    Rabia.decide_bc_decide_full_val_vote_rnd2_vote_rnd1_tr]

private theorem invariants_decide_full_noval
    {s s' : State' node set_majority set_f_plus_1 proposal_value}
    (hinv : ConcreteInvariants (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s)
    (htr : DecideFullNoValTr (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s s') :
    ConcreteInvariants (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s' := by
  have hinv' : Invariants
      (Theory' node set_majority set_f_plus_1 proposal_value)
      (State' node set_majority set_f_plus_1 proposal_value)
      node set_majority set_f_plus_1 phase proposal_value state_value
      (Field' node set_majority set_f_plus_1 proposal_value) {} s := hinv
  dsimp [DecideFullNoValTr] at htr
  dsimp [ConcreteInvariants, ConcreteInv, Invariants]
  repeat' constructor
  all_goals solve_by_elim [
    Rabia.decide_bc_decide_full_noval_decision_bc_same_round_agree_tr,
    Rabia.decide_bc_decide_full_noval_decision_bc_started_tr,
    Rabia.decide_bc_decide_full_noval_decision_bc_vote_rnd1_tr,
    Rabia.decide_bc_decide_full_noval_decision_full_noval_inv_tr,
    Rabia.decide_bc_decide_full_noval_decision_full_val_agree_tr,
    Rabia.decide_bc_decide_full_noval_decision_full_val_inv_tr,
    Rabia.decide_bc_decide_full_noval_decision_full_val_validity_tr,
    Rabia.decide_bc_decide_full_noval_good_succ_good_tr,
    Rabia.decide_bc_decide_full_noval_good_zero_tr,
    Rabia.decide_bc_decide_full_noval_inv_0_tr,
    Rabia.decide_bc_decide_full_noval_inv_10_tr,
    Rabia.decide_bc_decide_full_noval_inv_11_tr,
    Rabia.decide_bc_decide_full_noval_inv_12_tr,
    Rabia.decide_bc_decide_full_noval_inv_13_tr,
    Rabia.decide_bc_decide_full_noval_inv_14_tr,
    Rabia.decide_bc_decide_full_noval_inv_15_tr,
    Rabia.decide_bc_decide_full_noval_inv_16_tr,
    Rabia.decide_bc_decide_full_noval_inv_17_tr,
    Rabia.decide_bc_decide_full_noval_inv_18_tr,
    Rabia.decide_bc_decide_full_noval_inv_19_tr,
    Rabia.decide_bc_decide_full_noval_inv_20_tr,
    Rabia.decide_bc_decide_full_noval_inv_21_tr,
    Rabia.decide_bc_decide_full_noval_inv_22_tr,
    Rabia.decide_bc_decide_full_noval_inv_23_tr,
    Rabia.decide_bc_decide_full_noval_inv_24_tr,
    Rabia.decide_bc_decide_full_noval_inv_25_tr,
    Rabia.decide_bc_decide_full_noval_inv_26_tr,
    Rabia.decide_bc_decide_full_noval_inv_27_tr,
    Rabia.decide_bc_decide_full_noval_inv_28_tr,
    Rabia.decide_bc_decide_full_noval_inv_2_tr,
    Rabia.decide_bc_decide_full_noval_inv_30_tr,
    Rabia.decide_bc_decide_full_noval_inv_31_tr,
    Rabia.decide_bc_decide_full_noval_inv_32_tr,
    Rabia.decide_bc_decide_full_noval_inv_33_tr,
    Rabia.decide_bc_decide_full_noval_inv_34_tr,
    Rabia.decide_bc_decide_full_noval_inv_35_tr,
    Rabia.decide_bc_decide_full_noval_inv_36_tr,
    Rabia.decide_bc_decide_full_noval_inv_37_tr,
    Rabia.decide_bc_decide_full_noval_inv_39_tr,
    Rabia.decide_bc_decide_full_noval_inv_41_tr,
    Rabia.decide_bc_decide_full_noval_inv_6_tr,
    Rabia.decide_bc_decide_full_noval_inv_7_tr,
    Rabia.decide_bc_decide_full_noval_inv_8_tr,
    Rabia.decide_bc_decide_full_noval_inv_9_tr,
    Rabia.decide_bc_decide_full_noval_started_pred_tr,
    Rabia.decide_bc_decide_full_noval_vl_decision_bc_agree_tr,
    Rabia.decide_bc_decide_full_noval_vote_rnd1_pred_rnd_tr,
    Rabia.decide_bc_decide_full_noval_vote_rnd2_vote_rnd1_tr]

private theorem invariants_initial_vote1
    {s s' : State' node set_majority set_f_plus_1 proposal_value}
    (hinv : ConcreteInvariants (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s)
    (htr : InitialVote1Tr (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s s') :
    ConcreteInvariants (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s' := by
  have hinv' : Invariants
      (Theory' node set_majority set_f_plus_1 proposal_value)
      (State' node set_majority set_f_plus_1 proposal_value)
      node set_majority set_f_plus_1 phase proposal_value state_value
      (Field' node set_majority set_f_plus_1 proposal_value) {} s := hinv
  dsimp [InitialVote1Tr] at htr
  dsimp [ConcreteInvariants, ConcreteInv, Invariants]
  repeat' constructor
  all_goals solve_by_elim [
    Rabia.initial_vote1_decision_bc_same_round_agree_tr,
    Rabia.initial_vote1_decision_bc_started_tr,
    Rabia.initial_vote1_decision_bc_vote_rnd1_tr,
    Rabia.initial_vote1_decision_full_noval_inv_tr,
    Rabia.initial_vote1_decision_full_val_agree_tr,
    Rabia.initial_vote1_decision_full_val_inv_tr,
    Rabia.initial_vote1_decision_full_val_validity_tr,
    Rabia.initial_vote1_good_succ_good_tr,
    Rabia.initial_vote1_good_zero_tr,
    Rabia.initial_vote1_inv_0_tr,
    Rabia.initial_vote1_inv_10_tr,
    Rabia.initial_vote1_inv_11_tr,
    Rabia.initial_vote1_inv_12_tr,
    Rabia.initial_vote1_inv_13_tr,
    Rabia.initial_vote1_inv_14_tr,
    Rabia.initial_vote1_inv_15_tr,
    Rabia.initial_vote1_inv_16_tr,
    Rabia.initial_vote1_inv_17_tr,
    Rabia.initial_vote1_inv_18_tr,
    Rabia.initial_vote1_inv_19_tr,
    Rabia.initial_vote1_inv_20_tr,
    Rabia.initial_vote1_inv_21_tr,
    Rabia.initial_vote1_inv_22_tr,
    Rabia.initial_vote1_inv_23_tr,
    Rabia.initial_vote1_inv_24_tr,
    Rabia.initial_vote1_inv_25_tr,
    Rabia.initial_vote1_inv_26_tr,
    Rabia.initial_vote1_inv_27_tr,
    Rabia.initial_vote1_inv_28_tr,
    Rabia.initial_vote1_inv_2_tr,
    Rabia.initial_vote1_inv_30_tr,
    Rabia.initial_vote1_inv_31_tr,
    Rabia.initial_vote1_inv_32_tr,
    Rabia.initial_vote1_inv_33_tr,
    Rabia.initial_vote1_inv_34_tr,
    Rabia.initial_vote1_inv_35_tr,
    Rabia.initial_vote1_inv_36_tr,
    Rabia.initial_vote1_inv_37_tr,
    Rabia.initial_vote1_inv_39_tr,
    Rabia.initial_vote1_inv_41_tr,
    Rabia.initial_vote1_inv_6_tr,
    Rabia.initial_vote1_inv_7_tr,
    Rabia.initial_vote1_inv_8_tr,
    Rabia.initial_vote1_inv_9_tr,
    Rabia.initial_vote1_started_pred_tr,
    Rabia.initial_vote1_vl_decision_bc_agree_tr,
    Rabia.initial_vote1_vote_rnd1_pred_rnd_tr,
    Rabia.initial_vote1_vote_rnd2_vote_rnd1_tr]

private theorem invariants_phase_rnd1
    {s s' : State' node set_majority set_f_plus_1 proposal_value}
    (hinv : ConcreteInvariants (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s)
    (htr : PhaseRnd1Tr (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s s') :
    ConcreteInvariants (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s' := by
  have hinv' : Invariants
      (Theory' node set_majority set_f_plus_1 proposal_value)
      (State' node set_majority set_f_plus_1 proposal_value)
      node set_majority set_f_plus_1 phase proposal_value state_value
      (Field' node set_majority set_f_plus_1 proposal_value) {} s := hinv
  dsimp [PhaseRnd1Tr] at htr
  dsimp [ConcreteInvariants, ConcreteInv, Invariants]
  repeat' constructor
  all_goals solve_by_elim [
    Rabia.phase_rnd1_decision_bc_same_round_agree_tr,
    Rabia.phase_rnd1_decision_bc_started_tr,
    Rabia.phase_rnd1_decision_bc_vote_rnd1_tr,
    Rabia.phase_rnd1_decision_full_noval_inv_tr,
    Rabia.phase_rnd1_decision_full_val_agree_tr,
    Rabia.phase_rnd1_decision_full_val_inv_tr,
    Rabia.phase_rnd1_decision_full_val_validity_tr,
    Rabia.phase_rnd1_good_succ_good_tr,
    Rabia.phase_rnd1_good_zero_tr,
    Rabia.phase_rnd1_inv_0_tr,
    Rabia.phase_rnd1_inv_10_tr,
    Rabia.phase_rnd1_inv_11_tr,
    Rabia.phase_rnd1_inv_12_tr,
    Rabia.phase_rnd1_inv_13_tr,
    Rabia.phase_rnd1_inv_14_tr,
    Rabia.phase_rnd1_inv_15_tr,
    Rabia.phase_rnd1_inv_16_tr,
    Rabia.phase_rnd1_inv_17_tr,
    Rabia.phase_rnd1_inv_18_tr,
    Rabia.phase_rnd1_inv_19_tr,
    Rabia.phase_rnd1_inv_20_tr,
    Rabia.phase_rnd1_inv_21_tr,
    Rabia.phase_rnd1_inv_22_tr,
    Rabia.phase_rnd1_inv_23_tr,
    Rabia.phase_rnd1_inv_24_tr,
    Rabia.phase_rnd1_inv_25_tr,
    Rabia.phase_rnd1_inv_26_tr,
    Rabia.phase_rnd1_inv_27_tr,
    Rabia.phase_rnd1_inv_28_tr,
    Rabia.phase_rnd1_inv_2_tr,
    Rabia.phase_rnd1_inv_30_tr,
    Rabia.phase_rnd1_inv_31_tr,
    Rabia.phase_rnd1_inv_32_tr,
    Rabia.phase_rnd1_inv_33_tr,
    Rabia.phase_rnd1_inv_34_tr,
    Rabia.phase_rnd1_inv_35_tr,
    Rabia.phase_rnd1_inv_36_tr,
    Rabia.phase_rnd1_inv_37_tr,
    Rabia.phase_rnd1_inv_39_tr,
    Rabia.phase_rnd1_inv_41_tr,
    Rabia.phase_rnd1_inv_6_tr,
    Rabia.phase_rnd1_inv_7_tr,
    Rabia.phase_rnd1_inv_8_tr,
    Rabia.phase_rnd1_inv_9_tr,
    Rabia.phase_rnd1_started_pred_tr,
    Rabia.phase_rnd1_vl_decision_bc_agree_tr,
    Rabia.phase_rnd1_vote_rnd1_pred_rnd_tr,
    Rabia.phase_rnd1_vote_rnd2_vote_rnd1_tr]

private theorem invariants_phase_rnd2
    {s s' : State' node set_majority set_f_plus_1 proposal_value}
    (hinv : ConcreteInvariants (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s)
    (htr : PhaseRnd2Tr (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s s') :
    ConcreteInvariants (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) s' := by
  have hinv' : Invariants
      (Theory' node set_majority set_f_plus_1 proposal_value)
      (State' node set_majority set_f_plus_1 proposal_value)
      node set_majority set_f_plus_1 phase proposal_value state_value
      (Field' node set_majority set_f_plus_1 proposal_value) {} s := hinv
  dsimp [PhaseRnd2Tr] at htr
  dsimp [ConcreteInvariants, ConcreteInv, Invariants]
  repeat' constructor
  all_goals solve_by_elim [
    Rabia.phase_rnd2_decision_bc_same_round_agree_tr,
    Rabia.phase_rnd2_decision_bc_started_tr,
    Rabia.phase_rnd2_decision_bc_vote_rnd1_tr,
    Rabia.phase_rnd2_decision_full_noval_inv_tr,
    Rabia.phase_rnd2_decision_full_val_agree_tr,
    Rabia.phase_rnd2_decision_full_val_inv_tr,
    Rabia.phase_rnd2_decision_full_val_validity_tr,
    Rabia.phase_rnd2_good_succ_good_tr,
    Rabia.phase_rnd2_good_zero_tr,
    Rabia.phase_rnd2_inv_0_tr,
    Rabia.phase_rnd2_inv_10_tr,
    Rabia.phase_rnd2_inv_11_tr,
    Rabia.phase_rnd2_inv_12_tr,
    Rabia.phase_rnd2_inv_13_tr,
    Rabia.phase_rnd2_inv_14_tr,
    Rabia.phase_rnd2_inv_15_tr,
    Rabia.phase_rnd2_inv_16_tr,
    Rabia.phase_rnd2_inv_17_tr,
    Rabia.phase_rnd2_inv_18_tr,
    Rabia.phase_rnd2_inv_19_tr,
    Rabia.phase_rnd2_inv_20_tr,
    Rabia.phase_rnd2_inv_21_tr,
    Rabia.phase_rnd2_inv_22_tr,
    Rabia.phase_rnd2_inv_23_tr,
    Rabia.phase_rnd2_inv_24_tr,
    Rabia.phase_rnd2_inv_25_tr,
    Rabia.phase_rnd2_inv_26_tr,
    Rabia.phase_rnd2_inv_27_tr,
    Rabia.phase_rnd2_inv_28_tr,
    Rabia.phase_rnd2_inv_2_tr,
    Rabia.phase_rnd2_inv_30_tr,
    Rabia.phase_rnd2_inv_31_tr,
    Rabia.phase_rnd2_inv_32_tr,
    Rabia.phase_rnd2_inv_33_tr,
    Rabia.phase_rnd2_inv_34_tr,
    Rabia.phase_rnd2_inv_35_tr,
    Rabia.phase_rnd2_inv_36_tr,
    Rabia.phase_rnd2_inv_37_tr,
    Rabia.phase_rnd2_inv_39_tr,
    Rabia.phase_rnd2_inv_41_tr,
    Rabia.phase_rnd2_inv_6_tr,
    Rabia.phase_rnd2_inv_7_tr,
    Rabia.phase_rnd2_inv_8_tr,
    Rabia.phase_rnd2_inv_9_tr,
    Rabia.phase_rnd2_started_pred_tr,
    Rabia.phase_rnd2_vl_decision_bc_agree_tr,
    Rabia.phase_rnd2_vote_rnd1_pred_rnd_tr,
    Rabia.phase_rnd2_vote_rnd2_vote_rnd1_tr]

theorem Invariants.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant
      (ConcreteInvariants (node := node) (set_majority := set_majority)
        (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)) := by
  intro th st hr
  induction hr with
  | init s has hinit =>
      cases th
      apply invariants_initial
      simpa [System'] using hinit
  | step s s' hreach hnext ih =>
      cases th
      rcases hnext with ⟨label, htr⟩
      cases label
      · apply invariants_initial_proposal ih
        simpa [System', relationalTransitionSystem, InitialProposalTr, Next, NextAct,
          initial_proposal.ext.derived_eq] using htr
      · apply invariants_decide_full_val ih
        simpa [System', relationalTransitionSystem, DecideFullValTr, Next, NextAct,
          decide_bc_decide_full_val.ext.derived_eq] using htr
      · apply invariants_decide_full_noval ih
        simpa [System', relationalTransitionSystem, DecideFullNoValTr, Next, NextAct,
          decide_bc_decide_full_noval.ext.derived_eq] using htr
      · apply invariants_initial_vote1 ih
        simpa [System', relationalTransitionSystem, InitialVote1Tr, Next, NextAct,
          initial_vote1.ext.derived_eq] using htr
      · apply invariants_phase_rnd1 ih
        simpa [System', relationalTransitionSystem, PhaseRnd1Tr, Next, NextAct,
          phase_rnd1.ext.derived_eq] using htr
      · apply invariants_phase_rnd2 ih
        simpa [System', relationalTransitionSystem, PhaseRnd2Tr, Next, NextAct,
          phase_rnd2.ext.derived_eq] using htr

private theorem invariant_projection
    {p : State' node set_majority set_f_plus_1 proposal_value → Prop}
    (hp : ∀ st,
      ConcreteInvariants (node := node) (set_majority := set_majority)
        (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value) st → p st) :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant p := by
  intro th st hr
  exact hp st (Invariants.is_inv th st hr)

theorem good_succ_good.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant
      (ConcreteInv (node := node) (set_majority := set_majority)
        (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)
        (fun th st => good_succ_good (th := th) (st := st))) := by
  apply invariant_projection
  intro st h
  dsimp [ConcreteInvariants, ConcreteInv, Invariants] at h ⊢
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem good_zero.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant
      (ConcreteInv (node := node) (set_majority := set_majority)
        (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)
        (fun th st => good_zero (th := th) (st := st))) := by
  apply invariant_projection
  intro st h
  dsimp [ConcreteInvariants, ConcreteInv, Invariants] at h ⊢
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem started_pred.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant
      (ConcreteInv (node := node) (set_majority := set_majority)
        (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)
        (fun th st => started_pred (th := th) (st := st))) := by
  apply invariant_projection
  intro st h
  dsimp [ConcreteInvariants, ConcreteInv, Invariants] at h ⊢
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem decision_bc_started.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant
      (ConcreteInv (node := node) (set_majority := set_majority)
        (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)
        (fun th st => decision_bc_started (th := th) (st := st))) := by
  apply invariant_projection
  intro st h
  dsimp [ConcreteInvariants, ConcreteInv, Invariants] at h ⊢
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem decision_bc_vote_rnd1.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant
      (ConcreteInv (node := node) (set_majority := set_majority)
        (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)
        (fun th st => decision_bc_vote_rnd1 (th := th) (st := st))) := by
  apply invariant_projection
  intro st h
  dsimp [ConcreteInvariants, ConcreteInv, Invariants] at h ⊢
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem vote_rnd1_pred_rnd.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant
      (ConcreteInv (node := node) (set_majority := set_majority)
        (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)
        (fun th st => vote_rnd1_pred_rnd (th := th) (st := st))) := by
  apply invariant_projection
  intro st h
  dsimp [ConcreteInvariants, ConcreteInv, Invariants] at h ⊢
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem vl_decision_bc_agree.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant
      (ConcreteInv (node := node) (set_majority := set_majority)
        (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)
        (fun th st => vl_decision_bc_agree (th := th) (st := st))) := by
  apply invariant_projection
  intro st h
  dsimp [ConcreteInvariants, ConcreteInv, Invariants] at h ⊢
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem decision_bc_same_round_agree.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant
      (ConcreteInv (node := node) (set_majority := set_majority)
        (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)
        (fun th st => decision_bc_same_round_agree (th := th) (st := st))) := by
  apply invariant_projection
  intro st h
  dsimp [ConcreteInvariants, ConcreteInv, Invariants] at h ⊢
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem decision_full_val_inv.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant
      (ConcreteInv (node := node) (set_majority := set_majority)
        (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)
        (fun th st => decision_full_val_inv (th := th) (st := st))) := by
  apply invariant_projection
  intro st h
  dsimp [ConcreteInvariants, ConcreteInv, Invariants] at h ⊢
  exact h.2.1

theorem decision_full_noval_inv.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant
      (ConcreteInv (node := node) (set_majority := set_majority)
        (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)
        (fun th st => decision_full_noval_inv (th := th) (st := st))) := by
  apply invariant_projection
  intro st h
  dsimp [ConcreteInvariants, ConcreteInv, Invariants] at h ⊢
  exact h.2.2.2.2.2.1

theorem decision_full_val_agree.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant
      (ConcreteInv (node := node) (set_majority := set_majority)
        (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)
        (fun th st => decision_full_val_agree (th := th) (st := st))) := by
  apply invariant_projection
  intro st h
  dsimp [ConcreteInvariants, ConcreteInv, Invariants] at h ⊢
  exact h.2.2.2.2.1

theorem decision_full_val_validity.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant
      (ConcreteInv (node := node) (set_majority := set_majority)
        (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)
        (fun th st => decision_full_val_validity (th := th) (st := st))) := by
  apply invariant_projection
  intro st h
  dsimp [ConcreteInvariants, ConcreteInv, Invariants] at h ⊢
  exact h.2.2.2.1

def started_good (s : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  ∀ (p : phase), phase_started p (th := ({} : Theory' node set_majority set_f_plus_1 proposal_value)) (st := s) →
    good p (th := ({} : Theory' node set_majority set_f_plus_1 proposal_value)) (st := s)

theorem started_good.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant started_good := by
  intro th s hr
  have hgsg := Rabia.good_succ_good.is_inv th s hr
  have hgz0 := Rabia.good_zero.is_inv th s hr
  have hhp := Rabia.started_pred.is_inv th s hr

  intro p hstarted
  induction p with
  | zero => apply hgz0 ; exact hstarted
  | succ p ih =>
    apply hgsg p ; apply And.intro
    · apply ih ; apply hhp ; apply And.intro ; exact hstarted ; rfl
    · apply And.intro ; rfl ; exact hstarted

def validity_bc (s : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  ∀ N1 P1 V1, s.decision_bc N1 P1 V1 → ∃ N2, s.vote_rnd1 N2 0 V1

theorem validity_bc.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant validity_bc := by
  intro th s hr
  have hdr1 := Rabia.decision_bc_vote_rnd1.is_inv th s hr
  have hvr1_pred_r1 := Rabia.vote_rnd1_pred_rnd.is_inv th s hr

  suffices h : (∀ N1 P1 V1, s.vote_rnd1 N1 P1 V1 → ∃ N2, s.vote_rnd1 N2 0 V1) by
    intro n p v hh
    specialize hdr1 _ _ _ hh ; rcases hdr1 with ⟨n', hdr1⟩
    solve_by_elim
  intro n p
  induction p generalizing n with
  | zero => solve_by_elim
  | succ p ih =>
    intro v h
    specialize hvr1_pred_r1 _ _ _ _ ⟨h, rfl⟩ ; rcases hvr1_pred_r1 with ⟨n'', hvr1_pred_r1⟩
    solve_by_elim

def agreement_bc (s : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  ∀ N1 P1 V1 N2 P2 V2,
    s.decision_bc N1 P1 V1 →
    s.decision_bc N2 P2 V2 →
    V1 = V2

theorem agreement_bc.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant agreement_bc := by
  intro th s hr
  have hstarted := started_good.is_inv th s hr
  have hvld_agree := Rabia.vl_decision_bc_agree.is_inv th s hr
  have hdsr_agree := Rabia.decision_bc_same_round_agree.is_inv th s hr
  have hdstarted := Rabia.decision_bc_started.is_inv th s hr

  suffices h : (∀ N1 P1 V1 N2 P2 V2,
    P1 ≤ P2 →
    s.decision_bc N1 P1 V1 →
    s.decision_bc N2 P2 V2 →
    V1 = V2) by
    intro n1 p1 vv1 n2 p2 vv2
    by_cases hh : p1 ≤ p2
    · apply h ; assumption
    · intro h1 h2 ; symm ; revert h1 ; revert h2 ; apply h
      unfold phase at * ; omega
  intro n1 p1 vv1 n2 p2 vv2 hle hdec1 hdec2
  by_cases p1 = p2
  · subst_vars ; apply hdsr_agree ; solve_by_elim
  · have hlt : p1 < p2 := by unfold phase at * ; omega
    clear hle
    have hh : state_value_locked p2 vv1
        (th := ({} : Theory' node set_majority set_f_plus_1 proposal_value)) (st := s) := by
      dsimp [decision_bc_started] at hdstarted
      have hgood P hh := hstarted P hh |>.right |>.right
      dsimp only [phase_started] at hgood ; simp only [and_imp] at hgood
      apply hgood <;> solve_by_elim
    apply hvld_agree <;> solve_by_elim

def agreement2 (s : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  ∀ N1 P1 V1 N2 P2,
    s.decision_full_val N1 P1 V1 →
    s.decision_full_noval N2 P2 → False

theorem agreement2.is_inv :
    (System' (node := node) (set_majority := set_majority)
      (set_f_plus_1 := set_f_plus_1) (proposal_value := proposal_value)).isInvariant agreement2 := by
  intro th s hr
  have ha := Rabia.decision_full_val_inv.is_inv th s hr
  have hb := Rabia.decision_full_noval_inv.is_inv th s hr
  have hc := agreement_bc.is_inv th s hr

  intro n1 p1 vv1 n2 p2 hdec1 hdec2
  suffices state_value.v0 = state_value.v1 by contradiction
  specialize ha _ _ _ hdec1
  specialize hb _ _ hdec2
  solve_by_elim

end Rabia
