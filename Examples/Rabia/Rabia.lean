import Veil

-- adapted from [weak_mvc.ivy](https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/ivy/weak_mvc.ivy)

-- Axiomatizing an enumerated type containing three distinct elements:
-- `v0`, `v1`, and `vquestion`.
class ThreeValuedType (t : Type) where
  v0 : t
  v1 : t
  vquestion : t

  ax1 : v0 ≠ v1
  ax2 : v0 ≠ vquestion
  ax3 : v1 ≠ vquestion
  ax4 : ∀ (x : t), x = v0 ∨ x = v1 ∨ x = vquestion

-- Axioms from the Ivy spec.
class Rabia.Background (node set_majority set_f_plus_1 : outParam Type) where
  member_maj : node → set_majority → Prop
  member_fp1 : node → set_f_plus_1 → Prop

  ax0 : ∀ (Q1 Q2 : set_majority), ∃ (N : node), member_maj N Q1 ∧ member_maj N Q2
  ax1 : ∀ (Q1 : set_majority) (Q2 : set_f_plus_1), ∃ (N : node), member_maj N Q1 ∧ member_fp1 N Q2

veil module Rabia

-- `main` enables `veil.gen_sound` for the isolate recovery commands. Those
-- commands are disabled below because isolates are not supported in preview.
-- set_option veil.gen_sound true
set_option synthInstance.maxSize 8192

type node
type set_majority
type set_f_plus_1
instantiate bg : Background node set_majority set_f_plus_1

type phase
instantiate tot : TotalOrderWithMinimum phase

relation in_phase (N : node) (P : phase)

type proposal_value
type state_value
instantiate tv : ThreeValuedType state_value

open Background

relation propose (N : node) (V : proposal_value)
relation vote_rnd1 (N : node) (P : phase) (V : state_value)
relation vote_rnd2 (N : node) (P : phase) (V : state_value)

relation decision_bc (N : node) (P : phase) (V : state_value)
relation decision_full_val (N : node) (P : phase) (V : proposal_value)
relation decision_full_noval (N : node) (P : phase)
relation coin (P : phase) (V : state_value)

#gen_state

after_init {
  in_phase N P := false
  decision_bc N P V := false
  decision_full_val N P V := false
  decision_full_noval N P := false
  propose N V := false
  vote_rnd1 N P V := false
  vote_rnd2 N P V := false
  coin P V := false
}

action initial_proposal {
  let n : node ← pick
  let v : proposal_value ← pick
  assume ¬ ∃ V : proposal_value, propose n V
  assume ∀ P, ¬ ∃ V : state_value, vote_rnd1 n P V
  assume ∀ P, ¬ ∃ V : state_value, vote_rnd2 n P V
  assume ∀ P, ¬ ∃ V : state_value, decision_bc n P V
  assume ∀ P, ¬ in_phase n P
  propose n v := true
}

action decide_bc_decide_full_val {
  let n : node ← pick
  let p : phase ← pick
  let q : set_majority ← pick
  assume decision_bc n p tv.v1
  if v : (∀ (N : node), member_maj N q → propose N v) then
    decision_full_val n p v := true
}

action decide_bc_decide_full_noval {
  let n : node ← pick
  let p : phase ← pick
  assume decision_bc n p tv.v0
  decision_full_noval n p := true
}

action initial_vote1 {
  let n : node ← pick
  let q : set_majority ← pick
  assume ∃ V : proposal_value, propose n V
  assume ∀ P, ¬ ∃ V : state_value, vote_rnd1 n P V
  assume ∀ P, ¬ ∃ V : state_value, vote_rnd2 n P V
  assume ∀ P, ¬ ∃ V : state_value, decision_bc n P V
  assume ∀ P, ¬ in_phase n P

  if v : (∀ (N : node), member_maj N q → propose N v) then
    vote_rnd1 n tot.zero tv.v1 := true
    in_phase n tot.zero := true
  else
    vote_rnd1 n tot.zero tv.v0 := true
    in_phase n tot.zero := true
}

action phase_rnd1 {
  let n : node ← pick
  let p : phase ← pick
  let q : set_majority ← pick
  assume in_phase n p
  assume ¬ ∃ V : state_value, vote_rnd2 n p V
  assume ∀ (N : node), member_maj N q → ∃ V, vote_rnd1 N p V

  if v : (∀ (N : node), member_maj N q → vote_rnd1 N p v) then
    vote_rnd2 n p v := true
  else
    vote_rnd2 n p tv.vquestion := true
}

action phase_rnd2 {
  let n : node ← pick
  let p : phase ← pick
  let psucc : phase ← pick
  let q : set_majority ← pick
  assume in_phase n p
  assume ∃ V : state_value, vote_rnd2 n p V
  assume ∀ (N : node), member_maj N q → ∃ V, vote_rnd2 N p V
  assume tot.next p psucc

  if v : (v ≠ tv.vquestion ∧
      (∃ N0 Q, member_fp1 N0 Q ∧ (∀ N, member_fp1 N Q → member_maj N q ∧ vote_rnd2 N p v)))
  then
    decision_bc n p v := true
    vote_rnd1 n psucc v := true
    in_phase n psucc := true
    in_phase n p := false
  else
    if v : (v ≠ tv.vquestion ∧ (∃ N, member_maj N q ∧ vote_rnd2 N p v)) then
      vote_rnd1 n psucc v := true
      in_phase n psucc := true
      in_phase n p := false
    else
      if v : (v ≠ tv.vquestion ∧ coin p v) then
        vote_rnd1 n psucc v := true
        in_phase n psucc := true
        in_phase n p := false
      else
        let v : state_value ← pick
        assume v ≠ tv.vquestion
        coin p v := true
        vote_rnd1 n psucc v := true
        in_phase n psucc := true
        in_phase n p := false
}

-- NOTE: These invsets correspond to the `isolate`s in the Ivy spec.
invset Protocol {

invariant propose N V1 ∧ propose N V2 → V1 = V2
invariant [decision_full_val_inv] decision_full_val N P V → decision_bc N P tv.v1
invariant decision_full_val N P V →
  ∃ Q : set_majority, ∀ N : node, member_maj N Q → propose N V
invariant [decision_full_val_validity] decision_full_val N P V → ∃ N0 : node, propose N0 V
invariant [decision_full_val_agree] decision_full_val N1 P1 V1 ∧ decision_full_val N2 P2 V2 → V1 = V2
invariant [decision_full_noval_inv] decision_full_noval N P → decision_bc N P tv.v0

invariant in_phase N P1 ∧ in_phase N P2 → P1 = P2
invariant vote_rnd1 N P1 V ∧ in_phase N P2 → tot.le P1 P2
invariant vote_rnd2 N P1 V ∧ in_phase N P2 → tot.le P1 P2
invariant vote_rnd2 N P V2 → ∃ V1, vote_rnd1 N P V1
invariant in_phase N P1 → ∃ V1, vote_rnd1 N P1 V1
invariant in_phase N P1 ∧ tot.le P1 P2 ∧ P1 ≠ P2 → ¬ ∃ V1, vote_rnd1 N P2 V1
invariant in_phase N P1 ∧ tot.le P1 P2 ∧ P1 ≠ P2 → ¬ ∃ V1, vote_rnd2 N P2 V1

invariant vote_rnd1 N P V → V ≠ tv.vquestion
invariant vote_rnd1 N P V1 ∧ vote_rnd1 N P V2 → V1 = V2
invariant vote_rnd2 N P V1 ∧ vote_rnd2 N P V2 → V1 = V2
invariant vote_rnd2 N1 P V1 ∧ vote_rnd2 N2 P V2 ∧ V1 ≠ tv.vquestion ∧ V2 ≠ tv.vquestion → V1 = V2
invariant vote_rnd2 N P V ∧ V ≠ tv.vquestion →
  ∃ Q : set_majority, ∀ N : node, member_maj N Q → vote_rnd1 N P V
invariant decision_bc N P1 V ∧ in_phase N P2 → P1 ≠ P2 ∧ tot.le P1 P2
invariant in_phase N P → ¬ ∃ V, decision_bc N P V
invariant decision_bc N1 P1 V1 → V1 ≠ tv.vquestion
invariant decision_bc N P V → ∃ Q : set_f_plus_1, ∀ N : node, member_fp1 N Q → vote_rnd2 N P V

invariant ¬ coin P tv.vquestion
invariant ¬ (coin P tv.v0 ∧ coin P tv.v1)
-- CHECK the following one does not seem to make sense? Comment out for now.
-- invariant decision_bc N P V ∧ vote_rnd2 N2 P V2 → V2 ≠ tv.vquestion ∨ V2 = V2
invariant ∀ Q, coin P V → ∃ N : node, member_fp1 N Q ∧ vote_rnd2 N P tv.vquestion
invariant decision_bc N P V → ¬ coin P V2

invariant coin P V → ∃ Q : set_majority, ∀ N : node, member_maj N Q → ∃ V, vote_rnd2 N P V
invariant tot.next P P2 ∧ vote_rnd1 N P2 V →
  ∃ Q : set_majority, ∀ N : node, member_maj N Q → ∃ V, vote_rnd2 N P V
invariant tot.next P P2 ∧ vote_rnd1 N P2 V ∧ ¬ coin P tv.v0 ∧ ¬ coin P tv.v1 →
  ∃ (Q : set_majority) (N : node), member_maj N Q ∧ vote_rnd2 N P V

ghost relation state_value_locked (p : phase) (v : state_value) :=
  ∀ N Valt, vote_rnd1 N p Valt → Valt = v

ghost relation strong_state_value_locked (p : phase) (v : state_value) :=
  ∃ N : node, vote_rnd1 N p v ∧ (∀ N Valt, vote_rnd1 N p Valt → Valt = v)

ghost relation members_voted_rnd2 (q : set_majority) (p : phase) :=
  ∀ N, member_maj N q → ∃ V, vote_rnd2 N p V

invariant [vote_rnd1_pred_rnd] vote_rnd1 N1 P2 V1 ∧ tot.next P P2 → ∃ N2, vote_rnd1 N2 P V1

invariant decision_bc N1 P V1 ∧ tot.next P P2 → state_value_locked P2 V1

invariant state_value_locked P V1 ∧ vote_rnd2 N P V2 → V1 = V2 ∨ V2 = tv.vquestion

invariant coin P V →
  ∃ Q : set_majority, ∀ N : node, member_maj N Q → vote_rnd2 N P tv.vquestion

invariant state_value_locked P V → ∀ Q : set_majority, members_voted_rnd2 Q P →
  ∃ N : node, member_maj N Q ∧ vote_rnd2 N P V
invariant state_value_locked P V → ∀ Q : set_majority, members_voted_rnd2 Q P → ¬ coin P V2
invariant state_value_locked P V ∧ tot.next P P2 → state_value_locked P2 V

invariant decision_bc N1 P V1 ∧ tot.next P P2 → ∀ Q : set_majority, members_voted_rnd2 Q P2 →
  ∃ N : node, member_maj N Q ∧ vote_rnd2 N P2 V1
invariant decision_bc N1 P V1 ∧ tot.next P P2 → ¬ ∃ V, coin P2 V

invariant [vl_decision_bc_agree] state_value_locked P V ∧ decision_bc N2 P V2 → V = V2

invariant decision_bc N1 P V1 ∧ tot.next P P2 ∧ decision_bc N2 P2 V2 → V1 = V2

invariant [decision_bc_same_round_agree] decision_bc N1 P V1 ∧ decision_bc N2 P V2 → V1 = V2

invariant (∃ N V, vote_rnd1 N P V) ∧ state_value_locked P V1 ∧ state_value_locked P V2 → V1 = V2
}

ghost relation phase_started (p : phase) := ∃ N V, vote_rnd1 N p V

ghost relation good (p : phase) :=
  phase_started p ∧
  (∀ P0, tot.lt P0 p → phase_started P0) ∧
  (∀ P0 V0, tot.lt P0 p ∧ phase_started P0 ∧
    ((∃ N, decision_bc N P0 V0) ∨ state_value_locked P0 V0) →
      state_value_locked p V0)

invset Wrapper1 extends Protocol {
invariant [good_succ_good] good P ∧ tot.next P P2 ∧ phase_started P2 → good P2
}

invset Wrapper2 extends Wrapper1 {
invariant [good_zero] phase_started tot.zero → good tot.zero
}

invset Wrapper3 extends Wrapper2 {
invariant [started_pred] phase_started P2 ∧ tot.next P P2 → phase_started P
}

invset Wrapper4 extends Protocol {
invariant [decision_bc_started] decision_bc N P V2 → phase_started P
}

invset Wrapper5 extends Protocol {
invariant [vote_rnd2_vote_rnd1] vote_rnd2 N P V ∧ V ≠ tv.vquestion → ∃ N2, vote_rnd1 N2 P V
invariant [decision_bc_vote_rnd1] decision_bc N P V → ∃ N2, vote_rnd1 N2 P V
}


set_option veil.solver "grind+smt"
set_option maxHeartbeats 8000000
set_option veil.smt.timeout 120

-- set_option veil.smt.trust false
#gen_spec


theorem TotalOrderWithMinimum.prev_unique {α : Type} [TotalOrderWithMinimum α] {p q r : α}
    (hp : TotalOrderWithMinimum.next p r) (hq : TotalOrderWithMinimum.next q r) : p = q := by
  have hp_next := (TotalOrderWithMinimum.next_def p r).mp hp
  have hq_next := (TotalOrderWithMinimum.next_def q r).mp hq
  by_cases hpq : p = q
  · exact hpq
  rcases TotalOrderWithMinimum.le_total p q with hpq_le | hqp_le
  · have hpq_lt : TotalOrderWithMinimum.lt p q :=
      (TotalOrderWithMinimum.le_lt p q).mpr ⟨hpq_le, hpq⟩
    have hrq_le : TotalOrderWithMinimum.le r q := hp_next.2 q hpq_lt
    have hqr := (TotalOrderWithMinimum.le_lt q r).mp hq_next.1
    have hqr_eq : q = r := TotalOrderWithMinimum.le_antisymm q r hqr.1 hrq_le
    exact False.elim (hqr.2 hqr_eq)
  · have hqp_lt : TotalOrderWithMinimum.lt q p :=
      (TotalOrderWithMinimum.le_lt q p).mpr ⟨hqp_le, fun h => hpq h.symm⟩
    have hrp_le : TotalOrderWithMinimum.le r p := hq_next.2 p hqp_lt
    have hpr := (TotalOrderWithMinimum.le_lt p r).mp hp_next.1
    have hpr_eq : p = r := TotalOrderWithMinimum.le_antisymm p r hpr.1 hrp_le
    exact False.elim (hpr.2 hpr_eq)

theorem TotalOrderWithMinimum.next_unique {α : Type} [TotalOrderWithMinimum α] {p q r : α}
    (hq : TotalOrderWithMinimum.next p q) (hr : TotalOrderWithMinimum.next p r) : q = r := by
  have hq_next := (TotalOrderWithMinimum.next_def p q).mp hq
  have hr_next := (TotalOrderWithMinimum.next_def p r).mp hr
  exact TotalOrderWithMinimum.le_antisymm q r (hq_next.2 r hr_next.1) (hr_next.2 q hq_next.1)

theorem TotalOrderWithMinimum.next_ne {α : Type} [TotalOrderWithMinimum α] {p r : α}
    (h : TotalOrderWithMinimum.next p r) : p ≠ r := by
  exact ((TotalOrderWithMinimum.le_lt p r).mp ((TotalOrderWithMinimum.next_def p r).mp h).1).2

theorem TotalOrderWithMinimum.eq_or_lt_of_lt_next {α : Type} [TotalOrderWithMinimum α] {p q r : α}
    (hnext : TotalOrderWithMinimum.next q r) (hlt : TotalOrderWithMinimum.lt p r) :
    p = q ∨ TotalOrderWithMinimum.lt p q := by
  have hn := (TotalOrderWithMinimum.next_def q r).mp hnext
  rcases TotalOrderWithMinimum.le_total p q with hpq | hqp
  · by_cases hpq_eq : p = q
    · exact Or.inl hpq_eq
    · exact Or.inr ((TotalOrderWithMinimum.le_lt p q).mpr ⟨hpq, hpq_eq⟩)
  · by_cases hqp_eq : q = p
    · exact Or.inl hqp_eq.symm
    · have hq_lt_p : TotalOrderWithMinimum.lt q p :=
        (TotalOrderWithMinimum.le_lt q p).mpr ⟨hqp, hqp_eq⟩
      have hr_le_p : TotalOrderWithMinimum.le r p := hn.2 p hq_lt_p
      have hp_lt_r := (TotalOrderWithMinimum.le_lt p r).mp hlt
      have hpr_eq : p = r := TotalOrderWithMinimum.le_antisymm p r hp_lt_r.1 hr_le_p
      exact False.elim (hp_lt_r.2 hpr_eq)

theorem ThreeValuedType.eq_of_ne_question_of_ne_same {α : Type} [ThreeValuedType α] {x y z : α}
    (hxq : x ≠ ThreeValuedType.vquestion) (hyq : y ≠ ThreeValuedType.vquestion)
    (hxz : x ≠ z) (hyz : y ≠ z) (hzq : z ≠ ThreeValuedType.vquestion) : x = y := by
  have hxCases := ThreeValuedType.ax4 x
  have hyCases := ThreeValuedType.ax4 y
  have hzCases := ThreeValuedType.ax4 z
  grind


@[veil]
theorem phase_rnd2_good_succ_good (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (set_majority : Type) [set_majority_dec_eq : DecidableEq.{1} set_majority]
    [set_majority_inhabited : Inhabited.{1} set_majority] (set_f_plus_1 : Type)
    [set_f_plus_1_dec_eq : DecidableEq.{1} set_f_plus_1] [set_f_plus_1_inhabited : Inhabited.{1} set_f_plus_1]
    [bg : Background node set_majority set_f_plus_1] (phase : Type) [phase_dec_eq : DecidableEq.{1} phase]
    [phase_inhabited : Inhabited.{1} phase] [tot : TotalOrderWithMinimum phase] (proposal_value : Type)
    [proposal_value_dec_eq : DecidableEq.{1} proposal_value] [proposal_value_inhabited : Inhabited.{1} proposal_value]
    (state_value : Type) [state_value_dec_eq : DecidableEq.{1} state_value]
    [state_value_inhabited : Inhabited.{1} state_value] [tv : ThreeValuedType state_value] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory node set_majority set_f_plus_1 phase proposal_value state_value) ρ]
    [phase_rnd2_dec_0 :
      delta% @Rabia.phase_rnd2._veil_dec_type_0 χ node phase state_value set_majority set_f_plus_1 proposal_value χ_rep]
    [phase_rnd2_dec_1 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_1 χ phase set_majority node set_f_plus_1 bg state_value proposal_value χ_rep]
    [phase_rnd2_dec_2 : delta% @Rabia.phase_rnd2._veil_dec_type_2 phase tot]
    [phase_rnd2_dec_3 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_3 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_4 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_4 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_5 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_5 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_6 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_6 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_7 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_7 χ phase state_value tv node set_majority set_f_plus_1 proposal_value χ_rep] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@phase_rnd2.ext ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub phase_rnd2_dec_0 phase_rnd2_dec_1 phase_rnd2_dec_2 phase_rnd2_dec_3 phase_rnd2_dec_4
        phase_rnd2_dec_5 phase_rnd2_dec_6 phase_rnd2_dec_7)
      (@Assumptions ρ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv ρ_sub)
      (@Invariants ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub)
      (@good_succ_good ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  rcases hinv with
    ⟨hProposeUnique, hDecisionFullValInv, hDecisionFullValQuorum, hDecisionFullValValid, hDecisionFullValAgree,
      hDecisionFullNoValInv, hInPhaseUnique, hVoteRnd1Le, hVoteRnd2Le, hVoteRnd2ImpliesVoteRnd1,
      hInPhaseVote, hNoFutureVoteRnd1, hNoFutureVoteRnd2, hVoteRnd1NonQuestion, hVoteRnd1Unique,
      hVoteRnd2Unique, hVoteRnd2Agreement, hVoteRnd2NonQuestionVoteRnd1, hDecisionInPhase,
      hInPhaseNoDecision, hDecisionNonQuestion, hDecisionFp1, hNoCoinQuestion, hCoin01, hCoinFp1Question,
      hDecisionNoCoin, hCoinMembers, hNextVoteMembers, hNextVoteNoCoinWitness, hVotePred,
      hDecisionLockNext, hLockedRnd2, hCoinQuestionMajority, hLockedWitness, hLockedNoCoin, hLockedNext,
      hDecisionNextWitness, hDecisionNextNoCoin, hLockedDecisionAgree, hDecisionNextAgree,
      hDecisionSameRoundAgree, hLockedUnique, hGoodSucc, hGoodZero, hStartedPred, hDecisionStarted,
      hVoteRnd2VoteRnd1, hDecisionVoteRnd1⟩
  intro hinPhase _ _ hMembers hNext
  have goodSuccCore
      (vote' : node → phase → state_value → Prop)
      (decision' : node → phase → state_value → Prop)
      (hDecisionStep :
        ∀ {P P2 : phase} {Val : state_value},
          (∃ N : node, decision' N P Val) →
            TotalOrderWithMinimum.next P P2 →
              ∀ (N : node) (Valt : state_value), vote' N P2 Valt → Valt = Val)
      (hLockedStep :
        ∀ {P P2 : phase} {Val : state_value},
          (∀ (N : node) (Valt : state_value), vote' N P Valt → Valt = Val) →
            TotalOrderWithMinimum.next P P2 →
              ∀ (N : node) (Valt : state_value), vote' N P2 Valt → Valt = Val) :
      ∀ (P P2 : phase) (x : node) (x_1 : state_value),
        vote' x P x_1 →
          (∀ (P0 : phase), TotalOrderWithMinimum.lt P0 P → ∃ N V, vote' N P0 V) →
            (∀ (P0 : phase) (V0 : state_value),
                TotalOrderWithMinimum.lt P0 P →
                  ∀ (x : node) (x_2 : state_value),
                    vote' x P0 x_2 →
                      ((∃ N, decision' N P0 V0) ∨
                          ∀ (N : node) (Valt : state_value), vote' N P0 Valt → Valt = V0) →
                        ∀ (N : node) (Valt : state_value), vote' N P Valt → Valt = V0) →
              TotalOrderWithMinimum.next P P2 →
                ∀ (x : node) (x_2 : state_value),
                  vote' x P2 x_2 →
                    (∃ N V, vote' N P2 V) ∧
                      (∀ (P0 : phase), TotalOrderWithMinimum.lt P0 P2 → ∃ N V, vote' N P0 V) ∧
                        ∀ (P0 : phase) (V0 : state_value),
                          TotalOrderWithMinimum.lt P0 P2 →
                            ∀ (x : node) (x_3 : state_value),
                              vote' x P0 x_3 →
                                ((∃ N, decision' N P0 V0) ∨
                                    ∀ (N : node) (Valt : state_value), vote' N P0 Valt → Valt = V0) →
                                  ∀ (N : node) (Valt : state_value), vote' N P2 Valt → Valt = V0 := by
    intro P P2 x x_1 hStartedP hStartedBeforeP hGoodP hNextPP2 x_2 x_3 hStartedP2
    constructor
    · exact ⟨x_2, x_3, hStartedP2⟩
    constructor
    · intro P0 hLtP0P2
      rcases TotalOrderWithMinimum.eq_or_lt_of_lt_next hNextPP2 hLtP0P2 with hP0 | hLtP0P
      · subst P0
        exact ⟨x, x_1, hStartedP⟩
      · exact hStartedBeforeP P0 hLtP0P
    · intro P0 V0 hLtP0P2 x_4 x_5 hStartedP0 hCause N Valt hVoteP2
      rcases TotalOrderWithMinimum.eq_or_lt_of_lt_next hNextPP2 hLtP0P2 with hP0 | hLtP0P
      · subst P0
        rcases hCause with hDecision | hLocked
        · exact hDecisionStep hDecision hNextPP2 N Valt hVoteP2
        · exact hLockedStep hLocked hNextPP2 N Valt hVoteP2
      · have hLockedP := hGoodP P0 V0 hLtP0P x_4 x_5 hStartedP0 hCause
        exact hLockedStep hLockedP hNextPP2 N Valt hVoteP2
  split
  · intro vnew hNonQuestion fpNode fpQ hfpMem hfpAll
    let vote' : node → phase → state_value → Prop :=
      fun N P V => (n = N → psucc = P → ¬vnew = V) → st.vote_rnd1 N P V = true
    let decision' : node → phase → state_value → Prop :=
      fun N P V => (n = N → p = P → ¬vnew = V) → st.decision_bc N P V = true
    have hNoCoinAtP (V : state_value) : st.coin p V = false := by
      by_cases hCoin : st.coin p V = true
      · obtain ⟨w, hwMem, hwQuestion⟩ := hCoinFp1Question p V fpQ hCoin
        have hwNew : st.vote_rnd2 w p vnew = true := (hfpAll w hwMem).2
        have hqEq : ThreeValuedType.vquestion = vnew :=
          hVoteRnd2Unique w p ThreeValuedType.vquestion vnew hwQuestion hwNew
        exact False.elim (hNonQuestion hqEq.symm)
      · exact Bool.eq_false_iff.mpr hCoin
    have hLockedStep :
        ∀ {P P2 : phase} {Val : state_value},
          (∀ (N : node) (Valt : state_value), vote' N P Valt → Valt = Val) →
            TotalOrderWithMinimum.next P P2 →
              ∀ (N : node) (Valt : state_value), vote' N P2 Valt → Valt = Val := by
      intro P P2 Val hLocked hNextPP2 N Valt hVote
      by_cases hnewVote : n = N ∧ psucc = P2 ∧ vnew = Valt
      · rcases hnewVote with ⟨hn, hpsucc, hv⟩
        subst N
        subst P2
        subst Valt
        have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPP2 hNext
        subst P
        have hLockedOld :
            ∀ (N : node) (Valt : state_value), st.vote_rnd1 N p Valt = true → Valt = Val := by
          intro N Valt hOldVote
          exact hLocked N Valt (fun _ => hOldVote)
        have hEqOr := hLockedRnd2 p Val fpNode vnew hLockedOld ((hfpAll fpNode hfpMem).2)
        rcases hEqOr with hEq | hQuestion
        · exact hEq.symm
        · exact False.elim (hNonQuestion hQuestion)
      · have hOldVote : st.vote_rnd1 N P2 Valt = true := hVote (by
          intro hn hpsucc hv
          exact hnewVote ⟨hn, hpsucc, hv⟩)
        have hLockedOld :
            ∀ (N : node) (Valt : state_value), st.vote_rnd1 N P Valt = true → Valt = Val := by
          intro N Valt hOldVote
          exact hLocked N Valt (fun _ => hOldVote)
        exact hLockedNext P Val P2 hLockedOld hNextPP2 N Valt hOldVote
    have hDecisionStep :
        ∀ {P P2 : phase} {Val : state_value},
          (∃ N : node, decision' N P Val) →
            TotalOrderWithMinimum.next P P2 →
              ∀ (N : node) (Valt : state_value), vote' N P2 Valt → Valt = Val := by
      intro P P2 Val hDecision hNextPP2 N Valt hVote
      obtain ⟨Ndec, hDecisionUpdated⟩ := hDecision
      by_cases hnewVote : n = N ∧ psucc = P2 ∧ vnew = Valt
      · rcases hnewVote with ⟨hn, hpsucc, hv⟩
        subst N
        subst P2
        subst Valt
        have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPP2 hNext
        subst P
        by_cases hnewDecision : n = Ndec ∧ vnew = Val
        · rcases hnewDecision with ⟨hN, hVal⟩
          subst Ndec
          subst Val
          rfl
        · have hOldDecision : st.decision_bc Ndec p Val = true := hDecisionUpdated (by
            intro hN _ hVal
            exact hnewDecision ⟨hN, hVal⟩)
          obtain ⟨Qdec, hQdec⟩ := hDecisionFp1 Ndec p Val hOldDecision
          obtain ⟨w, _, hwFp⟩ := Background.ax1 q Qdec
          have hRnd2Val : st.vote_rnd2 w p Val = true := hQdec w hwFp
          have hEq : Val = vnew :=
            hVoteRnd2Agreement w p Val fpNode vnew hRnd2Val ((hfpAll fpNode hfpMem).2)
              (hDecisionNonQuestion Ndec p Val hOldDecision) hNonQuestion
          exact hEq.symm
      · have hOldVote : st.vote_rnd1 N P2 Valt = true := hVote (by
          intro hn hpsucc hv
          exact hnewVote ⟨hn, hpsucc, hv⟩)
        by_cases hnewDecision : n = Ndec ∧ p = P ∧ vnew = Val
        · rcases hnewDecision with ⟨hN, hP, hVal⟩
          subst Ndec
          subst P
          subst Val
          have hP2 : P2 = psucc := TotalOrderWithMinimum.next_unique hNextPP2 hNext
          subst P2
          obtain ⟨Q, w, hwMaj, hwRnd2⟩ :=
            hNextVoteNoCoinWitness p psucc N Valt hNext hOldVote
              (hNoCoinAtP ThreeValuedType.v0) (hNoCoinAtP ThreeValuedType.v1)
          have hValtNonQuestion : ¬Valt = ThreeValuedType.vquestion :=
            hVoteRnd1NonQuestion N psucc Valt hOldVote
          exact hVoteRnd2Agreement w p Valt fpNode vnew hwRnd2 ((hfpAll fpNode hfpMem).2)
            hValtNonQuestion hNonQuestion
        · have hOldDecision : st.decision_bc Ndec P Val = true := hDecisionUpdated (by
            intro hN hP hVal
            exact hnewDecision ⟨hN, hP, hVal⟩)
          exact hDecisionLockNext Ndec P Val P2 hOldDecision hNextPP2 N Valt hOldVote
    exact goodSuccCore vote' decision' hDecisionStep hLockedStep
  · rename_i hNoDecision
    split
    · intro vnew hNonQuestion majNode hMaj hVoteMaj
      let vote' : node → phase → state_value → Prop :=
        fun N P V => (n = N → psucc = P → ¬vnew = V) → st.vote_rnd1 N P V = true
      let decision' : node → phase → state_value → Prop :=
        fun N P V => st.decision_bc N P V = true
      have hLockedStep :
          ∀ {P P2 : phase} {Val : state_value},
            (∀ (N : node) (Valt : state_value), vote' N P Valt → Valt = Val) →
              TotalOrderWithMinimum.next P P2 →
                ∀ (N : node) (Valt : state_value), vote' N P2 Valt → Valt = Val := by
        intro P P2 Val hLocked hNextPP2 N Valt hVote
        by_cases hnewVote : n = N ∧ psucc = P2 ∧ vnew = Valt
        · rcases hnewVote with ⟨hn, hpsucc, hv⟩
          subst N
          subst P2
          subst Valt
          have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPP2 hNext
          subst P
          have hLockedOld :
              ∀ (N : node) (Valt : state_value), st.vote_rnd1 N p Valt = true → Valt = Val := by
            intro N Valt hOldVote
            exact hLocked N Valt (fun _ => hOldVote)
          have hEqOr := hLockedRnd2 p Val majNode vnew hLockedOld hVoteMaj
          rcases hEqOr with hEq | hQuestion
          · exact hEq.symm
          · exact False.elim (hNonQuestion hQuestion)
        · have hOldVote : st.vote_rnd1 N P2 Valt = true := hVote (by
            intro hn hpsucc hv
            exact hnewVote ⟨hn, hpsucc, hv⟩)
          have hLockedOld :
              ∀ (N : node) (Valt : state_value), st.vote_rnd1 N P Valt = true → Valt = Val := by
            intro N Valt hOldVote
            exact hLocked N Valt (fun _ => hOldVote)
          exact hLockedNext P Val P2 hLockedOld hNextPP2 N Valt hOldVote
      have hDecisionStep :
          ∀ {P P2 : phase} {Val : state_value},
            (∃ N : node, decision' N P Val) →
              TotalOrderWithMinimum.next P P2 →
                ∀ (N : node) (Valt : state_value), vote' N P2 Valt → Valt = Val := by
        intro P P2 Val hDecision hNextPP2 N Valt hVote
        obtain ⟨Ndec, hOldDecision⟩ := hDecision
        by_cases hnewVote : n = N ∧ psucc = P2 ∧ vnew = Valt
        · rcases hnewVote with ⟨hn, hpsucc, hv⟩
          subst N
          subst P2
          subst Valt
          have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPP2 hNext
          subst P
          obtain ⟨Qdec, hQdec⟩ := hDecisionFp1 Ndec p Val hOldDecision
          obtain ⟨w, _, hwFp⟩ := Background.ax1 q Qdec
          have hRnd2Val : st.vote_rnd2 w p Val = true := hQdec w hwFp
          have hEq : Val = vnew :=
            hVoteRnd2Agreement w p Val majNode vnew hRnd2Val hVoteMaj
              (hDecisionNonQuestion Ndec p Val hOldDecision) hNonQuestion
          exact hEq.symm
        · have hOldVote : st.vote_rnd1 N P2 Valt = true := hVote (by
            intro hn hpsucc hv
            exact hnewVote ⟨hn, hpsucc, hv⟩)
          exact hDecisionLockNext Ndec P Val P2 hOldDecision hNextPP2 N Valt hOldVote
      exact goodSuccCore vote' decision' hDecisionStep hLockedStep
    · rename_i hNoMajVote
      split
      · intro vnew hNonQuestion hCoin
        let vote' : node → phase → state_value → Prop :=
          fun N P V => (n = N → psucc = P → ¬vnew = V) → st.vote_rnd1 N P V = true
        let decision' : node → phase → state_value → Prop :=
          fun N P V => st.decision_bc N P V = true
        have hLockedStep :
            ∀ {P P2 : phase} {Val : state_value},
              (∀ (N : node) (Valt : state_value), vote' N P Valt → Valt = Val) →
                TotalOrderWithMinimum.next P P2 →
                  ∀ (N : node) (Valt : state_value), vote' N P2 Valt → Valt = Val := by
          intro P P2 Val hLocked hNextPP2 N Valt hVote
          by_cases hnewVote : n = N ∧ psucc = P2 ∧ vnew = Valt
          · rcases hnewVote with ⟨hn, hpsucc, hv⟩
            subst N
            subst P2
            subst Valt
            have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPP2 hNext
            subst P
            have hLockedOld :
                ∀ (N : node) (Valt : state_value), st.vote_rnd1 N p Valt = true → Valt = Val := by
              intro N Valt hOldVote
              exact hLocked N Valt (fun _ => hOldVote)
            have hNoCoin := hLockedNoCoin p Val vnew hLockedOld q hMembers
            simp [hCoin] at hNoCoin
          · have hOldVote : st.vote_rnd1 N P2 Valt = true := hVote (by
              intro hn hpsucc hv
              exact hnewVote ⟨hn, hpsucc, hv⟩)
            have hLockedOld :
                ∀ (N : node) (Valt : state_value), st.vote_rnd1 N P Valt = true → Valt = Val := by
              intro N Valt hOldVote
              exact hLocked N Valt (fun _ => hOldVote)
            exact hLockedNext P Val P2 hLockedOld hNextPP2 N Valt hOldVote
        have hDecisionStep :
            ∀ {P P2 : phase} {Val : state_value},
              (∃ N : node, decision' N P Val) →
                TotalOrderWithMinimum.next P P2 →
                  ∀ (N : node) (Valt : state_value), vote' N P2 Valt → Valt = Val := by
          intro P P2 Val hDecision hNextPP2 N Valt hVote
          obtain ⟨Ndec, hOldDecision⟩ := hDecision
          by_cases hnewVote : n = N ∧ psucc = P2 ∧ vnew = Valt
          · rcases hnewVote with ⟨hn, hpsucc, hv⟩
            subst N
            subst P2
            subst Valt
            have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPP2 hNext
            subst P
            have hNoCoin := hDecisionNoCoin Ndec p Val vnew hOldDecision
            simp [hCoin] at hNoCoin
          · have hOldVote : st.vote_rnd1 N P2 Valt = true := hVote (by
              intro hn hpsucc hv
              exact hnewVote ⟨hn, hpsucc, hv⟩)
            exact hDecisionLockNext Ndec P Val P2 hOldDecision hNextPP2 N Valt hOldVote
        exact goodSuccCore vote' decision' hDecisionStep hLockedStep
      · intro vnew hNonQuestion
        let vote' : node → phase → state_value → Prop :=
          fun N P V => (n = N → psucc = P → ¬vnew = V) → st.vote_rnd1 N P V = true
        let decision' : node → phase → state_value → Prop :=
          fun N P V => st.decision_bc N P V = true
        have hLockedStep :
            ∀ {P P2 : phase} {Val : state_value},
              (∀ (N : node) (Valt : state_value), vote' N P Valt → Valt = Val) →
                TotalOrderWithMinimum.next P P2 →
                  ∀ (N : node) (Valt : state_value), vote' N P2 Valt → Valt = Val := by
          intro P P2 Val hLocked hNextPP2 N Valt hVote
          by_cases hnewVote : n = N ∧ psucc = P2 ∧ vnew = Valt
          · rcases hnewVote with ⟨hn, hpsucc, hv⟩
            subst N
            subst P2
            subst Valt
            have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPP2 hNext
            subst P
            have hLockedOld :
                ∀ (N : node) (Valt : state_value), st.vote_rnd1 N p Valt = true → Valt = Val := by
              intro N Valt hOldVote
              exact hLocked N Valt (fun _ => hOldVote)
            obtain ⟨w, hwMaj, hwRnd2⟩ := hLockedWitness p Val hLockedOld q hMembers
            have hValNonQuestion : ¬Val = ThreeValuedType.vquestion := by
              obtain ⟨V0, hVote0⟩ := hInPhaseVote n p hinPhase
              have hEq : V0 = Val := hLockedOld n V0 hVote0
              intro hValQuestion
              exact hVoteRnd1NonQuestion n p V0 hVote0 (hEq.trans hValQuestion)
            exact False.elim (hNoMajVote ⟨Val, hValNonQuestion, ⟨w, hwMaj, hwRnd2⟩⟩)
          · have hOldVote : st.vote_rnd1 N P2 Valt = true := hVote (by
              intro hn hpsucc hv
              exact hnewVote ⟨hn, hpsucc, hv⟩)
            have hLockedOld :
                ∀ (N : node) (Valt : state_value), st.vote_rnd1 N P Valt = true → Valt = Val := by
              intro N Valt hOldVote
              exact hLocked N Valt (fun _ => hOldVote)
            exact hLockedNext P Val P2 hLockedOld hNextPP2 N Valt hOldVote
        have hDecisionStep :
            ∀ {P P2 : phase} {Val : state_value},
              (∃ N : node, decision' N P Val) →
                TotalOrderWithMinimum.next P P2 →
                  ∀ (N : node) (Valt : state_value), vote' N P2 Valt → Valt = Val := by
          intro P P2 Val hDecision hNextPP2 N Valt hVote
          obtain ⟨Ndec, hOldDecision⟩ := hDecision
          by_cases hnewVote : n = N ∧ psucc = P2 ∧ vnew = Valt
          · rcases hnewVote with ⟨hn, hpsucc, hv⟩
            subst N
            subst P2
            subst Valt
            have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPP2 hNext
            subst P
            obtain ⟨Qdec, hQdec⟩ := hDecisionFp1 Ndec p Val hOldDecision
            obtain ⟨w, hwMaj, hwFp⟩ := Background.ax1 q Qdec
            have hRnd2Val : st.vote_rnd2 w p Val = true := hQdec w hwFp
            exact False.elim
              (hNoMajVote ⟨Val, hDecisionNonQuestion Ndec p Val hOldDecision, ⟨w, hwMaj, hRnd2Val⟩⟩)
          · have hOldVote : st.vote_rnd1 N P2 Valt = true := hVote (by
              intro hn hpsucc hv
              exact hnewVote ⟨hn, hpsucc, hv⟩)
            exact hDecisionLockNext Ndec P Val P2 hOldDecision hNextPP2 N Valt hOldVote
        exact goodSuccCore vote' decision' hDecisionStep hLockedStep

@[veil]
theorem phase_rnd2_inv_35 (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (set_majority : Type) [set_majority_dec_eq : DecidableEq.{1} set_majority]
    [set_majority_inhabited : Inhabited.{1} set_majority] (set_f_plus_1 : Type)
    [set_f_plus_1_dec_eq : DecidableEq.{1} set_f_plus_1] [set_f_plus_1_inhabited : Inhabited.{1} set_f_plus_1]
    [bg : Background node set_majority set_f_plus_1] (phase : Type) [phase_dec_eq : DecidableEq.{1} phase]
    [phase_inhabited : Inhabited.{1} phase] [tot : TotalOrderWithMinimum phase] (proposal_value : Type)
    [proposal_value_dec_eq : DecidableEq.{1} proposal_value] [proposal_value_inhabited : Inhabited.{1} proposal_value]
    (state_value : Type) [state_value_dec_eq : DecidableEq.{1} state_value]
    [state_value_inhabited : Inhabited.{1} state_value] [tv : ThreeValuedType state_value] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory node set_majority set_f_plus_1 phase proposal_value state_value) ρ]
    [phase_rnd2_dec_0 :
      delta% @Rabia.phase_rnd2._veil_dec_type_0 χ node phase state_value set_majority set_f_plus_1 proposal_value χ_rep]
    [phase_rnd2_dec_1 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_1 χ phase set_majority node set_f_plus_1 bg state_value proposal_value χ_rep]
    [phase_rnd2_dec_2 : delta% @Rabia.phase_rnd2._veil_dec_type_2 phase tot]
    [phase_rnd2_dec_3 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_3 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_4 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_4 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_5 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_5 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_6 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_6 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_7 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_7 χ phase state_value tv node set_majority set_f_plus_1 proposal_value χ_rep] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@phase_rnd2.ext ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub phase_rnd2_dec_0 phase_rnd2_dec_1 phase_rnd2_dec_2 phase_rnd2_dec_3 phase_rnd2_dec_4
        phase_rnd2_dec_5 phase_rnd2_dec_6 phase_rnd2_dec_7)
      (@Assumptions ρ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv ρ_sub)
      (@Invariants ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub)
      (@inv_35 ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited set_f_plus_1
        set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  rcases hinv with
    ⟨hProposeUnique, hDecisionFullValInv, hDecisionFullValQuorum, hDecisionFullValValid, hDecisionFullValAgree,
      hDecisionFullNoValInv, hInPhaseUnique, hVoteRnd1Le, hVoteRnd2Le, hVoteRnd2ImpliesVoteRnd1,
      hInPhaseVote, hNoFutureVoteRnd1, hNoFutureVoteRnd2, hVoteRnd1NonQuestion, hVoteRnd1Unique,
      hVoteRnd2Unique, hVoteRnd2Agreement, hVoteRnd2NonQuestionVoteRnd1, hDecisionInPhase,
      hInPhaseNoDecision, hDecisionNonQuestion, hDecisionFp1, hNoCoinQuestion, hCoin01, hCoinFp1Question,
      hDecisionNoCoin, hCoinMembers, hNextVoteMembers, hNextVoteNoCoinWitness, hVotePred,
      hDecisionLockNext, hLockedRnd2, hCoinQuestionMajority, hLockedWitness, hLockedNoCoin, hLockedNext,
      hDecisionNextWitness, hDecisionNextNoCoin, hLockedDecisionAgree, hDecisionNextAgree,
      hDecisionSameRoundAgree, hLockedUnique, hGoodSucc, hGoodZero, hStartedPred, hDecisionStarted,
      hVoteRnd2VoteRnd1, hDecisionVoteRnd1⟩
  intro hinPhase _ _ hMembers hNext
  split
  · intro vnew hNonQuestion fpNode fpQ hfpMem hfpAll P V P2 hLocked hNextPP2 N Valt hVote
    by_cases hnewVote : n = N ∧ psucc = P2 ∧ vnew = Valt
    · rcases hnewVote with ⟨hn, hpsucc, hv⟩
      subst N
      subst P2
      subst Valt
      have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPP2 hNext
      subst P
      have hLockedOld :
          ∀ (N : node) (Valt : state_value), st.vote_rnd1 N p Valt = true → Valt = V := by
        intro N Valt hOldVote
        exact hLocked N Valt (fun _ => hOldVote)
      have hEqOr := hLockedRnd2 p V fpNode vnew hLockedOld ((hfpAll fpNode hfpMem).2)
      rcases hEqOr with hEq | hQuestion
      · exact hEq.symm
      · exact False.elim (hNonQuestion hQuestion)
    · have hOldVote : st.vote_rnd1 N P2 Valt = true := hVote (by
        intro hn hpsucc hv
        exact hnewVote ⟨hn, hpsucc, hv⟩)
      have hLockedOld :
          ∀ (N : node) (Valt : state_value), st.vote_rnd1 N P Valt = true → Valt = V := by
        intro N Valt hOldVote
        exact hLocked N Valt (fun _ => hOldVote)
      exact hLockedNext P V P2 hLockedOld hNextPP2 N Valt hOldVote
  · rename_i hNoDecision
    split
    · intro vnew hNonQuestion majNode hMaj hVoteMaj P V P2 hLocked hNextPP2 N Valt hVote
      by_cases hnewVote : n = N ∧ psucc = P2 ∧ vnew = Valt
      · rcases hnewVote with ⟨hn, hpsucc, hv⟩
        subst N
        subst P2
        subst Valt
        have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPP2 hNext
        subst P
        have hLockedOld :
            ∀ (N : node) (Valt : state_value), st.vote_rnd1 N p Valt = true → Valt = V := by
          intro N Valt hOldVote
          exact hLocked N Valt (fun _ => hOldVote)
        have hEqOr := hLockedRnd2 p V majNode vnew hLockedOld hVoteMaj
        rcases hEqOr with hEq | hQuestion
        · exact hEq.symm
        · exact False.elim (hNonQuestion hQuestion)
      · have hOldVote : st.vote_rnd1 N P2 Valt = true := hVote (by
          intro hn hpsucc hv
          exact hnewVote ⟨hn, hpsucc, hv⟩)
        have hLockedOld :
            ∀ (N : node) (Valt : state_value), st.vote_rnd1 N P Valt = true → Valt = V := by
          intro N Valt hOldVote
          exact hLocked N Valt (fun _ => hOldVote)
        exact hLockedNext P V P2 hLockedOld hNextPP2 N Valt hOldVote
    · rename_i hNoMajVote
      split
      · intro vnew hNonQuestion hCoin P V P2 hLocked hNextPP2 N Valt hVote
        by_cases hnewVote : n = N ∧ psucc = P2 ∧ vnew = Valt
        · rcases hnewVote with ⟨hn, hpsucc, hv⟩
          subst N
          subst P2
          subst Valt
          have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPP2 hNext
          subst P
          have hLockedOld :
              ∀ (N : node) (Valt : state_value), st.vote_rnd1 N p Valt = true → Valt = V := by
            intro N Valt hOldVote
            exact hLocked N Valt (fun _ => hOldVote)
          have hFalse : False := by
            have hNoCoin := hLockedNoCoin p V vnew hLockedOld q hMembers
            simp [hCoin] at hNoCoin
          exact False.elim hFalse
        · have hOldVote : st.vote_rnd1 N P2 Valt = true := hVote (by
            intro hn hpsucc hv
            exact hnewVote ⟨hn, hpsucc, hv⟩)
          have hLockedOld :
              ∀ (N : node) (Valt : state_value), st.vote_rnd1 N P Valt = true → Valt = V := by
            intro N Valt hOldVote
            exact hLocked N Valt (fun _ => hOldVote)
          exact hLockedNext P V P2 hLockedOld hNextPP2 N Valt hOldVote
      · intro vnew hNonQuestion P V P2 hLocked hNextPP2 N Valt hVote
        by_cases hnewVote : n = N ∧ psucc = P2 ∧ vnew = Valt
        · rcases hnewVote with ⟨hn, hpsucc, hv⟩
          subst N
          subst P2
          subst Valt
          have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPP2 hNext
          subst P
          have hLockedOld :
              ∀ (N : node) (Valt : state_value), st.vote_rnd1 N p Valt = true → Valt = V := by
            intro N Valt hOldVote
            exact hLocked N Valt (fun _ => hOldVote)
          obtain ⟨w, hwMaj, hwRnd2⟩ := hLockedWitness p V hLockedOld q hMembers
          have hValNonQuestion : ¬V = ThreeValuedType.vquestion := by
            obtain ⟨V0, hVote0⟩ := hInPhaseVote n p hinPhase
            have hEq : V0 = V := hLockedOld n V0 hVote0
            intro hVQuestion
            exact hVoteRnd1NonQuestion n p V0 hVote0 (hEq.trans hVQuestion)
          exact False.elim (hNoMajVote ⟨V, hValNonQuestion, ⟨w, hwMaj, hwRnd2⟩⟩)
        · have hOldVote : st.vote_rnd1 N P2 Valt = true := hVote (by
            intro hn hpsucc hv
            exact hnewVote ⟨hn, hpsucc, hv⟩)
          have hLockedOld :
              ∀ (N : node) (Valt : state_value), st.vote_rnd1 N P Valt = true → Valt = V := by
            intro N Valt hOldVote
            exact hLocked N Valt (fun _ => hOldVote)
          exact hLockedNext P V P2 hLockedOld hNextPP2 N Valt hOldVote

@[veil]
theorem phase_rnd2_inv_17 (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (set_majority : Type) [set_majority_dec_eq : DecidableEq.{1} set_majority]
    [set_majority_inhabited : Inhabited.{1} set_majority] (set_f_plus_1 : Type)
    [set_f_plus_1_dec_eq : DecidableEq.{1} set_f_plus_1] [set_f_plus_1_inhabited : Inhabited.{1} set_f_plus_1]
    [bg : Background node set_majority set_f_plus_1] (phase : Type) [phase_dec_eq : DecidableEq.{1} phase]
    [phase_inhabited : Inhabited.{1} phase] [tot : TotalOrderWithMinimum phase] (proposal_value : Type)
    [proposal_value_dec_eq : DecidableEq.{1} proposal_value] [proposal_value_inhabited : Inhabited.{1} proposal_value]
    (state_value : Type) [state_value_dec_eq : DecidableEq.{1} state_value]
    [state_value_inhabited : Inhabited.{1} state_value] [tv : ThreeValuedType state_value] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory node set_majority set_f_plus_1 phase proposal_value state_value) ρ]
    [phase_rnd2_dec_0 :
      delta% @Rabia.phase_rnd2._veil_dec_type_0 χ node phase state_value set_majority set_f_plus_1 proposal_value χ_rep]
    [phase_rnd2_dec_1 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_1 χ phase set_majority node set_f_plus_1 bg state_value proposal_value χ_rep]
    [phase_rnd2_dec_2 : delta% @Rabia.phase_rnd2._veil_dec_type_2 phase tot]
    [phase_rnd2_dec_3 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_3 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_4 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_4 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_5 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_5 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_6 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_6 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_7 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_7 χ phase state_value tv node set_majority set_f_plus_1 proposal_value χ_rep] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@phase_rnd2.ext ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub phase_rnd2_dec_0 phase_rnd2_dec_1 phase_rnd2_dec_2 phase_rnd2_dec_3 phase_rnd2_dec_4
        phase_rnd2_dec_5 phase_rnd2_dec_6 phase_rnd2_dec_7)
      (@Assumptions ρ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv ρ_sub)
      (@Invariants ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub)
      (@inv_17 ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited set_f_plus_1
        set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  rcases hinv with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hVoteRnd2NonQuestionVoteRnd1, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro _ _ _ _ _
  have preserve (vnew : state_value) (N : node) (P : phase) (V : state_value)
      (hVote : st.vote_rnd2 N P V = true) (hNonQuestion : ¬V = ThreeValuedType.vquestion) :
      ∃ Q : set_majority,
        ∀ M : node, member_maj M Q → (n = M → psucc = P → ¬vnew = V) → st.vote_rnd1 M P V = true := by
    obtain ⟨Q, hQ⟩ := hVoteRnd2NonQuestionVoteRnd1 N P V hVote hNonQuestion
    exact ⟨Q, by
      intro M hMem _
      exact hQ M hMem⟩
  split
  · intro vnew _ _ _ _ _ N P V hVote hNonQuestion
    exact preserve vnew N P V hVote hNonQuestion
  · split
    · intro vnew _ _ _ _ N P V hVote hNonQuestion
      exact preserve vnew N P V hVote hNonQuestion
    · split
      · intro vnew _ _ N P V hVote hNonQuestion
        exact preserve vnew N P V hVote hNonQuestion
      · intro vnew _ N P V hVote hNonQuestion
        exact preserve vnew N P V hVote hNonQuestion


@[veil]
theorem phase_rnd2_inv_27 (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (set_majority : Type) [set_majority_dec_eq : DecidableEq.{1} set_majority]
    [set_majority_inhabited : Inhabited.{1} set_majority] (set_f_plus_1 : Type)
    [set_f_plus_1_dec_eq : DecidableEq.{1} set_f_plus_1] [set_f_plus_1_inhabited : Inhabited.{1} set_f_plus_1]
    [bg : Background node set_majority set_f_plus_1] (phase : Type) [phase_dec_eq : DecidableEq.{1} phase]
    [phase_inhabited : Inhabited.{1} phase] [tot : TotalOrderWithMinimum phase] (proposal_value : Type)
    [proposal_value_dec_eq : DecidableEq.{1} proposal_value] [proposal_value_inhabited : Inhabited.{1} proposal_value]
    (state_value : Type) [state_value_dec_eq : DecidableEq.{1} state_value]
    [state_value_inhabited : Inhabited.{1} state_value] [tv : ThreeValuedType state_value] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory node set_majority set_f_plus_1 phase proposal_value state_value) ρ]
    [phase_rnd2_dec_0 :
      delta% @Rabia.phase_rnd2._veil_dec_type_0 χ node phase state_value set_majority set_f_plus_1 proposal_value χ_rep]
    [phase_rnd2_dec_1 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_1 χ phase set_majority node set_f_plus_1 bg state_value proposal_value χ_rep]
    [phase_rnd2_dec_2 : delta% @Rabia.phase_rnd2._veil_dec_type_2 phase tot]
    [phase_rnd2_dec_3 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_3 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_4 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_4 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_5 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_5 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_6 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_6 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_7 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_7 χ phase state_value tv node set_majority set_f_plus_1 proposal_value χ_rep] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@phase_rnd2.ext ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub phase_rnd2_dec_0 phase_rnd2_dec_1 phase_rnd2_dec_2 phase_rnd2_dec_3 phase_rnd2_dec_4
        phase_rnd2_dec_5 phase_rnd2_dec_6 phase_rnd2_dec_7)
      (@Assumptions ρ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv ρ_sub)
      (@Invariants ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub)
      (@inv_27 ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited set_f_plus_1
        set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  rcases hinv with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hNextVoteMembers, _⟩
  intro _ _ _ hMembers hNext
  have preserve (vnew : state_value) (P P2 : phase) (N : node) (V : state_value)
      (hNextPV : TotalOrderWithMinimum.next P P2)
      (hVoteUpdated : (n = N → psucc = P2 → ¬vnew = V) → st.vote_rnd1 N P2 V = true) :
      ∃ Q : set_majority, ∀ N : node, member_maj N Q → ∃ V, st.vote_rnd2 N P V = true := by
    by_cases hnew : n = N ∧ psucc = P2 ∧ vnew = V
    · rcases hnew with ⟨hn, hpsucc, hv⟩
      subst N
      subst P2
      subst V
      have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPV hNext
      subst P
      exact ⟨q, hMembers⟩
    · exact hNextVoteMembers P P2 N V hNextPV (hVoteUpdated (by
        grind))
  split
  · intro vnew _ _ _ _ _ P P2 N V hNextPV hVoteUpdated
    exact preserve vnew P P2 N V hNextPV hVoteUpdated
  · split
    · intro vnew _ _ _ _ P P2 N V hNextPV hVoteUpdated
      exact preserve vnew P P2 N V hNextPV hVoteUpdated
    · split
      · intro vnew _ _ P P2 N V hNextPV hVoteUpdated
        exact preserve vnew P P2 N V hNextPV hVoteUpdated
      · intro vnew _ P P2 N V hNextPV hVoteUpdated
        exact preserve vnew P P2 N V hNextPV hVoteUpdated

@[veil]
theorem phase_rnd2_inv_28 (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (set_majority : Type) [set_majority_dec_eq : DecidableEq.{1} set_majority]
    [set_majority_inhabited : Inhabited.{1} set_majority] (set_f_plus_1 : Type)
    [set_f_plus_1_dec_eq : DecidableEq.{1} set_f_plus_1] [set_f_plus_1_inhabited : Inhabited.{1} set_f_plus_1]
    [bg : Background node set_majority set_f_plus_1] (phase : Type) [phase_dec_eq : DecidableEq.{1} phase]
    [phase_inhabited : Inhabited.{1} phase] [tot : TotalOrderWithMinimum phase] (proposal_value : Type)
    [proposal_value_dec_eq : DecidableEq.{1} proposal_value] [proposal_value_inhabited : Inhabited.{1} proposal_value]
    (state_value : Type) [state_value_dec_eq : DecidableEq.{1} state_value]
    [state_value_inhabited : Inhabited.{1} state_value] [tv : ThreeValuedType state_value] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory node set_majority set_f_plus_1 phase proposal_value state_value) ρ]
    [phase_rnd2_dec_0 :
      delta% @Rabia.phase_rnd2._veil_dec_type_0 χ node phase state_value set_majority set_f_plus_1 proposal_value χ_rep]
    [phase_rnd2_dec_1 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_1 χ phase set_majority node set_f_plus_1 bg state_value proposal_value χ_rep]
    [phase_rnd2_dec_2 : delta% @Rabia.phase_rnd2._veil_dec_type_2 phase tot]
    [phase_rnd2_dec_3 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_3 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_4 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_4 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_5 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_5 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_6 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_6 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_7 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_7 χ phase state_value tv node set_majority set_f_plus_1 proposal_value χ_rep] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@phase_rnd2.ext ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub phase_rnd2_dec_0 phase_rnd2_dec_1 phase_rnd2_dec_2 phase_rnd2_dec_3 phase_rnd2_dec_4
        phase_rnd2_dec_5 phase_rnd2_dec_6 phase_rnd2_dec_7)
      (@Assumptions ρ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv ρ_sub)
      (@Invariants ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub)
      (@inv_28 ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited set_f_plus_1
        set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  rcases hinv with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hNextVoteNoCoinWitness, _⟩
  intro _ _ _ _ hNext
  split
  · intro vnew _ fpNode fpQ hfpMem hfpAll P P2 N V hNextPV hVoteUpdated hNoCoin0 hNoCoin1
    by_cases hnew : n = N ∧ psucc = P2 ∧ vnew = V
    · rcases hnew with ⟨hn, hpsucc, hv⟩
      subst N
      subst P2
      subst V
      have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPV hNext
      subst P
      exact ⟨q, fpNode, (hfpAll fpNode hfpMem).1, (hfpAll fpNode hfpMem).2⟩
    · exact hNextVoteNoCoinWitness P P2 N V hNextPV (hVoteUpdated (by
        grind)) hNoCoin0 hNoCoin1
  · split
    · intro vnew _ majNode hMaj hVote P P2 N V hNextPV hVoteUpdated hNoCoin0 hNoCoin1
      by_cases hnew : n = N ∧ psucc = P2 ∧ vnew = V
      · rcases hnew with ⟨hn, hpsucc, hv⟩
        subst N
        subst P2
        subst V
        have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPV hNext
        subst P
        exact ⟨q, majNode, hMaj, hVote⟩
      · exact hNextVoteNoCoinWitness P P2 N V hNextPV (hVoteUpdated (by
          grind)) hNoCoin0 hNoCoin1
    · split
      · intro vnew hNonQuestion hCoin P P2 N V hNextPV hVoteUpdated hNoCoin0 hNoCoin1
        by_cases hnew : n = N ∧ psucc = P2 ∧ vnew = V
        · rcases hnew with ⟨hn, hpsucc, hv⟩
          subst N
          subst P2
          subst V
          have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPV hNext
          subst P
          exfalso
          have hvnewCases := ThreeValuedType.ax4 vnew
          grind
        · exact hNextVoteNoCoinWitness P P2 N V hNextPV (hVoteUpdated (by
            grind)) hNoCoin0 hNoCoin1
      · intro vnew hNonQuestion P P2 N V hNextPV hVoteUpdated hNoCoin0Guard hNoCoin0 hNoCoin1Guard hNoCoin1
        by_cases hnew : n = N ∧ psucc = P2 ∧ vnew = V
        · rcases hnew with ⟨hn, hpsucc, hv⟩
          subst N
          subst P2
          subst V
          have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPV hNext
          subst P
          exfalso
          have hvnewCases := ThreeValuedType.ax4 vnew
          grind
        · exact hNextVoteNoCoinWitness P P2 N V hNextPV (hVoteUpdated (by
            grind)) hNoCoin0 hNoCoin1

@[veil]
theorem phase_rnd2_vote_rnd1_pred_rnd (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (set_majority : Type) [set_majority_dec_eq : DecidableEq.{1} set_majority]
    [set_majority_inhabited : Inhabited.{1} set_majority] (set_f_plus_1 : Type)
    [set_f_plus_1_dec_eq : DecidableEq.{1} set_f_plus_1] [set_f_plus_1_inhabited : Inhabited.{1} set_f_plus_1]
    [bg : Background node set_majority set_f_plus_1] (phase : Type) [phase_dec_eq : DecidableEq.{1} phase]
    [phase_inhabited : Inhabited.{1} phase] [tot : TotalOrderWithMinimum phase] (proposal_value : Type)
    [proposal_value_dec_eq : DecidableEq.{1} proposal_value] [proposal_value_inhabited : Inhabited.{1} proposal_value]
    (state_value : Type) [state_value_dec_eq : DecidableEq.{1} state_value]
    [state_value_inhabited : Inhabited.{1} state_value] [tv : ThreeValuedType state_value] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory node set_majority set_f_plus_1 phase proposal_value state_value) ρ]
    [phase_rnd2_dec_0 :
      delta% @Rabia.phase_rnd2._veil_dec_type_0 χ node phase state_value set_majority set_f_plus_1 proposal_value χ_rep]
    [phase_rnd2_dec_1 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_1 χ phase set_majority node set_f_plus_1 bg state_value proposal_value χ_rep]
    [phase_rnd2_dec_2 : delta% @Rabia.phase_rnd2._veil_dec_type_2 phase tot]
    [phase_rnd2_dec_3 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_3 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_4 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_4 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_5 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_5 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_6 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_6 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_7 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_7 χ phase state_value tv node set_majority set_f_plus_1 proposal_value χ_rep] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@phase_rnd2.ext ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub phase_rnd2_dec_0 phase_rnd2_dec_1 phase_rnd2_dec_2 phase_rnd2_dec_3 phase_rnd2_dec_4
        phase_rnd2_dec_5 phase_rnd2_dec_6 phase_rnd2_dec_7)
      (@Assumptions ρ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv ρ_sub)
      (@Invariants ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub)
      (@vote_rnd1_pred_rnd ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  rcases hinv with
    ⟨_, _, _, _, _, _, _, _, _, _, hInPhaseVote, _, _, hVoteRnd1NonQuestion, _, _, _,
      hVoteRnd2NonQuestionVoteRnd1, _, _, _, _, _, _, _, _, _, _, _, hVotePred, _, _, _, hLockedWitness,
      hLockedNoCoin, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro hinPhase _ _ hMembers hNext
  have pred_from_vote (vnew : state_value) (hNonQuestion : ¬vnew = ThreeValuedType.vquestion)
      (Nvote : node) (hVote : st.vote_rnd2 Nvote p vnew = true) :
      ∃ N2 : node, st.vote_rnd1 N2 p vnew = true := by
    obtain ⟨Q, hQ⟩ := hVoteRnd2NonQuestionVoteRnd1 Nvote p vnew hVote hNonQuestion
    obtain ⟨w, hwQ, _⟩ := Background.ax0 Q q
    exact ⟨w, hQ w hwQ⟩
  have pred_from_forbidden_lock (vnew : state_value) (hNonQuestion : ¬vnew = ThreeValuedType.vquestion)
      (hForbid :
        ∀ V : state_value,
          (∀ (N : node) (Valt : state_value), st.vote_rnd1 N p Valt = true → Valt = V) → False) :
      ∃ N2 : node, st.vote_rnd1 N2 p vnew = true := by
    by_cases hPred : ∃ N2 : node, st.vote_rnd1 N2 p vnew = true
    · exact hPred
    · exfalso
      obtain ⟨V0, hVote0⟩ := hInPhaseVote n p hinPhase
      have hV0NonQuestion : ¬V0 = ThreeValuedType.vquestion := hVoteRnd1NonQuestion n p V0 hVote0
      have hV0Ne : V0 ≠ vnew := by
        intro hEq
        have hVoteNew : st.vote_rnd1 n p vnew = true := by
          rw [← hEq]
          exact hVote0
        exact hPred ⟨n, hVoteNew⟩
      have hLocked :
          ∀ (N : node) (Valt : state_value), st.vote_rnd1 N p Valt = true → Valt = V0 := by
        intro N Valt hVote
        by_cases hValEq : Valt = vnew
        · have hVoteNew : st.vote_rnd1 N p vnew = true := by
            rw [← hValEq]
            exact hVote
          exact False.elim (hPred ⟨N, hVoteNew⟩)
        · exact ThreeValuedType.eq_of_ne_question_of_ne_same
            (hVoteRnd1NonQuestion N p Valt hVote) hV0NonQuestion hValEq hV0Ne hNonQuestion
      exact hForbid V0 hLocked
  have preserve (vnew : state_value)
      (hNewPred : ∃ N2 : node, st.vote_rnd1 N2 p vnew = true)
      (N1 : node) (P2 : phase) (V1 : state_value) (P : phase)
      (hVoteUpdated : (n = N1 → psucc = P2 → ¬vnew = V1) → st.vote_rnd1 N1 P2 V1 = true)
      (hNextPP2 : TotalOrderWithMinimum.next P P2) :
      ∃ N2 : node, (n = N2 → psucc = P → ¬vnew = V1) → st.vote_rnd1 N2 P V1 = true := by
    by_cases hnew : n = N1 ∧ psucc = P2 ∧ vnew = V1
    · rcases hnew with ⟨hn, hpsucc, hv⟩
      subst N1
      subst P2
      subst V1
      have hP : P = p := TotalOrderWithMinimum.prev_unique hNextPP2 hNext
      subst P
      obtain ⟨N2, hPred⟩ := hNewPred
      exact ⟨N2, fun _ => hPred⟩
    · obtain ⟨N2, hPred⟩ := hVotePred N1 P2 V1 P (hVoteUpdated (by
        grind)) hNextPP2
      exact ⟨N2, fun _ => hPred⟩
  split
  · intro vnew hNonQuestion fpNode fpQ hfpMem hfpAll N1 P2 V1 P hVoteUpdated hNextPP2
    exact preserve vnew (pred_from_vote vnew hNonQuestion fpNode ((hfpAll fpNode hfpMem).2))
      N1 P2 V1 P hVoteUpdated hNextPP2
  · rename_i hNoDecision
    split
    · intro vnew hNonQuestion majNode hMaj hVote N1 P2 V1 P hVoteUpdated hNextPP2
      exact preserve vnew (pred_from_vote vnew hNonQuestion majNode hVote)
        N1 P2 V1 P hVoteUpdated hNextPP2
    · rename_i hNoMajVote
      split
      · intro vnew hNonQuestion hCoin N1 P2 V1 P hVoteUpdated hNextPP2
        have hNewPred := pred_from_forbidden_lock vnew hNonQuestion (by
          intro V hLocked
          have hNoCoin := hLockedNoCoin p V vnew hLocked q hMembers
          simp [hCoin] at hNoCoin)
        exact preserve vnew hNewPred N1 P2 V1 P hVoteUpdated hNextPP2
      · intro vnew hNonQuestion N1 P2 V1 P hVoteUpdated hNextPP2
        have hNewPred := pred_from_forbidden_lock vnew hNonQuestion (by
          intro V hLocked
          obtain ⟨w, hwMem, hwVote⟩ := hLockedWitness p V hLocked q hMembers
          have hVNonQuestion : ¬V = ThreeValuedType.vquestion := by
            obtain ⟨V0, hVote0⟩ := hInPhaseVote n p hinPhase
            have hEq : V0 = V := hLocked n V0 hVote0
            intro hVQuestion
            exact hVoteRnd1NonQuestion n p V0 hVote0 (hEq.trans hVQuestion)
          exact hNoMajVote ⟨V, hVNonQuestion, ⟨w, hwMem, hwVote⟩⟩)
        exact preserve vnew hNewPred N1 P2 V1 P hVoteUpdated hNextPP2

@[veil]
theorem phase_rnd2_inv_34 (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (set_majority : Type) [set_majority_dec_eq : DecidableEq.{1} set_majority]
    [set_majority_inhabited : Inhabited.{1} set_majority] (set_f_plus_1 : Type)
    [set_f_plus_1_dec_eq : DecidableEq.{1} set_f_plus_1] [set_f_plus_1_inhabited : Inhabited.{1} set_f_plus_1]
    [bg : Background node set_majority set_f_plus_1] (phase : Type) [phase_dec_eq : DecidableEq.{1} phase]
    [phase_inhabited : Inhabited.{1} phase] [tot : TotalOrderWithMinimum phase] (proposal_value : Type)
    [proposal_value_dec_eq : DecidableEq.{1} proposal_value] [proposal_value_inhabited : Inhabited.{1} proposal_value]
    (state_value : Type) [state_value_dec_eq : DecidableEq.{1} state_value]
    [state_value_inhabited : Inhabited.{1} state_value] [tv : ThreeValuedType state_value] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory node set_majority set_f_plus_1 phase proposal_value state_value) ρ]
    [phase_rnd2_dec_0 :
      delta% @Rabia.phase_rnd2._veil_dec_type_0 χ node phase state_value set_majority set_f_plus_1 proposal_value χ_rep]
    [phase_rnd2_dec_1 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_1 χ phase set_majority node set_f_plus_1 bg state_value proposal_value χ_rep]
    [phase_rnd2_dec_2 : delta% @Rabia.phase_rnd2._veil_dec_type_2 phase tot]
    [phase_rnd2_dec_3 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_3 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_4 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_4 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_5 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_5 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_6 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_6 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_7 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_7 χ phase state_value tv node set_majority set_f_plus_1 proposal_value χ_rep] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@phase_rnd2.ext ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub phase_rnd2_dec_0 phase_rnd2_dec_1 phase_rnd2_dec_2 phase_rnd2_dec_3 phase_rnd2_dec_4
        phase_rnd2_dec_5 phase_rnd2_dec_6 phase_rnd2_dec_7)
      (@Assumptions ρ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv ρ_sub)
      (@Invariants ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub)
      (@inv_34 ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited set_f_plus_1
        set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  rcases hinv with
    ⟨_, _, _, _, _, _, _, _, _, _, hInPhaseVote, _, _, hVoteRnd1NonQuestion, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, hLockedWitness, hLockedNoCoin, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro hinPhase _ _ hMembers hNext
  split
  · intro vnew _ _ _ _ _ P V V2 hLocked Q hMembersP
    exact hLockedNoCoin P V V2 (by
      intro N Valt hVote
      exact hLocked N Valt (fun _ => hVote)) Q hMembersP
  · rename_i hNoDecision
    split
    · intro vnew _ _ _ _ P V V2 hLocked Q hMembersP
      exact hLockedNoCoin P V V2 (by
        intro N Valt hVote
        exact hLocked N Valt (fun _ => hVote)) Q hMembersP
    · rename_i hNoMajVote
      split
      · intro vnew _ _ P V V2 hLocked Q hMembersP
        exact hLockedNoCoin P V V2 (by
          intro N Valt hVote
          exact hLocked N Valt (fun _ => hVote)) Q hMembersP
      · intro vnew _ P V V2 hLocked Q hMembersP
        constructor
        · intro hp _
          have hLockedOld :
              ∀ (N : node) (Valt : state_value), st.vote_rnd1 N P Valt = true → Valt = V := by
            intro N Valt hVote
            exact hLocked N Valt (fun _ => hVote)
          have hMembersAtP :
              ∀ (N : node), member_maj N q → ∃ V, st.vote_rnd2 N P V = true := by
            intro N hMem
            rw [← hp]
            exact hMembers N hMem
          obtain ⟨V0, hVote0⟩ := hInPhaseVote n p hinPhase
          have hVote0P : st.vote_rnd1 n P V0 = true := by
            rw [← hp]
            exact hVote0
          have hV0Eq : V0 = V := hLockedOld n V0 hVote0P
          have hVNonQuestion : ¬V = ThreeValuedType.vquestion := by
            intro hVQuestion
            exact hVoteRnd1NonQuestion n p V0 hVote0 (hV0Eq.trans hVQuestion)
          obtain ⟨N, hNMem, hNRnd2⟩ := hLockedWitness P V hLockedOld q hMembersAtP
          apply hNoMajVote
          exact ⟨V, hVNonQuestion, ⟨N, hNMem, by
            rw [hp]
            exact hNRnd2⟩⟩
        · exact hLockedNoCoin P V V2 (by
            intro N Valt hVote
            exact hLocked N Valt (fun _ => hVote)) Q hMembersP

@[veil]
theorem phase_rnd2_inv_33 (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (set_majority : Type) [set_majority_dec_eq : DecidableEq.{1} set_majority]
    [set_majority_inhabited : Inhabited.{1} set_majority] (set_f_plus_1 : Type)
    [set_f_plus_1_dec_eq : DecidableEq.{1} set_f_plus_1] [set_f_plus_1_inhabited : Inhabited.{1} set_f_plus_1]
    [bg : Background node set_majority set_f_plus_1] (phase : Type) [phase_dec_eq : DecidableEq.{1} phase]
    [phase_inhabited : Inhabited.{1} phase] [tot : TotalOrderWithMinimum phase] (proposal_value : Type)
    [proposal_value_dec_eq : DecidableEq.{1} proposal_value] [proposal_value_inhabited : Inhabited.{1} proposal_value]
    (state_value : Type) [state_value_dec_eq : DecidableEq.{1} state_value]
    [state_value_inhabited : Inhabited.{1} state_value] [tv : ThreeValuedType state_value] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory node set_majority set_f_plus_1 phase proposal_value state_value) ρ]
    [phase_rnd2_dec_0 :
      delta% @Rabia.phase_rnd2._veil_dec_type_0 χ node phase state_value set_majority set_f_plus_1 proposal_value χ_rep]
    [phase_rnd2_dec_1 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_1 χ phase set_majority node set_f_plus_1 bg state_value proposal_value χ_rep]
    [phase_rnd2_dec_2 : delta% @Rabia.phase_rnd2._veil_dec_type_2 phase tot]
    [phase_rnd2_dec_3 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_3 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_4 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_4 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_5 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_5 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_6 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_6 χ phase set_majority state_value tv node set_f_plus_1 bg proposal_value
          χ_rep]
    [phase_rnd2_dec_7 :
      delta%
        @Rabia.phase_rnd2._veil_dec_type_7 χ phase state_value tv node set_majority set_f_plus_1 proposal_value χ_rep] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@phase_rnd2.ext ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub phase_rnd2_dec_0 phase_rnd2_dec_1 phase_rnd2_dec_2 phase_rnd2_dec_3 phase_rnd2_dec_4
        phase_rnd2_dec_5 phase_rnd2_dec_6 phase_rnd2_dec_7)
      (@Assumptions ρ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv ρ_sub)
      (@Invariants ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub)
      (@inv_33 ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited set_f_plus_1
        set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  rcases hinv with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hLockedWitness, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro _ _ _ _ _
  split
  · intro vnew _ _ _ _ _ P V hLocked Q hMembersP
    exact hLockedWitness P V (by
      intro N Valt hVote
      exact hLocked N Valt (fun _ => hVote)) Q hMembersP
  · split
    · intro vnew _ _ _ _ P V hLocked Q hMembersP
      exact hLockedWitness P V (by
        intro N Valt hVote
        exact hLocked N Valt (fun _ => hVote)) Q hMembersP
    · split
      · intro vnew _ _ P V hLocked Q hMembersP
        exact hLockedWitness P V (by
          intro N Valt hVote
          exact hLocked N Valt (fun _ => hVote)) Q hMembersP
      · intro vnew _ P V hLocked Q hMembersP
        exact hLockedWitness P V (by
          intro N Valt hVote
          exact hLocked N Valt (fun _ => hVote)) Q hMembersP


@[veil]
theorem initial_proposal_good_succ_good (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (set_majority : Type) [set_majority_dec_eq : DecidableEq.{1} set_majority]
    [set_majority_inhabited : Inhabited.{1} set_majority] (set_f_plus_1 : Type)
    [set_f_plus_1_dec_eq : DecidableEq.{1} set_f_plus_1] [set_f_plus_1_inhabited : Inhabited.{1} set_f_plus_1]
    [bg : Background node set_majority set_f_plus_1] (phase : Type) [phase_dec_eq : DecidableEq.{1} phase]
    [phase_inhabited : Inhabited.{1} phase] [tot : TotalOrderWithMinimum phase] (proposal_value : Type)
    [proposal_value_dec_eq : DecidableEq.{1} proposal_value] [proposal_value_inhabited : Inhabited.{1} proposal_value]
    (state_value : Type) [state_value_dec_eq : DecidableEq.{1} state_value]
    [state_value_inhabited : Inhabited.{1} state_value] [tv : ThreeValuedType state_value] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory node set_majority set_f_plus_1 phase proposal_value state_value) ρ]
    [initial_proposal_dec_0 :
      delta%
        @Rabia.initial_proposal._veil_dec_type_0 χ node proposal_value set_majority set_f_plus_1 phase state_value
          χ_rep]
    [initial_proposal_dec_1 :
      delta%
        @Rabia.initial_proposal._veil_dec_type_1 χ node phase state_value set_majority set_f_plus_1 proposal_value
          χ_rep]
    [initial_proposal_dec_2 :
      delta%
        @Rabia.initial_proposal._veil_dec_type_2 χ node phase state_value set_majority set_f_plus_1 proposal_value
          χ_rep]
    [initial_proposal_dec_3 :
      delta%
        @Rabia.initial_proposal._veil_dec_type_3 χ node phase state_value set_majority set_f_plus_1 proposal_value
          χ_rep]
    [initial_proposal_dec_4 :
      delta%
        @Rabia.initial_proposal._veil_dec_type_4 χ node phase set_majority set_f_plus_1 proposal_value state_value
          χ_rep] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@initial_proposal.ext ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub initial_proposal_dec_0 initial_proposal_dec_1 initial_proposal_dec_2
        initial_proposal_dec_3 initial_proposal_dec_4)
      (@Assumptions ρ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv ρ_sub)
      (@Invariants ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub)
      (@good_succ_good ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  rcases hinv with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, hGoodSucc, _, _, _, _, _⟩
  intro _ _ _ _ _
  exact hGoodSucc


@[veil]
theorem initial_vote1_good_succ_good (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (set_majority : Type) [set_majority_dec_eq : DecidableEq.{1} set_majority]
    [set_majority_inhabited : Inhabited.{1} set_majority] (set_f_plus_1 : Type)
    [set_f_plus_1_dec_eq : DecidableEq.{1} set_f_plus_1] [set_f_plus_1_inhabited : Inhabited.{1} set_f_plus_1]
    [bg : Background node set_majority set_f_plus_1] (phase : Type) [phase_dec_eq : DecidableEq.{1} phase]
    [phase_inhabited : Inhabited.{1} phase] [tot : TotalOrderWithMinimum phase] (proposal_value : Type)
    [proposal_value_dec_eq : DecidableEq.{1} proposal_value] [proposal_value_inhabited : Inhabited.{1} proposal_value]
    (state_value : Type) [state_value_dec_eq : DecidableEq.{1} state_value]
    [state_value_inhabited : Inhabited.{1} state_value] [tv : ThreeValuedType state_value] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory node set_majority set_f_plus_1 phase proposal_value state_value) ρ]
    [initial_vote1_dec_0 :
      delta%
        @Rabia.initial_vote1._veil_dec_type_0 χ node proposal_value set_majority set_f_plus_1 phase state_value χ_rep]
    [initial_vote1_dec_1 :
      delta%
        @Rabia.initial_vote1._veil_dec_type_1 χ node phase state_value set_majority set_f_plus_1 proposal_value χ_rep]
    [initial_vote1_dec_2 :
      delta%
        @Rabia.initial_vote1._veil_dec_type_2 χ node phase state_value set_majority set_f_plus_1 proposal_value χ_rep]
    [initial_vote1_dec_3 :
      delta%
        @Rabia.initial_vote1._veil_dec_type_3 χ node phase state_value set_majority set_f_plus_1 proposal_value χ_rep]
    [initial_vote1_dec_4 :
      delta%
        @Rabia.initial_vote1._veil_dec_type_4 χ node phase set_majority set_f_plus_1 proposal_value state_value χ_rep]
    [initial_vote1_dec_5 :
      delta%
        @Rabia.initial_vote1._veil_dec_type_5 χ set_majority proposal_value node set_f_plus_1 bg phase state_value
          χ_rep]
    [initial_vote1_dec_6 :
      delta%
        @Rabia.initial_vote1._veil_dec_type_6 χ set_majority proposal_value node set_f_plus_1 bg phase state_value
          χ_rep] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@initial_vote1.ext ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub initial_vote1_dec_0 initial_vote1_dec_1 initial_vote1_dec_2 initial_vote1_dec_3
        initial_vote1_dec_4 initial_vote1_dec_5 initial_vote1_dec_6)
      (@Assumptions ρ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv ρ_sub)
      (@Invariants ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub)
      (@good_succ_good ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  rcases hinv with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, hDecisionNextLocked, _, _, _, _, hLockedNext, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have no_next_to_zero :
      ∀ {P P2 : phase}, TotalOrderWithMinimum.next P P2 → TotalOrderWithMinimum.zero ≠ P2 := by
    intro P P2 hNext hZero
    have hLtP2 : TotalOrderWithMinimum.lt P P2 :=
      ((TotalOrderWithMinimum.next_def P P2).mp hNext).1
    have hLtZero : TotalOrderWithMinimum.lt P TotalOrderWithMinimum.zero := by
      rw [← hZero] at hLtP2
      exact hLtP2
    have hLeAndNe := (TotalOrderWithMinimum.le_lt P TotalOrderWithMinimum.zero).mp hLtZero
    have hZeroLeP : TotalOrderWithMinimum.le TotalOrderWithMinimum.zero P :=
      TotalOrderWithMinimum.zero_lt P
    have hEq : P = TotalOrderWithMinimum.zero :=
      TotalOrderWithMinimum.le_antisymm P TotalOrderWithMinimum.zero hLeAndNe.1 hZeroLeP
    exact hLeAndNe.2 hEq
  intro _ _ _ _ _ _
  split
  · intro _ _ P P2 x x_1 hStartP hPreds hLocks hNext xP2 x_2 hStartP2
    have hP2NeZero : TotalOrderWithMinimum.zero ≠ P2 := no_next_to_zero hNext
    constructor
    · exact ⟨xP2, x_2, hStartP2⟩
    constructor
    · intro P0 hLtP0P2
      rcases TotalOrderWithMinimum.eq_or_lt_of_lt_next hNext hLtP0P2 with hP0Eq | hLtP0P
      · subst P0
        exact ⟨x, x_1, hStartP⟩
      · exact hPreds P0 hLtP0P
    · intro P0 V0 hLtP0P2 x0 x_3 hStartP0 hReason N Valt hVoteP2
      have hOldVoteP2 : st.vote_rnd1 N P2 Valt = true := hVoteP2 (by
        intro _ hZeroEq
        exact False.elim (hP2NeZero hZeroEq))
      rcases TotalOrderWithMinimum.eq_or_lt_of_lt_next hNext hLtP0P2 with hP0Eq | hLtP0P
      · subst P0
        rcases hReason with hDecision | hLockP
        · rcases hDecision with ⟨Ndec, hDecision⟩
          exact hDecisionNextLocked Ndec P V0 P2 hDecision hNext N Valt hOldVoteP2
        · have hOldLockP :
              ∀ (N : node) (Valt : state_value), st.vote_rnd1 N P Valt = true → Valt = V0 := by
            intro N' V' hOldVote
            exact hLockP N' V' (by
              intro _
              exact hOldVote)
          exact hLockedNext P V0 P2 hOldLockP hNext N Valt hOldVoteP2
      · have hLockP := hLocks P0 V0 hLtP0P x0 x_3 hStartP0 hReason
        have hOldLockP :
            ∀ (N : node) (Valt : state_value), st.vote_rnd1 N P Valt = true → Valt = V0 := by
          intro N' V' hOldVote
          exact hLockP N' V' (by
            intro _
            exact hOldVote)
        exact hLockedNext P V0 P2 hOldLockP hNext N Valt hOldVoteP2
  · intro P P2 x x_1 hStartP hPreds hLocks hNext xP2 x_2 hStartP2
    have hP2NeZero : TotalOrderWithMinimum.zero ≠ P2 := no_next_to_zero hNext
    constructor
    · exact ⟨xP2, x_2, hStartP2⟩
    constructor
    · intro P0 hLtP0P2
      rcases TotalOrderWithMinimum.eq_or_lt_of_lt_next hNext hLtP0P2 with hP0Eq | hLtP0P
      · subst P0
        exact ⟨x, x_1, hStartP⟩
      · exact hPreds P0 hLtP0P
    · intro P0 V0 hLtP0P2 x0 x_3 hStartP0 hReason N Valt hVoteP2
      have hOldVoteP2 : st.vote_rnd1 N P2 Valt = true := hVoteP2 (by
        intro _ hZeroEq
        exact False.elim (hP2NeZero hZeroEq))
      rcases TotalOrderWithMinimum.eq_or_lt_of_lt_next hNext hLtP0P2 with hP0Eq | hLtP0P
      · subst P0
        rcases hReason with hDecision | hLockP
        · rcases hDecision with ⟨Ndec, hDecision⟩
          exact hDecisionNextLocked Ndec P V0 P2 hDecision hNext N Valt hOldVoteP2
        · have hOldLockP :
              ∀ (N : node) (Valt : state_value), st.vote_rnd1 N P Valt = true → Valt = V0 := by
            intro N' V' hOldVote
            exact hLockP N' V' (by
              intro _
              exact hOldVote)
          exact hLockedNext P V0 P2 hOldLockP hNext N Valt hOldVoteP2
      · have hLockP := hLocks P0 V0 hLtP0P x0 x_3 hStartP0 hReason
        have hOldLockP :
            ∀ (N : node) (Valt : state_value), st.vote_rnd1 N P Valt = true → Valt = V0 := by
          intro N' V' hOldVote
          exact hLockP N' V' (by
            intro _
            exact hOldVote)
        exact hLockedNext P V0 P2 hOldLockP hNext N Valt hOldVoteP2


@[veil]
theorem phase_rnd1_inv_33 (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (set_majority : Type) [set_majority_dec_eq : DecidableEq.{1} set_majority]
    [set_majority_inhabited : Inhabited.{1} set_majority] (set_f_plus_1 : Type)
    [set_f_plus_1_dec_eq : DecidableEq.{1} set_f_plus_1] [set_f_plus_1_inhabited : Inhabited.{1} set_f_plus_1]
    [bg : Background node set_majority set_f_plus_1] (phase : Type) [phase_dec_eq : DecidableEq.{1} phase]
    [phase_inhabited : Inhabited.{1} phase] [tot : TotalOrderWithMinimum phase] (proposal_value : Type)
    [proposal_value_dec_eq : DecidableEq.{1} proposal_value] [proposal_value_inhabited : Inhabited.{1} proposal_value]
    (state_value : Type) [state_value_dec_eq : DecidableEq.{1} state_value]
    [state_value_inhabited : Inhabited.{1} state_value] [tv : ThreeValuedType state_value] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation
          (State.Label.toDomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f)
          (State.Label.toCodomain node set_majority set_f_plus_1 phase proposal_value state_value __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory node set_majority set_f_plus_1 phase proposal_value state_value) ρ]
    [phase_rnd1_dec_0 :
      delta% @Rabia.phase_rnd1._veil_dec_type_0 χ node phase state_value set_majority set_f_plus_1 proposal_value χ_rep]
    [phase_rnd1_dec_1 :
      delta%
        @Rabia.phase_rnd1._veil_dec_type_1 χ phase set_majority node set_f_plus_1 bg state_value proposal_value χ_rep]
    [phase_rnd1_dec_2 :
      delta%
        @Rabia.phase_rnd1._veil_dec_type_2 χ phase set_majority state_value node set_f_plus_1 bg proposal_value χ_rep]
    [phase_rnd1_dec_3 :
      delta%
        @Rabia.phase_rnd1._veil_dec_type_3 χ phase set_majority state_value node set_f_plus_1 bg proposal_value χ_rep] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@phase_rnd1.ext ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub phase_rnd1_dec_0 phase_rnd1_dec_1 phase_rnd1_dec_2 phase_rnd1_dec_3)
      (@Assumptions ρ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv ρ_sub)
      (@Invariants ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited
        set_f_plus_1 set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub)
      (@inv_33 ρ σ node node_dec_eq node_inhabited set_majority set_majority_dec_eq set_majority_inhabited set_f_plus_1
        set_f_plus_1_dec_eq set_f_plus_1_inhabited bg phase phase_dec_eq phase_inhabited tot proposal_value
        proposal_value_dec_eq proposal_value_inhabited state_value state_value_dec_eq state_value_inhabited tv χ χ_rep
        χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  rcases hinv with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hLockedWitness, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro _ _ hMajVoteRnd1
  split
  · intro vnew hUniform P V hLocked Q hMembersUpdated
    by_cases hp : p = P
    · have hNewEq : vnew = V := by
        obtain ⟨w, hwMem, _⟩ := Background.ax0 q q
        exact hLocked w vnew (by
          rw [← hp]
          exact hUniform w hwMem)
      by_cases hnQ : member_maj n Q
      · exact ⟨n, hnQ, by
          intro hUpdated
          exact False.elim ((hUpdated rfl hp) hNewEq)⟩
      · have hOldMembers :
            ∀ (N : node), member_maj N Q → ∃ V, st.vote_rnd2 N P V = true := by
          intro N hNQ
          obtain ⟨Valt, hVoteUpdated⟩ := hMembersUpdated N hNQ
          exact ⟨Valt, hVoteUpdated (by
            intro hn _ _
            have hnMem : member_maj n Q := by
              rw [hn]
              exact hNQ
            exact hnQ hnMem)⟩
        obtain ⟨w, hwMem, hwVote⟩ := hLockedWitness P V hLocked Q hOldMembers
        exact ⟨w, hwMem, fun _ => hwVote⟩
    · have hOldMembers :
          ∀ (N : node), member_maj N Q → ∃ V, st.vote_rnd2 N P V = true := by
        intro N hNQ
        obtain ⟨Valt, hVoteUpdated⟩ := hMembersUpdated N hNQ
        exact ⟨Valt, hVoteUpdated (by
          intro _ hpEq _
          exact hp hpEq)⟩
      obtain ⟨w, hwMem, hwVote⟩ := hLockedWitness P V hLocked Q hOldMembers
      exact ⟨w, hwMem, fun _ => hwVote⟩
  · rename_i hNoUniform
    intro P V hLocked Q hMembersUpdated
    by_cases hp : p = P
    · exfalso
      exact hNoUniform ⟨V, by
        intro N hNq
        obtain ⟨Valt, hVote⟩ := hMajVoteRnd1 N hNq
        have hValtEq : Valt = V := hLocked N Valt (by
          rw [← hp]
          exact hVote)
        rw [← hValtEq]
        exact hVote⟩
    · have hOldMembers :
          ∀ (N : node), member_maj N Q → ∃ V, st.vote_rnd2 N P V = true := by
        intro N hNQ
        obtain ⟨Valt, hVoteUpdated⟩ := hMembersUpdated N hNQ
        exact ⟨Valt, hVoteUpdated (by
          intro _ hpEq _
          exact hp hpEq)⟩
      obtain ⟨w, hwMem, hwVote⟩ := hLockedWitness P V hLocked Q hOldMembers
      exact ⟨w, hwMem, fun _ => hwVote⟩

#check_invariants
#gen_theorems


end Rabia
