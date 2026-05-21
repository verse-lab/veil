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

#time #check_invariants Protocol


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
  rename_i n p psucc
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
              ∀ (N : node), member_maj N t → ∃ V, st.vote_rnd2 N P V = true := by
            intro N hMem
            simpa [← hp] using hMembers N hMem
          obtain ⟨V0, hVote0⟩ := hInPhaseVote n p hinPhase
          have hVote0P : st.vote_rnd1 n P V0 = true := by
            simpa [← hp] using hVote0
          have hV0Eq : V0 = V := hLockedOld n V0 hVote0P
          have hVNonQuestion : ¬V = ThreeValuedType.vquestion := by
            simpa [hV0Eq] using hVoteRnd1NonQuestion n p V0 hVote0
          obtain ⟨N, hNMem, hNRnd2⟩ := hLockedWitness P V hLockedOld t hMembersAtP
          apply hNoMajVote
          exact ⟨V, hVNonQuestion, ⟨N, hNMem, by simpa [← hp] using hNRnd2⟩⟩
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
  rename_i n p psucc
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

#gen_theorems

end Rabia
