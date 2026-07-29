import Veil

-- https://www.wisdom.weizmann.ac.il/~padon/paxos-made-epr-examples.zip /vertical_paxos/vertical_paxos_fol.ivy

veil module VerticalPaxosFirstOrder

type node
type value
type quorum
type round
type config

individual none : value
instantiate tot : TotalOrder round

immutable relation member (N : node) (Q : quorum)
immutable relation quorumin (Q : quorum) (C : config)

relation one_a (R1 : round) (R2 : round)
relation join_ack_msg (N : node) (R1 : round) (R2 : round) (V : value)
relation proposal (R : round) (V : value)
relation vote (N : node) (R : round) (V : value)
relation decision (N : node) (R : round) (V : value)
relation configure_round_msg (R : round) (C : config)
relation complete_msg (R : round)
function complete_of (C : config) : round
function quorum_of_round (R : round) : quorum
individual master_complete : round

#gen_state

assumption ∀ (c : config) (q1 : quorum) (q2 : quorum),
  quorumin q1 c ∧ quorumin q2 c → ∃ (n : node), member n q1 ∧ member n q2

after_init {
  one_a R1 R2 := false
  join_ack_msg N R1 R2 V := false
  proposal R V := false
  vote N R V := false
  decision N R V := false
  configure_round_msg R C := false
  complete_msg R := false
  require ∀ R, tot.le master_complete R
}

-- Master actions.
action configure_round (r : round) (c : config) {
  require ∀ C, ¬ configure_round_msg r C
  require tot.le master_complete r
  require complete_of c = master_complete

  configure_round_msg r c := true
}

action mark_complete (r : round) {
  require complete_msg r
  if ¬ tot.le r master_complete then
    master_complete := r
}

-- Node actions.
action send_1a (r : round) (c : config) (cr : round) {
  require configure_round_msg r c
  require cr = complete_of c
  one_a r R := decide $ one_a r R ∨ (tot.le cr R ∧ ¬ tot.le r R)
}

action join_round (n : node) (r : round) (rp : round) {
  require one_a r rp
  require ¬ (∃ (r' : round) (rp' : round) (v : value),
    join_ack_msg n r' rp' v ∧ ¬ tot.le r' r)
  let mut v : value ← pick
  if ∀ V, ¬ vote n rp V then
    v := none
  else
    require vote n rp v
  join_ack_msg n r rp v := true
}

action propose (r : round) (c : config) (cr : round) {
  quorum_of_round R := *
  require configure_round_msg r c
  require complete_of c = cr
  require ∀ V, ¬ proposal r V
  require ∀ R, tot.le cr R ∧ ¬ tot.le r R → ∃ c, configure_round_msg R c
  require ∀ R C, tot.le cr R ∧ ¬ tot.le r R ∧ configure_round_msg R C →
    quorumin (quorum_of_round R) C
  require ∀ R N, tot.le cr R ∧ ¬ tot.le r R ∧ member N (quorum_of_round R) →
    ∃ v, join_ack_msg N r R v
  let v : value ← pick
  let maxr : round ← pick
  assume
    (v = none ∧
        ∀ (N : node) (MAXR : round) (V : value),
          ¬ (tot.le cr MAXR ∧ ¬ tot.le r MAXR ∧ member N (quorum_of_round MAXR)) ∧
            join_ack_msg N r MAXR V ∧ V ≠ none) ∨
      (v ≠ none ∧
        (∃ (N : node),
          tot.le cr maxr ∧ ¬ tot.le r maxr ∧ member N (quorum_of_round maxr) ∧
            join_ack_msg N r maxr v ∧ v ≠ none) ∧
        (∀ (N : node) (MAXR : round) (V : value),
          (tot.le cr MAXR ∧ ¬ tot.le r MAXR ∧ member N (quorum_of_round MAXR) ∧
            join_ack_msg N r MAXR V ∧ V ≠ none) → tot.le MAXR maxr))
  if v = none then
    let proposedValue : value ← pick
    require proposedValue ≠ none
    complete_msg r := true
    proposal r proposedValue := true
  else
    proposal r v := true
}

action cast_vote (n : node) (v : value) (r : round) {
  require v ≠ none
  require ¬ (∃ (r' : round) (rp : round) (v' : value),
    join_ack_msg n r' rp v' ∧ ¬ tot.le r' r)
  require proposal r v
  vote n r v := true
}

action decide (n : node) (r : round) (c : config) (v : value) (q : quorum) {
  require v ≠ none
  require configure_round_msg r c
  require quorumin q c
  require ∀ N, member N q → vote N r v
  decision n r v := true
  complete_msg r := true
}

safety [coherence] decision N1 R1 V1 ∧ decision N2 R2 V2 → V1 = V2

invariant [proposal_unique] proposal R V1 ∧ proposal R V2 → V1 = V2

invariant [unique_config] configure_round_msg R C1 ∧ configure_round_msg R C2 → C1 = C2

invariant [property1_one_a] one_a R RP → ¬ tot.le R RP
invariant [property2_one_a] one_a R RP → ∃ c, configure_round_msg R c

invariant [only_vote_proposed] vote N R V → proposal R V

invariant [propose_if_lower_configured] proposal R2 V ∧ tot.le R1 R2 → ∃ c, configure_round_msg R1 c

invariant [master_complete_zero_or_holds]
  (R2 = master_complete ∨ (configure_round_msg R3 C ∧ complete_of C = R2)) ∧ ¬ tot.le R2 R1 →
    complete_msg R2

invariant [complete_prev_configured] complete_msg R2 ∧ tot.le R1 R2 → ∃ c, configure_round_msg R1 c

-- conjecture forall R:round, V:value. (exists N:node. decision(N,R,V)) -> exists C:config, Q:quorum. configure_round_msg(R,C) & quorumin(Q,C) & (forall N:node. member(N, Q) -> vote(N,R,V))
invariant [decisions_from_quorums]
  (∃ n, decision n R V) →
    ∃ c q, configure_round_msg R c ∧ quorumin q c ∧ (∀ n, member n q → vote n R V)

invariant [choosable_proposal]
  ¬ tot.le R2 R1 ∧ proposal R2 V2 ∧ V1 ≠ V2 ∧ configure_round_msg R1 C ∧ quorumin Q C →
    ∃ n r3 rp v, member n Q ∧ ¬ tot.le r3 R1 ∧ join_ack_msg n r3 rp v ∧ ¬ vote n R1 V1

invariant [configure_round_msg_bounds]
  configure_round_msg R C → tot.le (complete_of C) R ∧ tot.le (complete_of C) master_complete

invariant [complete_choosable_decision]
  complete_msg RR ∧ ¬ tot.le RR R ∧ configure_round_msg R C ∧ quorumin Q C ∧
      ¬ (∃ n r3 rp vp, member n Q ∧ ¬ tot.le r3 R ∧ join_ack_msg n r3 rp vp ∧ ¬ vote n R V) →
    ∃ nn, decision nn RR V

invariant [none_property1] ¬ proposal R none
invariant [none_property2] ¬ vote N R none
invariant [none_property3] ¬ decision N R none

invariant [join_ack_msg_property1] join_ack_msg N R RP V → one_a R RP
invariant [join_ack_msg_property2] join_ack_msg N R RP none → ¬ vote N RP V
invariant [join_ack_msg_property3] join_ack_msg N R RP V ∧ V ≠ none → vote N RP V

#time #gen_spec

#check_invariants


@[veil]
theorem propose_choosable_proposal (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (value : Type) [value_dec_eq : DecidableEq.{1} value]
    [value_inhabited : Inhabited.{1} value] (quorum : Type) [quorum_dec_eq : DecidableEq.{1} quorum]
    [quorum_inhabited : Inhabited.{1} quorum] (round : Type) [round_dec_eq : DecidableEq.{1} round]
    [round_inhabited : Inhabited.{1} round] (config : Type) [config_dec_eq : DecidableEq.{1} config]
    [config_inhabited : Inhabited.{1} config] [tot : TotalOrder round] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain node value quorum round config __veil_f)
          (State.Label.toCodomain node value quorum round config __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain node value quorum round config __veil_f)
          (State.Label.toCodomain node value quorum round config __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory node value quorum round config) ρ]
    [propose_dec_0 : delta% @VerticalPaxosFirstOrder.propose._veil_dec_type_0 round χ value node quorum config χ_rep]
    [propose_dec_1 :
      delta% @VerticalPaxosFirstOrder.propose._veil_dec_type_1 round χ tot config node value quorum χ_rep]
    [propose_dec_2 :
      delta% @VerticalPaxosFirstOrder.propose._veil_dec_type_2 round χ node value quorum config tot χ_rep]
    [propose_dec_3 :
      delta% @VerticalPaxosFirstOrder.propose._veil_dec_type_3 round χ node value quorum config tot χ_rep]
    [propose_dec_4 :
      delta% @VerticalPaxosFirstOrder.propose._veil_dec_type_4 round χ node value quorum config χ_rep tot] :
    ∀ (r : round) (c : config) (cr : round),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@propose.ext ρ σ node node_dec_eq node_inhabited value value_dec_eq value_inhabited quorum quorum_dec_eq
          quorum_inhabited round round_dec_eq round_inhabited config config_dec_eq config_inhabited tot χ χ_rep
          χ_rep_lawful σ_sub ρ_sub propose_dec_0 propose_dec_1 propose_dec_2 propose_dec_3 propose_dec_4 r c cr)
        (@Assumptions ρ node node_dec_eq node_inhabited value value_dec_eq value_inhabited quorum quorum_dec_eq
          quorum_inhabited round round_dec_eq round_inhabited config config_dec_eq config_inhabited tot ρ_sub)
        (@Invariants ρ σ node node_dec_eq node_inhabited value value_dec_eq value_inhabited quorum quorum_dec_eq
          quorum_inhabited round round_dec_eq round_inhabited config config_dec_eq config_inhabited tot χ χ_rep
          χ_rep_lawful σ_sub ρ_sub)
        (@choosable_proposal ρ σ node node_dec_eq node_inhabited value value_dec_eq value_inhabited quorum quorum_dec_eq
          quorum_inhabited round round_dec_eq round_inhabited config config_dec_eq config_inhabited tot χ χ_rep
          χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  classical
  rcases hinv with
    ⟨_, hproposal_unique, _, _, _, honly_vote_proposed, _, hcomplete_holds, _, hdecisions_from_quorums,
      hchoosable_proposal, hconfigure_bounds, hcomplete_choosable_decision, _, _, _, _,
      hjoin_none, hjoin_non_none⟩
  intro hconfigured_r hcr hno_proposal_r hconfigured_between hquorum_between hjoin_between v maxr hmax
  have hcr_le_r : TotalOrder.le cr r := by
    simpa [hcr] using (hconfigure_bounds r c hconfigured_r).1
  have old_proposal_witness {R2 R1 : round} {V2 V1 : value} {C : config} {Q : quorum}
      (hlt : ¬TotalOrder.le R2 R1) (hproposal : st.proposal R2 V2 = true)
      (hneq : ¬V1 = V2) (hconfigured : st.configure_round_msg R1 C = true)
      (hquorum : th.quorumin Q C = true) :
      ∃ n,
        th.member n Q = true ∧
          ∃ x,
            ¬TotalOrder.le x R1 ∧
              (∃ x_1 x_2, st.join_ack_msg n x x_1 x_2 = true) ∧ st.vote n R1 V1 = false :=
    hchoosable_proposal R2 R1 V2 V1 C Q hlt hproposal hneq hconfigured hquorum
  split
  · rename_i hv_none
    rcases hmax with hnone_case | hnon_none_case
    · rcases hnone_case with ⟨_, hnone_all⟩
      have hno_member_between :
          ∀ (N : node) (MAXR : round) (V : value),
            TotalOrder.le cr MAXR → ¬TotalOrder.le r MAXR → th.member N (t MAXR) = false := by
        intro N MAXR V hle hlt
        exact (hnone_all N MAXR V).1 hle hlt
      intro proposedValue hproposed_not_none R2 R1 V2 V1 C Q hlt hproposal_post hneq hconfigured hquorum
      by_cases hnew : r = R2 ∧ proposedValue = V2
      · rcases hnew with ⟨hr, hp⟩
        subst R2
        subst V2
        by_cases hcr_le_R1 : TotalOrder.le cr R1
        · have htquorum : th.quorumin (t R1) C = true := by
            exact hquorum_between R1 C hcr_le_R1 hlt hconfigured
          obtain ⟨n, hnQ, hnT⟩ := has C Q (t R1) hquorum htquorum
          have hnT_false := hno_member_between n R1 proposedValue hcr_le_R1 hlt
          rw [hnT] at hnT_false
          cases hnT_false
        · by_contra hmissing
          have hcomplete_cr : st.complete_msg cr = true :=
            hcomplete_holds cr r c R1 (Or.inr ⟨hconfigured_r, hcr⟩) hcr_le_R1
          have hno_counterexample :
              ∀ (x : node),
                th.member x Q = true →
                  ∀ (x_1 : round),
                    ¬TotalOrder.le x_1 R1 →
                      ∀ (x_2 : round) (x_3 : value),
                        st.join_ack_msg x x_1 x_2 x_3 = true → st.vote x R1 V1 = true := by
            intro x hxQ x_1 hx_1 x_2 x_3 hxjoin
            by_cases hvote : st.vote x R1 V1 = true
            · exact hvote
            · have hvote_false : st.vote x R1 V1 = false := by
                cases h : st.vote x R1 V1 <;> simp [h] at hvote ⊢
              exact False.elim (hmissing ⟨x, hxQ, x_1, hx_1, ⟨⟨x_2, x_3, hxjoin⟩, hvote_false⟩⟩)
          obtain ⟨nn, hdecision_cr⟩ :=
            hcomplete_choosable_decision cr R1 C Q V1 hcomplete_cr hcr_le_R1 hconfigured hquorum
              hno_counterexample
          obtain ⟨Ccr, hconfigured_cr, Qcr, hquorum_cr, hvotes_cr⟩ :=
            hdecisions_from_quorums cr V1 nn hdecision_cr
          by_cases hr_le_cr : TotalOrder.le r cr
          · have hr_eq_cr : r = cr := @TotalOrder.le_antisymm round tot r cr hr_le_cr hcr_le_r
            obtain ⟨n, hnQcr, _⟩ := has Ccr Qcr Qcr hquorum_cr hquorum_cr
            have hvote_cr : st.vote n cr V1 = true := hvotes_cr n hnQcr
            have hproposal_cr : st.proposal cr V1 = true := honly_vote_proposed n cr V1 hvote_cr
            have hproposal_r : st.proposal r V1 = true := by
              simpa [hr_eq_cr] using hproposal_cr
            rw [hno_proposal_r V1] at hproposal_r
            cases hproposal_r
          · have htquorum_cr : th.quorumin (t cr) Ccr = true :=
              hquorum_between cr Ccr (@TotalOrder.le_refl round tot cr) hr_le_cr hconfigured_cr
            obtain ⟨n, _, hnTcr⟩ := has Ccr Qcr (t cr) hquorum_cr htquorum_cr
            have hnTcr_false := hno_member_between n cr V1 (@TotalOrder.le_refl round tot cr) hr_le_cr
            rw [hnTcr] at hnTcr_false
            cases hnTcr_false
      · exact old_proposal_witness hlt
          (hproposal_post (by intro hr hp; exact hnew ⟨hr, hp⟩)) hneq hconfigured hquorum
    · exact False.elim (hnon_none_case.1 hv_none)
  · rename_i hv_not_none
    rcases hmax with hnone_case | hnon_none_case
    · exact False.elim (hv_not_none hnone_case.1)
    · rcases hnon_none_case with ⟨hv_non_none, hmax_in_range, hmaximal⟩
      rcases hmax_in_range with ⟨hcr_le_maxr, hr_not_le_maxr, hmax_witness⟩
      rcases hmax_witness with ⟨nmax, hnmax_member, hjoin_maxr, _⟩
      have hvote_maxr : st.vote nmax maxr v = true :=
        hjoin_non_none nmax r maxr v hjoin_maxr hv_non_none
      have hproposal_maxr : st.proposal maxr v = true :=
        honly_vote_proposed nmax maxr v hvote_maxr
      intro R2 R1 V2 V1 C Q hlt hproposal_post hneq hconfigured hquorum
      by_cases hnew : r = R2 ∧ v = V2
      · rcases hnew with ⟨hr, hp⟩
        subst R2
        subst V2
        by_cases hcr_le_R1 : TotalOrder.le cr R1
        · by_cases hmaxr_le_R1 : TotalOrder.le maxr R1
          · have htquorum : th.quorumin (t R1) C = true :=
              hquorum_between R1 C hcr_le_R1 hlt hconfigured
            obtain ⟨n, hnQ, hnT⟩ := has C Q (t R1) hquorum htquorum
            obtain ⟨joinedValue, hjoin⟩ := hjoin_between R1 n hcr_le_R1 hlt hnT
            by_cases hvote : st.vote n R1 V1 = true
            · by_cases hjoined_none : joinedValue = st.none
              · subst joinedValue
                have hvote_false := hjoin_none n r R1 V1 hjoin
                rw [hvote] at hvote_false
                cases hvote_false
              · have hvote_joined : st.vote n R1 joinedValue = true :=
                  hjoin_non_none n r R1 joinedValue hjoin hjoined_none
                have hR1_le_maxr : TotalOrder.le R1 maxr :=
                  hmaximal n R1 joinedValue hcr_le_R1 hlt hnT hjoin hjoined_none
                have hmaxr_eq_R1 : maxr = R1 :=
                  @TotalOrder.le_antisymm round tot maxr R1 hmaxr_le_R1 hR1_le_maxr
                have hproposal_R1_v : st.proposal R1 v = true := by
                  simpa [hmaxr_eq_R1] using hproposal_maxr
                have hproposal_V1 : st.proposal R1 V1 = true :=
                  honly_vote_proposed n R1 V1 hvote
                have hproposal_joined : st.proposal R1 joinedValue = true :=
                  honly_vote_proposed n R1 joinedValue hvote_joined
                have hV1_eq_joined : V1 = joinedValue :=
                  hproposal_unique R1 V1 joinedValue hproposal_V1 hproposal_joined
                have hjoined_eq_v : joinedValue = v :=
                  hproposal_unique R1 joinedValue v hproposal_joined hproposal_R1_v
                exact False.elim (hneq (hV1_eq_joined.trans hjoined_eq_v))
            · have hvote_false : st.vote n R1 V1 = false := by
                cases h : st.vote n R1 V1 <;> simp [h] at hvote ⊢
              exact ⟨n, hnQ, r, hlt, ⟨⟨R1, joinedValue, hjoin⟩, hvote_false⟩⟩
          · exact old_proposal_witness hmaxr_le_R1 hproposal_maxr hneq hconfigured hquorum
        · have hmaxr_not_le_R1 : ¬TotalOrder.le maxr R1 := by
            intro hle
            exact hcr_le_R1 (@TotalOrder.le_trans round tot cr maxr R1 hcr_le_maxr hle)
          exact old_proposal_witness hmaxr_not_le_R1 hproposal_maxr hneq hconfigured hquorum
      · exact old_proposal_witness hlt
          (hproposal_post (by intro hr hp; exact hnew ⟨hr, hp⟩)) hneq hconfigured hquorum

@[veil]
theorem join_round_complete_choosable_decision (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (value : Type) [value_dec_eq : DecidableEq.{1} value]
    [value_inhabited : Inhabited.{1} value] (quorum : Type) [quorum_dec_eq : DecidableEq.{1} quorum]
    [quorum_inhabited : Inhabited.{1} quorum] (round : Type) [round_dec_eq : DecidableEq.{1} round]
    [round_inhabited : Inhabited.{1} round] (config : Type) [config_dec_eq : DecidableEq.{1} config]
    [config_inhabited : Inhabited.{1} config] [tot : TotalOrder round] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain node value quorum round config __veil_f)
          (State.Label.toCodomain node value quorum round config __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain node value quorum round config __veil_f)
          (State.Label.toCodomain node value quorum round config __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory node value quorum round config) ρ]
    [join_round_dec_0 :
      delta% @VerticalPaxosFirstOrder.join_round._veil_dec_type_0 node round χ value quorum config χ_rep tot]
    [join_round_dec_1 :
      delta% @VerticalPaxosFirstOrder.join_round._veil_dec_type_1 node round χ value quorum config χ_rep] :
    ∀ (n : node) (r : round) (rp : round),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@join_round.ext ρ σ node node_dec_eq node_inhabited value value_dec_eq value_inhabited quorum quorum_dec_eq
          quorum_inhabited round round_dec_eq round_inhabited config config_dec_eq config_inhabited tot χ χ_rep
          χ_rep_lawful σ_sub ρ_sub join_round_dec_0 join_round_dec_1 n r rp)
        (@Assumptions ρ node node_dec_eq node_inhabited value value_dec_eq value_inhabited quorum quorum_dec_eq
          quorum_inhabited round round_dec_eq round_inhabited config config_dec_eq config_inhabited tot ρ_sub)
        (@Invariants ρ σ node node_dec_eq node_inhabited value value_dec_eq value_inhabited quorum quorum_dec_eq
          quorum_inhabited round round_dec_eq round_inhabited config config_dec_eq config_inhabited tot χ χ_rep
          χ_rep_lawful σ_sub ρ_sub)
        (@complete_choosable_decision ρ σ node node_dec_eq node_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited round round_dec_eq round_inhabited config config_dec_eq config_inhabited tot χ
          χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  rcases hinv with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcomplete_choosable_decision, _, _, _, _, _, _⟩
  intro _ _ t
  split
  · intro RR R C Q V hcomplete hlt hconfigured hquorum hchoosable
    exact hcomplete_choosable_decision RR R C Q V hcomplete hlt hconfigured hquorum
      (by
        intro x hxmem x₁ hx₁ x₂ x₃ hjoin
        exact hchoosable x hxmem x₁ hx₁ x₂ x₃ (fun _ => hjoin))
  · intro _ RR R C Q V hcomplete hlt hconfigured hquorum hchoosable
    exact hcomplete_choosable_decision RR R C Q V hcomplete hlt hconfigured hquorum
      (by
        intro x hxmem x₁ hx₁ x₂ x₃ hjoin
        exact hchoosable x hxmem x₁ hx₁ x₂ x₃ (fun _ => hjoin))

@[veil]
theorem join_round_choosable_proposal (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (value : Type) [value_dec_eq : DecidableEq.{1} value]
    [value_inhabited : Inhabited.{1} value] (quorum : Type) [quorum_dec_eq : DecidableEq.{1} quorum]
    [quorum_inhabited : Inhabited.{1} quorum] (round : Type) [round_dec_eq : DecidableEq.{1} round]
    [round_inhabited : Inhabited.{1} round] (config : Type) [config_dec_eq : DecidableEq.{1} config]
    [config_inhabited : Inhabited.{1} config] [tot : TotalOrder round] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain node value quorum round config __veil_f)
          (State.Label.toCodomain node value quorum round config __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain node value quorum round config __veil_f)
          (State.Label.toCodomain node value quorum round config __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory node value quorum round config) ρ]
    [join_round_dec_0 :
      delta% @VerticalPaxosFirstOrder.join_round._veil_dec_type_0 node round χ value quorum config χ_rep tot]
    [join_round_dec_1 :
      delta% @VerticalPaxosFirstOrder.join_round._veil_dec_type_1 node round χ value quorum config χ_rep] :
    ∀ (n : node) (r : round) (rp : round),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@join_round.ext ρ σ node node_dec_eq node_inhabited value value_dec_eq value_inhabited quorum quorum_dec_eq
          quorum_inhabited round round_dec_eq round_inhabited config config_dec_eq config_inhabited tot χ χ_rep
          χ_rep_lawful σ_sub ρ_sub join_round_dec_0 join_round_dec_1 n r rp)
        (@Assumptions ρ node node_dec_eq node_inhabited value value_dec_eq value_inhabited quorum quorum_dec_eq
          quorum_inhabited round round_dec_eq round_inhabited config config_dec_eq config_inhabited tot ρ_sub)
        (@Invariants ρ σ node node_dec_eq node_inhabited value value_dec_eq value_inhabited quorum quorum_dec_eq
          quorum_inhabited round round_dec_eq round_inhabited config config_dec_eq config_inhabited tot χ χ_rep
          χ_rep_lawful σ_sub ρ_sub)
        (@choosable_proposal ρ σ node node_dec_eq node_inhabited value value_dec_eq value_inhabited quorum quorum_dec_eq
          quorum_inhabited round round_dec_eq round_inhabited config config_dec_eq config_inhabited tot χ χ_rep
          χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  rcases hinv with
    ⟨_, _, _, _, _, _, _, _, _, _, hchoosable_proposal, _, _, _, _, _, _, _, _⟩
  intro _ _ t
  split
  · intro R2 R1 V2 V1 C Q hlt hproposal hneq hconfigured hquorum
    obtain ⟨n₁, hn₁mem, hwitness⟩ :=
      hchoosable_proposal R2 R1 V2 V1 C Q hlt hproposal hneq hconfigured hquorum
    obtain ⟨x, hxlt, hwitness⟩ := hwitness
    obtain ⟨hjoin_witness, hvote⟩ := hwitness
    obtain ⟨x₁, x₂, hjoin⟩ := hjoin_witness
    exact ⟨n₁, hn₁mem, x, hxlt, ⟨⟨x₁, x₂, fun _ => hjoin⟩, hvote⟩⟩
  · intro _ R2 R1 V2 V1 C Q hlt hproposal hneq hconfigured hquorum
    obtain ⟨n₁, hn₁mem, hwitness⟩ :=
      hchoosable_proposal R2 R1 V2 V1 C Q hlt hproposal hneq hconfigured hquorum
    obtain ⟨x, hxlt, hwitness⟩ := hwitness
    obtain ⟨hjoin_witness, hvote⟩ := hwitness
    obtain ⟨x₁, x₂, hjoin⟩ := hjoin_witness
    exact ⟨n₁, hn₁mem, x, hxlt, ⟨⟨x₁, x₂, fun _ => hjoin⟩, hvote⟩⟩

end VerticalPaxosFirstOrder
