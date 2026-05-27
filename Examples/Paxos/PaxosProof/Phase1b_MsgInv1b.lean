import Veil
import Examples.Paxos.PaxosSpec

namespace Paxos

@[veil]
theorem Phase1b_MsgInv1b (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
    [acceptor_inhabited : Inhabited.{1} acceptor] (value : Type) [value_dec_eq : DecidableEq.{1} value]
    [value_inhabited : Inhabited.{1} value] (quorum : Type) [quorum_dec_eq : DecidableEq.{1} quorum]
    [quorum_inhabited : Inhabited.{1} quorum] (ballot : Type) [ballot_dec_eq : DecidableEq.{1} ballot]
    [ballot_inhabited : Inhabited.{1} ballot] [tot : TotalOrderWithZeroAndNone ballot] (MsgSet : Type)
    [MsgSet_dec_eq : DecidableEq.{1} MsgSet] [MsgSet_inhabited : Inhabited.{1} MsgSet] (AcceptorSet : Type)
    [AcceptorSet_dec_eq : DecidableEq.{1} AcceptorSet] [AcceptorSet_inhabited : Inhabited.{1} AcceptorSet]
    [msgTset : TSet (Msg acceptor value ballot) MsgSet] [acSet : TSet acceptor AcceptorSet] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain acceptor value quorum ballot MsgSet AcceptorSet __veil_f)
          (State.Label.toCodomain acceptor value quorum ballot MsgSet AcceptorSet __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain acceptor value quorum ballot MsgSet AcceptorSet __veil_f)
          (State.Label.toCodomain acceptor value quorum ballot MsgSet AcceptorSet __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory acceptor value quorum ballot MsgSet AcceptorSet) ρ]
    [Phase1b_dec_0 :
      (a : acceptor) →
        (__do_lift : State χ) →
          (m : Msg acceptor value ballot) →
            Decidable
              (And
                (@TotalOrderWithZeroAndNone.le ballot tot
                  (@Veil.FieldRepresentation.get
                    (State.Label.toDomain acceptor value quorum ballot MsgSet AcceptorSet State.Label.maxBal)
                    (State.Label.toCodomain acceptor value quorum ballot MsgSet AcceptorSet State.Label.maxBal)
                    (χ State.Label.maxBal) (χ_rep State.Label.maxBal) __do_lift.3 a)
                  m.4)
                (Not
                  (@Eq.{1} ballot m.4
                    (@Veil.FieldRepresentation.get
                      (State.Label.toDomain acceptor value quorum ballot MsgSet AcceptorSet State.Label.maxBal)
                      (State.Label.toCodomain acceptor value quorum ballot MsgSet AcceptorSet State.Label.maxBal)
                      (χ State.Label.maxBal) (χ_rep State.Label.maxBal) __do_lift.3 a))))] :
    ∀ (a : acceptor),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Phase1b.ext ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub
          Phase1b_dec_0 a)
        (@Assumptions ρ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet ρ_sub)
        (@Invariants ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@MsgInv1b ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  -- Phase1b creates message: { msgType := Phase1b, acc := a, val := st.maxVal a, bal := t.bal, maxVBal := st.maxVBal a }
  -- Need to show MsgInv1b for all Phase1b messages in post-state
  -- Note: After unveil, `a`, `t`, and `m` are already in scope
  intro hcontains hmcontains hmtype
  revert hmtype hmcontains m
  intro msg hmcontains hmtype
  -- Check if m is the newly created message or was in pre-state
  by_cases heq : msg = { msgType := MsgType.Phase1b, acc := a, val := st.maxVal a, bal := m.bal, maxVBal := st.maxVBal a }
  · -- m is the new message - need to verify MsgInv1b properties
    subst heq
    simp only [ite_true]
    -- Extract guards and invariants
    have hpred := TSet.contains_filter _ _ _ hcontains
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
    obtain ⟨_, hle_guard, _⟩ := hpred
    obtain ⟨_, _, _, _, _, hAccInv, _⟩ := hinv
    obtain ⟨_, hVoted, hNoVote⟩ := hAccInv a
    refine ⟨TotalOrderWithZeroAndNone.le_refl _, ?_, ?_⟩
    -- VotedForIn witness from AccInv: (maxVBal a ≠ none → VotedForIn ...) becomes disjunction
    · by_cases hmaxVBal_none : st.maxVBal a = tot.none
      · -- maxVBal a = none
        right; exact hmaxVBal_none
      · -- maxVBal a ≠ none, so hVoted gives us VotedForIn
        left
        refine ⟨hmaxVBal_none, ?_⟩
        -- VotedForIn a (maxVal a) (maxVBal a) from hVoted
        have hvf := hVoted hmaxVBal_none
        -- hvf : ∃ m, contains m msgs ∧ m.msgType = Phase2b ∧ ...
        obtain ⟨m'', hm''contains, hm''type, hm''val, hm''bal, hm''acc⟩ := hvf
        have hm''ne : m'' ≠ { msgType := MsgType.Phase1b, acc := a, val := st.maxVal a, bal := m.bal, maxVBal := st.maxVBal a } := by
          intro heq'; rw [heq'] at hm''type; simp at hm''type
        refine ⟨m'', ?_, hm''type, hm''val, hm''bal, hm''acc⟩
        rw [TSet.contains_insert_other _ _ _ hm''ne]
        exact hm''contains
    -- No votes between maxVBal and t.bal - from AccInv
    -- The third conjunct is: ∀ c, lt maxVBal c → lt c bal → ∀ v, ¬VotedForIn a v c
    -- Ghost relations expand conjuncts, so intro pattern matches Phase1a_MsgInv1b
    · intro x c hle1 hne1 hle2 hne2 hxcontains hxtype hxbal
      have hxne : x ≠ { msgType := MsgType.Phase1b, acc := a, val := st.maxVal a, bal := m.bal, maxVBal := st.maxVBal a } := by
        intro heq'; rw [heq'] at hxtype; simp at hxtype
      rw [TSet.contains_insert_other _ _ _ hxne] at hxcontains
      -- Use AccInv's hNoVote: ∀ c, gt c (maxVBal a) → ∀ v, ¬VotedForIn a v c
      -- gt c x = le x c ∧ c ≠ x, we have hle1 : le maxVBal c and hne1 : maxVBal ≠ c
      exact hNoVote x c hle1 (Ne.symm hne1) hxcontains hxtype hxbal
  · -- m was in pre-state
    have hmne := heq
    rw [TSet.contains_insert_other _ _ _ hmne] at hmcontains
    -- Extract MsgInv1b from hinv
    obtain ⟨_, _, hMsgInv1b, _⟩ := hinv
    obtain ⟨hbal, hmaxVBal_or, hnoVote⟩ := hMsgInv1b msg hmcontains hmtype
    refine ⟨?_, ?_, ?_⟩
    -- Ballot condition: le m.bal (new maxBal m.acc)
    · by_cases hacc : a = msg.acc
      · -- a = m.acc: new maxBal = t.bal
        simp only [hacc, ite_true]
        -- hbal : le msg.bal (st.maxBal msg.acc), need to rewrite using hacc
        rw [← hacc] at hbal
        -- Now hbal : le m.bal (st.maxBal a)
        -- hle_guard : le (st.maxBal a) t.bal
        have hpred := TSet.contains_filter _ _ _ hcontains
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
        exact TotalOrderWithZeroAndNone.le_trans _ _ _ hbal hpred.2.1
      · -- a ≠ m.acc: maxBal unchanged
        simp only [hacc, ite_false]
        exact hbal
    -- VotedForIn witness preserved
    · rcases hmaxVBal_or with ⟨hne, m'', hm''contains, hm''type, hm''val, hm''bal, hm''acc⟩ | heq_none
      · left
        have hm''ne : m'' ≠ { msgType := MsgType.Phase1b, acc := a, val := st.maxVal a, bal := m.bal, maxVBal := st.maxVBal a } := by
          intro heq'; rw [heq'] at hm''type; simp at hm''type
        refine ⟨hne, m'', ?_, hm''type, hm''val, hm''bal, hm''acc⟩
        rw [TSet.contains_insert_other _ _ _ hm''ne]
        exact hm''contains
      · right; exact heq_none
    -- No votes between maxVBal and m.bal preserved
    · intro x c hle hne hlt hne' hxcontains hxtype hxbal
      have hxne : x ≠ { msgType := MsgType.Phase1b, acc := a, val := st.maxVal a, bal := m.bal, maxVBal := st.maxVBal a } := by
        intro heq'; rw [heq'] at hxtype; simp at hxtype
      rw [TSet.contains_insert_other _ _ _ hxne] at hxcontains
      exact hnoVote x c hle hne hlt hne' hxcontains hxtype hxbal

end Paxos
