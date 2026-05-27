import Veil
import Examples.Paxos.PaxosSpec

namespace Paxos

@[veil]
theorem Phase1b_MsgInv2a (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@MsgInv2a ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  -- Phase1b only adds a Phase1b message, so MsgInv2a for Phase2a messages is preserved
  -- After unveil: `a` (acceptor), `t` (trigger Phase1a message), `m` (message to check) are in scope
  -- Goal requires: htcontains → hmcontains → hmsgtype → (SafeAt ∧ Unique)
  intro htcontains hmcontains hmsgtype
  revert hmsgtype hmcontains m
  intro msg hmcontains hmsgtype
  -- Extract the guard from htcontains: t is Phase1a and gt t.bal (st.maxBal a)
  have hpred := TSet.contains_filter _ _ _ htcontains
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
  obtain ⟨_, hle_guard, hne_guard⟩ := hpred
  -- The newly inserted message is a Phase1b message, not Phase2a
  have hne : msg ≠ { msgType := MsgType.Phase1b, acc := a, val := st.maxVal a, bal := m.bal, maxVBal := st.maxVBal a } := by
    intro heq
    rw [heq] at hmsgtype
    simp at hmsgtype
  -- So m was in the pre-state msgs
  rw [TSet.contains_insert_other _ _ _ hne] at hmcontains
  -- Extract MsgInv2a from hinv
  obtain ⟨_, _, _, hMsgInv2a, _⟩ := hinv
  -- Apply the pre-state MsgInv2a invariant
  obtain ⟨hSafeAt, hUnique⟩ := hMsgInv2a msg hmcontains hmsgtype
  refine ⟨?_, ?_⟩
  -- SafeAt: need to show VotedForIn/WontVoteIn witnesses exist in post-state
  -- VotedForIn witnesses are Phase2b messages which lift to post-state
  -- WontVoteIn involves ¬VotedForIn (about Phase2b messages) and maxBal (only increases for acceptor a)
  · intro c hlt hne' hne_none
    obtain ⟨Q, hQ⟩ := hSafeAt c hlt hne' hne_none
    refine ⟨Q, ?_⟩
    intro a' ha'
    rcases hQ a' ha' with ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩ | ⟨hnoVote, hmaxBal1, hmaxBal2⟩
    -- Case: VotedForIn - lift the Phase2b witness to post-state
    · left
      have hm'ne : m' ≠ { msgType := MsgType.Phase1b, acc := a, val := st.maxVal a, bal := m.bal, maxVBal := st.maxVBal a } := by
        intro heq'
        rw [heq'] at hm'type
        simp at hm'type
      refine ⟨m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
      rw [TSet.contains_insert_other _ _ _ hm'ne]
      exact hm'contains
    -- Case: WontVoteIn - Phase1b doesn't add Phase2b messages, and maxBal only increases
    · right
      refine ⟨?_, ?_, ?_⟩
      -- ¬VotedForIn in post-state: no new Phase2b messages added
      · intro x hxcontains hxtype hxbal
        have hxne : x ≠ { msgType := MsgType.Phase1b, acc := a, val := st.maxVal a, bal := m.bal, maxVBal := st.maxVBal a } := by
          intro heq'
          rw [heq'] at hxtype
          simp at hxtype
        rw [TSet.contains_insert_other _ _ _ hxne] at hxcontains
        exact hnoVote x hxcontains hxtype hxbal
      -- maxBal condition: need to show le c (new maxBal a') and c ≠ (new maxBal a')
      -- For a' = a: new maxBal = t.bal
      -- For a' ≠ a: maxBal unchanged
      · by_cases hacc : a = a'
        · simp only [hacc, ite_true]
          -- hmaxBal1 : le c (st.maxBal a'), hmaxBal2 : c ≠ st.maxBal a'
          -- hle_guard : le (st.maxBal a) t.bal
          rw [← hacc] at hmaxBal1
          exact TotalOrderWithZeroAndNone.le_trans _ _ _ hmaxBal1 hle_guard
        · simp only [hacc, ite_false]
          exact hmaxBal1
      · by_cases hacc : a = a'
        · simp only [hacc, ite_true]
          -- Need to show c ≠ t.bal (i.e., ¬t.bal = c)
          -- We have WontVoteIn in pre-state: gt (st.maxBal a') c
          -- i.e., le c (st.maxBal a') ∧ c ≠ st.maxBal a'
          -- And from guard: gt t.bal (st.maxBal a), i.e., le (st.maxBal a) t.bal ∧ t.bal ≠ st.maxBal a
          -- When a = a': c ≤ st.maxBal a and st.maxBal a < t.bal
          -- So c < t.bal, hence t.bal ≠ c
          rw [← hacc] at hmaxBal1 hmaxBal2
          -- hmaxBal1 : le c (st.maxBal a)
          -- hmaxBal2 : ¬st.maxBal a = c
          -- hle_guard : le (st.maxBal a) t.bal
          -- hne_guard : ¬t.bal = st.maxBal a
          -- If t.bal = c, then since c ≤ st.maxBal a and st.maxBal a ≤ t.bal = c, we get st.maxBal a = c
          -- But hmaxBal2 says ¬st.maxBal a = c
          intro hc_eq_tbal
          -- hc_eq_tbal : t.bal = c
          rw [← hc_eq_tbal] at hmaxBal1
          -- Now hmaxBal1 : le t.bal (st.maxBal a)
          -- hle_guard : le (st.maxBal a) t.bal
          -- So st.maxBal a = t.bal by antisymmetry
          have heq_bal := TotalOrderWithZeroAndNone.le_antisymm _ _ hle_guard hmaxBal1
          -- heq_bal : st.maxBal a = t.bal
          -- hmaxBal2 : ¬st.maxBal a = c, and hc_eq_tbal : t.bal = c
          -- So st.maxBal a = t.bal = c, contradicting hmaxBal2
          rw [heq_bal, hc_eq_tbal] at hmaxBal2
          exact hmaxBal2 rfl
        · simp only [hacc, ite_false]
          exact hmaxBal2
  -- Uniqueness: any Phase2a message in post-state was in pre-state
  · intro ma hmacontains hmatype hmabal
    have hmane : ma ≠ { msgType := MsgType.Phase1b, acc := a, val := st.maxVal a, bal := m.bal, maxVBal := st.maxVBal a } := by
      intro heq'
      rw [heq'] at hmatype
      simp at hmatype
    rw [TSet.contains_insert_other _ _ _ hmane] at hmacontains
    exact hUnique ma hmacontains hmatype hmabal

end Paxos
