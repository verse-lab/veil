import Veil
import Examples.Paxos.PaxosSpec

namespace Paxos

@[veil]
theorem Phase2b_MsgInv2b (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
    [Phase2b_dec_0 :
      (a : acceptor) →
        (__do_lift : State χ) →
          (m : Msg acceptor value ballot) →
            Decidable
              (And (@Eq.{1} MsgType m.1 MsgType.Phase2a)
                (@TotalOrderWithZeroAndNone.le ballot tot
                  (@Veil.FieldRepresentation.get
                    (State.Label.toDomain acceptor value quorum ballot MsgSet AcceptorSet State.Label.maxBal)
                    (State.Label.toCodomain acceptor value quorum ballot MsgSet AcceptorSet State.Label.maxBal)
                    (χ State.Label.maxBal) (χ_rep State.Label.maxBal) __do_lift.3 a)
                  m.4))] :
    ∀ (a : acceptor),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Phase2b.ext ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub
          Phase2b_dec_0 a)
        (@Assumptions ρ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet ρ_sub)
        (@Invariants ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@MsgInv2b ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  -- Phase2b adds a Phase2b message
  -- MsgInv2b: for each Phase2b m, there's a Phase2a with same ballot/value, and m.bal <= maxVBal[m.acc]
  intro hfilter hm_in_post hmsgtype
  revert hmsgtype hm_in_post m
  intro msg hm_in_post hmsgtype
  let newMsg : Msg acceptor value ballot := {
    msgType := MsgType.Phase2b,
    acc := a,
    val := m.val,
    bal := m.bal,
    maxVBal := default
  }
  obtain ⟨_, hTypeOK, _, _, hMsgInv2b, _⟩ := hinv
  by_cases hm_eq : msg = newMsg
  · -- m is the new Phase2b message
    subst hm_eq
    refine ⟨?_, ?_⟩
    -- Show there's a Phase2a with same ballot and value
    · -- t is the Phase2a message
      have hpred := @TSet.contains_filter _ _ msgTset m _ _ hfilter
      simp only [decide_eq_true_iff] at hpred
      obtain ⟨ht_type, _⟩ := hpred
      -- t is in pre-state, need to show in post-state
      have ht_in_pre : TSet.contains m st.msgs = true := TSet.contains_of_contains_filter _ _ _ hfilter
      by_cases ht_eq : m = newMsg
      · -- t = newMsg is impossible since t is Phase2a and newMsg is Phase2b
        rw [ht_eq] at ht_type
        simp at ht_type
      · refine ⟨m, ?_, ht_type, rfl, rfl⟩
        rw [TSet.contains_insert_other _ _ _ ht_eq]
        exact ht_in_pre
    -- Show newMsg.bal <= maxVBal[newMsg.acc] = t.bal <= maxVBal[a] in post-state
    · -- Post-state maxVBal[a] = t.bal, so goal is le t.bal t.bal
      -- After subst, m.acc = newMsg.acc = a, so condition is a = a
      rw [if_pos rfl]
      exact TotalOrderWithZeroAndNone.le_refl _
  · -- m is in pre-state
    rw [TSet.contains_insert_other _ _ _ hm_eq] at hm_in_post
    obtain ⟨hPhase2a, hle_maxVBal⟩ := hMsgInv2b msg hm_in_post hmsgtype
    refine ⟨?_, ?_⟩
    -- Lift the Phase2a witness
    · obtain ⟨ma, hma_contains, hma_type, hma_bal, hma_val⟩ := hPhase2a
      refine ⟨ma, ?_, hma_type, hma_bal, hma_val⟩
      have hma_ne : ma ≠ newMsg := by
        intro heq
        rw [heq] at hma_type
        simp at hma_type
      rw [TSet.contains_insert_other _ _ _ hma_ne]
      exact hma_contains
    -- Show m.bal <= maxVBal[m.acc] in post-state
    · by_cases ha : a = msg.acc
      · simp only [ha, ite_true]
        -- Post-state maxVBal[m.acc] = t.bal
        -- Pre-state: m.bal <= maxVBal[m.acc]
        -- Need: m.bal <= t.bal
        -- From filter: le (maxBal a) t.bal
        -- From pre-state TypeOK: maxVBal[a] <= maxBal[a]
        -- So maxVBal[m.acc] <= maxBal[a] <= t.bal
        have hpred := @TSet.contains_filter _ _ msgTset m _ _ hfilter
        simp only [decide_eq_true_iff] at hpred
        obtain ⟨_, hle_filter⟩ := hpred
        have hle_type := hTypeOK a
        rw [← ha] at hle_maxVBal
        have hle1 := TotalOrderWithZeroAndNone.le_trans _ _ _ hle_maxVBal hle_type
        exact TotalOrderWithZeroAndNone.le_trans _ _ _ hle1 hle_filter
      · simp only [ha, ite_false]
        exact hle_maxVBal

end Paxos
