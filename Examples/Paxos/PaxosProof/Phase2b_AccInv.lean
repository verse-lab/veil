import Veil
import Examples.Paxos.PaxosSpec

namespace Paxos

@[veil]
theorem Phase2b_AccInv (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@AccInv ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum quorum_dec_eq
          quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited AcceptorSet
          AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  -- Goal: prove AccInv in post-state
  -- After unveil: `a` (acceptor doing Phase2b), `t` (trigger Phase2a message), `st` (pre-state) in scope
  -- Phase2b creates message: { msgType := Phase2b, acc := a, val := t.val, bal := t.bal, maxVBal := default }
  -- Updates: maxBal a := t.bal, maxVBal a := t.bal, maxVal a := t.val
  intro hcontains a'
  -- Extract the guard from hcontains: t is Phase2a and ge t.bal (st.maxBal a)
  have hpred := TSet.contains_filter _ _ _ hcontains
  simp only [decide_eq_true_eq] at hpred
  obtain ⟨htype_t, hge_guard⟩ := hpred
  -- Extract AccInv from hinv
  obtain ⟨_, _, _, _, _, hAccInv, _⟩ := hinv
  -- Define the new message
  let newMsg : Msg acceptor value ballot := {
    msgType := MsgType.Phase2b,
    acc := a,
    val := m.val,
    bal := m.bal,
    maxVBal := default
  }
  -- Case split on whether a' = a
  by_cases h : a = a'
  · -- a = a': need to prove AccInv for the acceptor doing Phase2b
    subst h
    simp only [ite_true]
    obtain ⟨hle_pre, hVoted_pre, hNoVote_pre⟩ := hAccInv a
    refine ⟨?_, ?_, ?_⟩
    -- 1. le t.bal t.bal: by reflexivity
    · exact TotalOrderWithZeroAndNone.le_refl _
    -- 2. t.bal ≠ none → VotedForIn a t.val t.bal in post-state
    --    The new Phase2b message proves this!
    · intro hmaxVBal_ne
      -- The new message witnesses VotedForIn
      refine ⟨newMsg, ?_, rfl, rfl, rfl, rfl⟩
      exact TSet.contains_insert_self _ _
    -- 3. For all c > t.bal, ¬VotedForIn a v c in post-state
    --    The new message has bal = t.bal, not c > t.bal
    --    Any other Phase2b message was in pre-state, and pre-state AccInv says no votes above old maxVBal
    --    Since old maxVBal ≤ old maxBal ≤ t.bal < c, we have c > old maxVBal
    · intro x c hle_c hne_c hxcontains hxtype hxbal hxacc
      by_cases hxeq : x = newMsg
      · -- x is the new message: its bal = t.bal, but c > t.bal, contradiction
        subst hxeq
        -- hxbal : newMsg.bal = c, i.e., t.bal = c
        -- hne_c : c ≠ t.bal
        exact hne_c hxbal.symm
      · -- x is an old message: use pre-state AccInv
        rw [TSet.contains_insert_other _ _ _ hxeq] at hxcontains
        -- Need: c > st.maxVBal a
        -- We know: le (st.maxVBal a) (st.maxBal a) from pre-state AccInv (TypeOK part)
        -- And: ge t.bal (st.maxBal a) from guard, i.e., le (st.maxBal a) t.bal
        -- And: c > t.bal, i.e., le t.bal c ∧ t.bal ≠ c
        -- So: le (st.maxVBal a) c (by transitivity)
        -- If st.maxVBal a = c, then le t.bal (st.maxVBal a) and le (st.maxVBal a) (st.maxBal a) ≤ t.bal
        -- But hne_c says t.bal ≠ c = st.maxVBal a. Need to show c ≠ st.maxVBal a
        have hle_chain : tot.le (st.maxVBal a) c := by
          apply TotalOrderWithZeroAndNone.le_trans _ (st.maxBal a) _
          · exact hle_pre
          · apply TotalOrderWithZeroAndNone.le_trans _ m.bal _
            · exact hge_guard
            · exact hle_c
        -- Now need c ≠ st.maxVBal a
        by_cases hceq : c = st.maxVBal a
        · -- c = st.maxVBal a
          subst hceq
          -- le (st.maxVBal a) (st.maxBal a) ≤ t.bal and le t.bal (st.maxVBal a) and t.bal ≠ st.maxVBal a
          have hle_tb_mvb : tot.le m.bal (st.maxVBal a) := hle_c
          have hle_mvb_tb : tot.le (st.maxVBal a) m.bal := TotalOrderWithZeroAndNone.le_trans _ _ _ hle_pre hge_guard
          have heq_tb_mvb : st.maxVBal a = m.bal := TotalOrderWithZeroAndNone.le_antisymm _ _ hle_mvb_tb hle_tb_mvb
          exact hne_c heq_tb_mvb
        · -- c ≠ st.maxVBal a
          exact hNoVote_pre x c hle_chain hceq hxcontains hxtype hxbal hxacc
  · -- a ≠ a': all state for a' unchanged, invariant preserved
    simp only [h, ite_false]
    obtain ⟨hle_pre, hVoted_pre, hNoVote_pre⟩ := hAccInv a'
    refine ⟨hle_pre, ?_, ?_⟩
    -- VotedForIn condition preserved
    · intro hmaxVBal_ne
      have hvf := hVoted_pre hmaxVBal_ne
      obtain ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩ := hvf
      have hm'ne : m' ≠ newMsg := by
        intro heq
        rw [heq] at hm'acc
        -- hm'acc : newMsg.acc = a', i.e., a = a'
        -- h : ¬(a = a')
        exact h hm'acc
      refine ⟨m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
      rw [TSet.contains_insert_other _ _ _ hm'ne]
      exact hm'contains
    -- NoVote condition preserved
    · intro x c hle' hne' hxcontains hxtype hxbal hxacc
      by_cases hxeq : x = newMsg
      · -- x is the new message, but its acc = a ≠ a'
        subst hxeq
        -- hxacc : newMsg.acc = a', i.e., a = a'
        -- h : ¬(a = a')
        exact h hxacc
      · rw [TSet.contains_insert_other _ _ _ hxeq] at hxcontains
        exact hNoVote_pre x c hle' hne' hxcontains hxtype hxbal hxacc

end Paxos
