import Veil
import Examples.Paxos.PaxosSpec

namespace Paxos

@[veil]
theorem Phase2b_VotedInv (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@VotedInv ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro voteMsg hguard a' v b hm_in_post hmsgtype hval hbal hacc
  let newMsg : Msg acceptor value ballot := {
    msgType := MsgType.Phase2b,
    acc := a,
    val := m.val,
    bal := m.bal,
    maxVBal := default
  }
  obtain ⟨_, hTypeOK, hMsgInv1b, hMsgInv2a, hMsgInv2b, hAccInv, _, hVotedInv, _⟩ := hinv
  have hpred := @TSet.contains_filter _ _ msgTset m _ _ hguard
  simp only [decide_eq_true_iff] at hpred
  have ht_contains := TSet.contains_of_contains_filter _ _ _ hguard
  have ht_type : m.msgType = MsgType.Phase2a := hpred.1
  have hle_filter : TotalOrderWithZeroAndNone.le (st.maxBal a) m.bal := hpred.2
  by_cases hmeq : voteMsg = newMsg
  · -- Case: m is the new Phase2b message
    rw [hmeq] at hval hbal hacc
    -- newMsg.val = t.val, newMsg.bal = t.bal, newMsg.acc = a
    -- So v = t.val, b = t.bal, a' = a
    have hSafeAt_t := (hMsgInv2a m ht_contains ht_type).1
    refine ⟨?_, ?_⟩
    · -- SafeAt part: show SafeAt v b in post-state
      intro c hlt hne' hne_none
      rw [← hval]
      -- Since hbal : newMsg.bal = b, we have b = t.bal
      obtain ⟨Q, hQ⟩ := hSafeAt_t c (hbal ▸ hlt) (hbal ▸ hne') hne_none
      refine ⟨Q, ?_⟩
      intro a'' ha''
      rcases hQ a'' ha'' with ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩ | ⟨hnoVote, hmaxBal_le, hmaxBal_ne⟩
      · -- VotedForIn case: lift witness to post-state
        left
        refine ⟨m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
        by_cases hm'eq : m' = newMsg
        · rw [hm'eq]; exact TSet.contains_insert_self _ _
        · rw [TSet.contains_insert_other _ _ _ hm'eq]; exact hm'contains
      · -- WontVoteIn case
        right
        refine ⟨?_, ?_, ?_⟩
        · -- No Phase2b vote at ballot c
          intro x hxcontains hxtype hxbal
          by_cases hxeq : x = newMsg
          · -- x is the new message, so x.bal = t.bal
            -- We need to show x.acc ≠ a''
            -- hxbal : x.bal = c, and after hxeq, newMsg.bal = c means t.bal = c
            -- hbal : newMsg.bal = b means t.bal = b
            -- So c = t.bal = b, contradicting hne' : ¬ c = b
            intro hacc_eq
            rw [hxeq] at hxbal
            -- hxbal : newMsg.bal = c means t.bal = c
            -- hbal : newMsg.bal = b means t.bal = b
            -- So c = b (by transitivity via t.bal)
            have hceqb : c = b := hxbal.symm.trans hbal
            exact hne' hceqb
          · rw [TSet.contains_insert_other _ _ _ hxeq] at hxcontains
            exact hnoVote x hxcontains hxtype hxbal
        · -- maxBal ordering
          by_cases ha : a = a''
          · rw [if_pos ha]
            rw [← ha] at hmaxBal_le
            exact TotalOrderWithZeroAndNone.le_trans _ _ _ hmaxBal_le hle_filter
          · rw [if_neg ha]
            exact hmaxBal_le
        · -- maxBal not equal c
          by_cases ha : a = a''
          · rw [if_pos ha]
            -- Goal: ¬ t.bal = c
            -- hbal : newMsg.bal = b means t.bal = b
            -- hne' : ¬ c = b
            -- If t.bal = c, then b = c (from hbal.symm), so c = b, contradicting hne'
            intro heq
            -- heq : t.bal = c
            -- hbal : t.bal = b (since newMsg.bal = t.bal)
            have hceqb : c = b := heq.symm.trans hbal
            exact hne' hceqb
          · rw [if_neg ha]
            exact hmaxBal_ne
    · -- Show le b (post-state maxVBal a')
      -- hacc : newMsg.acc = a', so a = a'
      -- hbal : newMsg.bal = b, so t.bal = b
      -- Post-state: maxVBal a = t.bal
      -- Goal: le b (if a = a' then t.bal else st.maxVBal a')
      -- Since a = a' (from hacc), goal is le b t.bal = le t.bal t.bal
      rw [← hacc, if_pos rfl, ← hbal]
      exact TotalOrderWithZeroAndNone.le_refl _
  · -- Case: m is not the new message, was in pre-state
    rw [TSet.contains_insert_other _ _ _ hmeq] at hm_in_post
    obtain ⟨hSafeAt_pre, hle_pre⟩ := hVotedInv voteMsg a' v b hm_in_post hmsgtype hval hbal hacc
    refine ⟨?_, ?_⟩
    · -- SafeAt: lift witnesses from pre-state
      intro c hlt hne' hne_none
      obtain ⟨Q, hQ⟩ := hSafeAt_pre c hlt hne' hne_none
      refine ⟨Q, ?_⟩
      intro a'' ha''
      rcases hQ a'' ha'' with ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩ | ⟨hnoVote, hmaxBal_le, hmaxBal_ne⟩
      · -- VotedForIn case
        left
        -- m' is a Phase2b witness from pre-state
        -- We need to lift it to post-state
        refine ⟨m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
        by_cases hm'eq : m' = newMsg
        · rw [hm'eq]; exact TSet.contains_insert_self _ _
        · rw [TSet.contains_insert_other _ _ _ hm'eq]; exact hm'contains
      · -- WontVoteIn case
        right
        refine ⟨?_, ?_, ?_⟩
        · -- No Phase2b vote at ballot c
          intro x hxcontains hxtype hxbal
          by_cases hxeq : x = newMsg
          · -- x is the new message
            -- hxbal : x.bal = c, so after hxeq, newMsg.bal = c means t.bal = c
            -- hmaxBal_le : le c (st.maxBal a'')
            -- hmaxBal_ne : ¬ st.maxBal a'' = c
            -- hle_filter : le (st.maxBal a) t.bal
            -- If a = a'', then le (st.maxBal a) t.bal = le (st.maxBal a'') c
            -- Combined with hmaxBal_le: c ≤ maxBal a'' ≤ c implies maxBal a'' = c
            -- This contradicts hmaxBal_ne
            rw [hxeq] at hxbal
            -- hxbal : newMsg.bal = c means t.bal = c
            intro hacc_eq
            -- hacc_eq : x.acc = a''
            -- After rw [hxeq], hacc_eq becomes newMsg.acc = a'', i.e., a = a''
            rw [hxeq] at hacc_eq
            -- hacc_eq : newMsg.acc = a'' which is a = a''
            -- Now use hacc_eq (which says a = a'') and hxbal (which says t.bal = c)
            -- hle_filter : le (st.maxBal a) t.bal
            -- Substitute a = a'' in hle_filter: le (st.maxBal a'') t.bal
            -- Substitute t.bal = c: le (st.maxBal a'') c
            -- But wait, hle_filter has st.maxBal a, not st.maxBal a''
            -- hacc_eq : newMsg.acc = a'' means a = a'' (since newMsg.acc = a)
            -- So we need to use that a = a''
            have ha_eq : a = a'' := hacc_eq
            rw [ha_eq] at hle_filter
            rw [hxbal] at hle_filter
            -- hle_filter : le (st.maxBal a'') c
            -- hmaxBal_le : le c (st.maxBal a'')
            have heq := TotalOrderWithZeroAndNone.le_antisymm _ _ hle_filter hmaxBal_le
            -- heq : st.maxBal a'' = c
            exact hmaxBal_ne heq
          · rw [TSet.contains_insert_other _ _ _ hxeq] at hxcontains
            exact hnoVote x hxcontains hxtype hxbal
        · -- maxBal ordering
          by_cases ha : a = a''
          · rw [if_pos ha]
            rw [← ha] at hmaxBal_le
            exact TotalOrderWithZeroAndNone.le_trans _ _ _ hmaxBal_le hle_filter
          · rw [if_neg ha]
            exact hmaxBal_le
        · -- maxBal not equal c
          by_cases ha : a = a''
          · rw [if_pos ha]
            -- Post-state maxBal a'' = t.bal (since a = a'')
            -- Need to show ¬ t.bal = c
            -- hmaxBal_le : le c (st.maxBal a'')
            -- hmaxBal_ne : ¬ st.maxBal a'' = c
            -- hle_filter : le (st.maxBal a) t.bal
            -- rw [← ha] at hmaxBal_le gives le c (st.maxBal a)
            intro heq_tbal_c
            rw [← ha] at hmaxBal_le hmaxBal_ne
            rw [heq_tbal_c] at hle_filter
            have heq := TotalOrderWithZeroAndNone.le_antisymm _ _ hle_filter hmaxBal_le
            exact hmaxBal_ne heq
          · rw [if_neg ha]
            exact hmaxBal_ne
    · -- Show le b (post-state maxVBal a')
      by_cases ha : a = a'
      · rw [if_pos ha]
        -- Post-state maxVBal a' = t.bal (since a = a')
        -- Need: le b t.bal
        -- hle_pre : le b (st.maxVBal a')
        -- hTypeOK a' : le (st.maxVBal a') (st.maxBal a')
        -- hle_filter : le (st.maxBal a) t.bal
        -- Since a = a', hle_filter gives: le (st.maxBal a') t.bal
        -- Chain: b ≤ maxVBal a' ≤ maxBal a' ≤ t.bal
        have hle_vbal := hTypeOK a'
        have hle1 := TotalOrderWithZeroAndNone.le_trans _ _ _ hle_pre hle_vbal
        rw [← ha] at hle1
        exact TotalOrderWithZeroAndNone.le_trans _ _ _ hle1 hle_filter
      · rw [if_neg ha]
        exact hle_pre

end Paxos
