import Veil
import Examples.Paxos.Paxos

open Paxos

set_option maxHeartbeats 400000

theorem Phase2b_Consistency (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@Consistency ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro hfilter val1 val2 bal1 quorum1 hvote1 bal2 quorum2 hvote2
  let newMsg : Msg acceptor value ballot := {
    msgType := MsgType.Phase2b,
    acc := a,
    val := m.val,
    bal := m.bal,
    maxVBal := default
  }
  obtain ⟨hcons, _, _, hMsgInv2a, hMsgInv2b, _, htwo_a_valid, hVotedInv, hVotedOnce⟩ := hinv
  have ht_in_msgs : TSet.contains m st.msgs = true := TSet.contains_of_contains_filter _ _ _ hfilter
  have hpred := TSet.contains_filter _ _ _ hfilter
  simp only [decide_eq_true_eq] at hpred
  obtain ⟨ht_type, hge_filter⟩ := hpred
  have votes_at_t_bal_have_t_val : ∀ (voteMsg : Msg acceptor value ballot),
      TSet.contains voteMsg (msgTset.insert newMsg st.msgs) = true →
      voteMsg.msgType = MsgType.Phase2b →
      voteMsg.bal = m.bal →
      voteMsg.val = m.val := by
    intro voteMsg hm_contains hm_type hm_bal
    by_cases hm_eq : voteMsg = newMsg
    · subst hm_eq
      rfl
    · rw [TSet.contains_insert_other _ _ _ hm_eq] at hm_contains
      obtain ⟨⟨ma, hma_contains, hma_type, hma_bal, hma_val⟩, _⟩ := hMsgInv2b voteMsg hm_contains hm_type
      obtain ⟨_, hunique⟩ := hMsgInv2a m ht_in_msgs ht_type
      have hma_bal' : ma.bal = m.bal := hma_bal.trans hm_bal
      have hma_eq_t : ma = m := hunique ma hma_contains hma_type hma_bal'
      rw [← hma_val, hma_eq_t]
  have chosen_at_t_bal_is_t_val : ∀ v b Q,
      b = m.bal →
      (∀ acc', th.member acc' Q = true →
        ∃ m, TSet.contains m (msgTset.insert newMsg st.msgs) = true ∧
             m.msgType = MsgType.Phase2b ∧ m.val = v ∧ m.bal = b ∧ m.acc = acc') →
      v = m.val := by
    intro v b Q hb_eq hvotes
    obtain ⟨acc', hmem', _⟩ := has.1 Q Q
    obtain ⟨voteMsg, hm_contains, hm_type, hm_val, hm_bal, _⟩ := hvotes acc' hmem'
    have hm_val_eq : voteMsg.val = m.val := votes_at_t_bal_have_t_val voteMsg hm_contains hm_type (hm_bal.trans hb_eq)
    rw [← hm_val, hm_val_eq]
  by_cases hbal1 : bal1 = m.bal
  · have hval1 : val1 = m.val := chosen_at_t_bal_is_t_val val1 bal1 quorum1 hbal1 hvote1
    by_cases hbal2 : bal2 = m.bal
    · have hval2 : val2 = m.val := chosen_at_t_bal_is_t_val val2 bal2 quorum2 hbal2 hvote2
      rw [hval1, hval2]
    · have hvote2_pre : ∀ acc', th.member acc' quorum2 = true →
          ∃ m, TSet.contains m st.msgs = true ∧ m.msgType = MsgType.Phase2b ∧ m.val = val2 ∧ m.bal = bal2 ∧ m.acc = acc' := by
        intro acc' hmem'
        obtain ⟨m, hm_contains, hm_type, hm_val, hm_bal, hm_acc⟩ := hvote2 acc' hmem'
        have hm_ne : m ≠ newMsg := by
          intro heq
          subst heq
          exact hbal2 hm_bal.symm
        rw [TSet.contains_insert_other _ _ _ hm_ne] at hm_contains
        exact ⟨m, hm_contains, hm_type, hm_val, hm_bal, hm_acc⟩
      obtain ⟨hSafeAt_t, _⟩ := hMsgInv2a m ht_in_msgs ht_type
      obtain ⟨acc2, hmem2, _⟩ := has.1 quorum2 quorum2
      obtain ⟨m2, hm2_contains, hm2_type, hm2_val, hm2_bal, _⟩ := hvote2_pre acc2 hmem2
      have hVotedInv2 := hVotedInv m2 m2.acc val2 bal2 hm2_contains hm2_type hm2_val hm2_bal rfl
      obtain ⟨hSafeAt_val2, _⟩ := hVotedInv2
      have hne : bal2 ≠ m.bal := hbal2
      by_cases hlt_bal2_t : tot.le bal2 m.bal
      · obtain ⟨⟨ma2, hma2_contains, hma2_type, hma2_bal, _⟩, _⟩ := hMsgInv2b m2 hm2_contains hm2_type
        have hbal2_ne_none : bal2 ≠ tot.none := by
          have hne' := htwo_a_valid ma2 hma2_contains hma2_type
          have hma2_bal_eq : ma2.bal = bal2 := hma2_bal.trans hm2_bal
          rw [hma2_bal_eq] at hne'
          exact hne'
        obtain ⟨Q', hQ'⟩ := hSafeAt_t bal2 hlt_bal2_t hne hbal2_ne_none
        obtain ⟨acc', hmemQ', hmem2'⟩ := has.1 Q' quorum2
        have hQ'_acc' := hQ' acc' hmemQ'
        have hvote2_acc' := hvote2_pre acc' hmem2'
        cases hQ'_acc' with
        | inl hvoted_t =>
          obtain ⟨mt, hmt_contains, hmt_type, hmt_val, hmt_bal, hmt_acc⟩ := hvoted_t
          obtain ⟨mv2, hmv2_contains, hmv2_type, hmv2_val, hmv2_bal, hmv2_acc⟩ := hvote2_acc'
          have heq := hVotedOnce mt mv2 acc' acc' bal2 m.val val2 hmt_contains hmt_type hmt_val hmt_bal hmt_acc hmv2_contains hmv2_type hmv2_val hmv2_bal hmv2_acc
          rw [hval1, heq]
        | inr hwont =>
          obtain ⟨hno_vote, _⟩ := hwont
          obtain ⟨mv2, hmv2_contains, hmv2_type, _, hmv2_bal, hmv2_acc⟩ := hvote2_acc'
          exact absurd hmv2_acc (hno_vote mv2 hmv2_contains hmv2_type hmv2_bal)
      · have hle_t_bal2 : tot.le m.bal bal2 := by
          have htri := tot.le_total bal2 m.bal
          cases htri with
          | inl h => exact absurd h hlt_bal2_t
          | inr h => exact h
        have hne_t_bal2 : m.bal ≠ bal2 := Ne.symm hne
        have ht_bal_ne_none : m.bal ≠ tot.none := htwo_a_valid m ht_in_msgs ht_type
        obtain ⟨Q', hQ'⟩ := hSafeAt_val2 m.bal hle_t_bal2 hne_t_bal2 ht_bal_ne_none
        obtain ⟨acc', hmemQ', hmem1'⟩ := has.1 Q' quorum1
        have hQ'_acc' := hQ' acc' hmemQ'
        obtain ⟨m1, hm1_contains, hm1_type, hm1_val, hm1_bal, hm1_acc⟩ := hvote1 acc' hmem1'
        cases hQ'_acc' with
        | inl hvoted_val2 =>
          by_cases hacc' : acc' = a
          · obtain ⟨m_val2, hm_val2_contains, hm_val2_type, hm_val2_val, hm_val2_bal, _⟩ := hvoted_val2
            obtain ⟨⟨ma_val2, hma_contains, hma_type, hma_bal, hma_val⟩, _⟩ := hMsgInv2b m_val2 hm_val2_contains hm_val2_type
            obtain ⟨_, hunique⟩ := hMsgInv2a m ht_in_msgs ht_type
            have hma_bal' : ma_val2.bal = m.bal := hma_bal.trans hm_val2_bal
            have hma_eq_t := hunique ma_val2 hma_contains hma_type hma_bal'
            have hval2_eq : val2 = m.val := by
              calc val2 = m_val2.val := hm_val2_val.symm
                   _ = ma_val2.val := hma_val.symm
                   _ = m.val := by rw [hma_eq_t]
            rw [hval1, hval2_eq]
          · have hm1_ne : m1 ≠ newMsg := by
              intro heq
              subst heq
              exact hacc' hm1_acc.symm
            rw [TSet.contains_insert_other _ _ _ hm1_ne] at hm1_contains
            obtain ⟨m_val2, hm_val2_contains, hm_val2_type, hm_val2_val, hm_val2_bal, hm_val2_acc⟩ := hvoted_val2
            have hm1_val' : m1.val = m.val := hm1_val.trans hval1
            have hm1_bal' : m1.bal = m.bal := hm1_bal.trans hbal1
            have heq := hVotedOnce m1 m_val2 acc' acc' m.bal m.val val2 hm1_contains hm1_type hm1_val' hm1_bal' hm1_acc hm_val2_contains hm_val2_type hm_val2_val hm_val2_bal hm_val2_acc
            rw [hval1, heq]
        | inr hwont =>
          by_cases hacc' : acc' = a
          · subst hacc'
            obtain ⟨_, hgt⟩ := hwont
            obtain ⟨hle_t_maxBal, hne_maxBal_t⟩ := hgt
            have hantisym := TotalOrderWithZeroAndNone.le_antisymm _ _ hge_filter hle_t_maxBal
            exact absurd hantisym hne_maxBal_t
          · have hm1_ne : m1 ≠ newMsg := by
              intro heq
              subst heq
              exact hacc' hm1_acc.symm
            rw [TSet.contains_insert_other _ _ _ hm1_ne] at hm1_contains
            have hm1_val' : m1.val = m.val := hm1_val.trans hval1
            have hm1_bal' : m1.bal = m.bal := hm1_bal.trans hbal1
            obtain ⟨hno_vote, _⟩ := hwont
            exact absurd hm1_acc (hno_vote m1 hm1_contains hm1_type hm1_bal')
  · have hvote1_pre : ∀ acc', th.member acc' quorum1 = true →
        ∃ m, TSet.contains m st.msgs = true ∧ m.msgType = MsgType.Phase2b ∧ m.val = val1 ∧ m.bal = bal1 ∧ m.acc = acc' := by
      intro acc' hmem'
      obtain ⟨m', hm'_contains, hm'_type, hm'_val, hm'_bal, hm'_acc⟩ := hvote1 acc' hmem'
      have hm'_ne : m' ≠ newMsg := by
        intro heq
        subst heq
        exact hbal1 hm'_bal.symm
      rw [TSet.contains_insert_other _ _ _ hm'_ne] at hm'_contains
      exact ⟨m', hm'_contains, hm'_type, hm'_val, hm'_bal, hm'_acc⟩
    by_cases hbal2 : bal2 = m.bal
    · have hval2 : val2 = m.val := chosen_at_t_bal_is_t_val val2 bal2 quorum2 hbal2 hvote2
      obtain ⟨hSafeAt_t, _⟩ := hMsgInv2a m ht_in_msgs ht_type
      obtain ⟨acc1, hmem1, _⟩ := has.1 quorum1 quorum1
      obtain ⟨m1, hm1_contains, hm1_type, hm1_val, hm1_bal, _⟩ := hvote1_pre acc1 hmem1
      have hVotedInv1 := hVotedInv m1 m1.acc val1 bal1 hm1_contains hm1_type hm1_val hm1_bal rfl
      obtain ⟨hSafeAt_val1, _⟩ := hVotedInv1
      have hne : bal1 ≠ m.bal := hbal1
      by_cases hlt_bal1_t : tot.le bal1 m.bal
      · obtain ⟨⟨ma1, hma1_contains, hma1_type, hma1_bal, _⟩, _⟩ := hMsgInv2b m1 hm1_contains hm1_type
        have hbal1_ne_none : bal1 ≠ tot.none := by
          have hne' := htwo_a_valid ma1 hma1_contains hma1_type
          have hma1_bal_eq : ma1.bal = bal1 := hma1_bal.trans hm1_bal
          rw [hma1_bal_eq] at hne'
          exact hne'
        obtain ⟨Q', hQ'⟩ := hSafeAt_t bal1 hlt_bal1_t hne hbal1_ne_none
        obtain ⟨acc', hmemQ', hmem1'⟩ := has.1 Q' quorum1
        have hQ'_acc' := hQ' acc' hmemQ'
        have hvote1_acc' := hvote1_pre acc' hmem1'
        cases hQ'_acc' with
        | inl hvoted_t =>
          obtain ⟨mt, hmt_contains, hmt_type, hmt_val, hmt_bal, hmt_acc⟩ := hvoted_t
          obtain ⟨mv1, hmv1_contains, hmv1_type, hmv1_val, hmv1_bal, hmv1_acc⟩ := hvote1_acc'
          have heq := hVotedOnce mt mv1 acc' acc' bal1 m.val val1 hmt_contains hmt_type hmt_val hmt_bal hmt_acc hmv1_contains hmv1_type hmv1_val hmv1_bal hmv1_acc
          rw [hval2, heq]
        | inr hwont =>
          obtain ⟨hno_vote, _⟩ := hwont
          obtain ⟨mv1, hmv1_contains, hmv1_type, _, hmv1_bal, hmv1_acc⟩ := hvote1_acc'
          exact absurd hmv1_acc (hno_vote mv1 hmv1_contains hmv1_type hmv1_bal)
      · have hle_t_bal1 : tot.le m.bal bal1 := by
          have htri := tot.le_total bal1 m.bal
          cases htri with
          | inl h => exact absurd h hlt_bal1_t
          | inr h => exact h
        have hne_t_bal1 : m.bal ≠ bal1 := Ne.symm hne
        have ht_bal_ne_none : m.bal ≠ tot.none := htwo_a_valid m ht_in_msgs ht_type
        obtain ⟨Q', hQ'⟩ := hSafeAt_val1 m.bal hle_t_bal1 hne_t_bal1 ht_bal_ne_none
        obtain ⟨acc', hmemQ', hmem2'⟩ := has.1 Q' quorum2
        have hQ'_acc' := hQ' acc' hmemQ'
        obtain ⟨m2, hm2_contains, hm2_type, hm2_val, hm2_bal, hm2_acc⟩ := hvote2 acc' hmem2'
        cases hQ'_acc' with
        | inl hvoted_val1 =>
          rw [hbal2] at hm2_bal
          by_cases hm2_eq : m2 = newMsg
          · subst hm2_eq
            have hacc' : acc' = a := by simp only [newMsg] at hm2_acc; exact hm2_acc.symm
            subst hacc'
            obtain ⟨m_val1, hm_val1_contains, hm_val1_type, hm_val1_val, hm_val1_bal, _⟩ := hvoted_val1
            obtain ⟨⟨ma_val1, hma_contains, hma_type, hma_bal, hma_val⟩, _⟩ := hMsgInv2b m_val1 hm_val1_contains hm_val1_type
            obtain ⟨_, hunique⟩ := hMsgInv2a m ht_in_msgs ht_type
            have hma_bal' : ma_val1.bal = m.bal := hma_bal.trans hm_val1_bal
            have hma_eq_t := hunique ma_val1 hma_contains hma_type hma_bal'
            have hval1_eq : val1 = m.val := by rw [← hm_val1_val, ← hma_val, hma_eq_t]
            rw [hval1_eq, hval2]
          · rw [TSet.contains_insert_other _ _ _ hm2_eq] at hm2_contains
            obtain ⟨m_val1, hm_val1_contains, hm_val1_type, hm_val1_val, hm_val1_bal, hm_val1_acc⟩ := hvoted_val1
            have hm2_val_eq : m2.val = m.val := hm2_val.trans hval2
            have hvote2_pre : TSet.contains m2 st.msgs = true ∧
                m2.msgType = MsgType.Phase2b ∧ m2.val = m.val ∧ m2.bal = m.bal ∧ m2.acc = acc' := by
              exact ⟨hm2_contains, hm2_type, hm2_val_eq, hm2_bal, hm2_acc⟩
            have heq := hVotedOnce m_val1 m2 acc' acc' m.bal val1 m.val hm_val1_contains hm_val1_type hm_val1_val hm_val1_bal hm_val1_acc hvote2_pre.1 hvote2_pre.2.1 hvote2_pre.2.2.1 hvote2_pre.2.2.2.1 hvote2_pre.2.2.2.2
            rw [hval2, ← heq]
        | inr hwont =>
          by_cases hm2_eq : m2 = newMsg
          · subst hm2_eq
            have hacc' : acc' = a := by simp only [newMsg] at hm2_acc; exact hm2_acc.symm
            subst hacc'
            obtain ⟨_, hgt⟩ := hwont
            obtain ⟨hle_t_maxBal, hne_maxBal_t⟩ := hgt
            have hantisym := TotalOrderWithZeroAndNone.le_antisymm _ _ hge_filter hle_t_maxBal
            exact absurd hantisym hne_maxBal_t
          · rw [TSet.contains_insert_other _ _ _ hm2_eq] at hm2_contains
            have hm2_val_eq : m2.val = m.val := hm2_val.trans hval2
            have hvote2_pre : TSet.contains m2 st.msgs = true ∧
                m2.msgType = MsgType.Phase2b ∧ m2.val = m.val ∧ m2.bal = m.bal ∧ m2.acc = acc' := by
              exact ⟨hm2_contains, hm2_type, hm2_val_eq, hm2_bal.trans hbal2, hm2_acc⟩
            obtain ⟨hno_vote, _⟩ := hwont
            exact absurd hvote2_pre.2.2.2.2 (hno_vote m2 hvote2_pre.1 hvote2_pre.2.1 hvote2_pre.2.2.2.1)
    · have hvote2_pre : ∀ acc', th.member acc' quorum2 = true →
          ∃ m, TSet.contains m st.msgs = true ∧ m.msgType = MsgType.Phase2b ∧ m.val = val2 ∧ m.bal = bal2 ∧ m.acc = acc' := by
        intro acc' hmem'
        obtain ⟨m', hm'_contains, hm'_type, hm'_val, hm'_bal, hm'_acc⟩ := hvote2 acc' hmem'
        have hm'_ne : m' ≠ newMsg := by
          intro heq
          subst heq
          exact hbal2 hm'_bal.symm
        rw [TSet.contains_insert_other _ _ _ hm'_ne] at hm'_contains
        exact ⟨m', hm'_contains, hm'_type, hm'_val, hm'_bal, hm'_acc⟩
      exact hcons val1 val2 bal1 quorum1 hvote1_pre bal2 quorum2 hvote2_pre
