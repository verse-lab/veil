import Veil
import Examples.Paxos.Paxos

open Paxos

theorem Phase2b_VotedOnce (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@VotedOnce ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  -- VotedOnce: ∀ a1 a2 b v1 v2, VotedForIn a1 v1 b → VotedForIn a2 v2 b → v1 = v2
  -- Phase2b adds a Phase2b message: { msgType := Phase2b, acc := a, val := t.val, bal := t.bal }
  -- Key: use MsgInv2a to show all votes at same ballot have same value
  intro x x_1 hfilter a1 a2 b v1 v2 hx_contains hx_type hx_val hx_bal hx_acc hx1_contains hx1_type hx1_val hx1_bal hx1_acc
  -- The newly added message
  let newMsg : Msg acceptor value ballot := { msgType := MsgType.Phase2b, acc := a, val := m.val, bal := m.bal, maxVBal := default }
  -- Extract invariants from hinv
  obtain ⟨_, _, _, hMsgInv2a, hMsgInv2b, _, _, _, hVotedOnce⟩ := hinv
  -- Determine where x and x_1 came from
  by_cases hxnew : x = newMsg
  · -- x is the new message
    by_cases hx1new : x_1 = newMsg
    · -- Both x and x_1 are the new message: v1 = t.val = v2
      have hv1 : v1 = m.val := by rw [hxnew] at hx_val; exact hx_val.symm
      have hv2 : v2 = m.val := by rw [hx1new] at hx1_val; exact hx1_val.symm
      rw [hv1, hv2]
    · -- x is new, x_1 is from pre-state
      rw [TSet.contains_insert_other _ _ _ hx1new] at hx1_contains
      -- From hxnew: x.val = t.val, so v1 = t.val
      have hv1_eq_tval : v1 = m.val := by rw [hxnew] at hx_val; exact hx_val.symm
      have hb_eq_tbal : b = m.bal := by rw [hxnew] at hx_bal; exact hx_bal.symm
      -- By MsgInv2b, there exists a Phase2a message ma with ma.bal = x_1.bal = b and ma.val = x_1.val
      have hMsgInv2b_x1 := hMsgInv2b x_1 hx1_contains hx1_type
      obtain ⟨⟨ma, hma_contains, hma_type, hma_bal, hma_val⟩, _⟩ := hMsgInv2b_x1
      -- t is a Phase2a message (from hfilter)
      have ht_contains : TSet.contains m st.msgs = true := TSet.contains_of_contains_filter _ _ _ hfilter
      have hpred := TSet.contains_filter _ _ _ hfilter
      simp only [decide_eq_true_eq] at hpred
      obtain ⟨ht_type, _⟩ := hpred
      -- ma.bal = x_1.bal = b = t.bal
      have hma_bal_eq_tbal : ma.bal = m.bal := by
        rw [hma_bal, hx1_bal, hb_eq_tbal]
      -- By MsgInv2a uniqueness: ma = t
      have hMsgInv2a_t := hMsgInv2a m ht_contains ht_type
      obtain ⟨_, hUnique⟩ := hMsgInv2a_t
      have hma_eq_t := hUnique ma hma_contains hma_type hma_bal_eq_tbal
      -- From hma_eq_t: ma = t, so ma.val = t.val
      -- From hma_val: ma.val = x_1.val, so x_1.val = t.val, hence v2 = t.val
      -- Goal: v1 = v2, we have v1 = t.val
      calc v1 = m.val := hv1_eq_tval
           _ = ma.val := by rw [hma_eq_t]
           _ = x_1.val := hma_val
           _ = v2 := hx1_val
  · -- x is from pre-state
    rw [TSet.contains_insert_other _ _ _ hxnew] at hx_contains
    by_cases hx1new : x_1 = newMsg
    · -- x is from pre-state, x_1 is new
      -- From hx1new: x_1.val = t.val, so v2 = t.val
      have hv2_eq_tval : v2 = m.val := by rw [hx1new] at hx1_val; exact hx1_val.symm
      have hb_eq_tbal : b = m.bal := by rw [hx1new] at hx1_bal; exact hx1_bal.symm
      -- By MsgInv2b, there exists a Phase2a message ma with ma.bal = x.bal = b and ma.val = x.val
      have hMsgInv2b_x := hMsgInv2b x hx_contains hx_type
      obtain ⟨⟨ma, hma_contains, hma_type, hma_bal, hma_val⟩, _⟩ := hMsgInv2b_x
      -- t is a Phase2a message (from hfilter)
      have ht_contains : TSet.contains m st.msgs = true := TSet.contains_of_contains_filter _ _ _ hfilter
      have hpred := TSet.contains_filter _ _ _ hfilter
      simp only [decide_eq_true_eq] at hpred
      obtain ⟨ht_type, _⟩ := hpred
      -- ma.bal = x.bal = b = t.bal
      have hma_bal_eq_tbal : ma.bal = m.bal := by
        rw [hma_bal, hx_bal, hb_eq_tbal]
      -- By MsgInv2a uniqueness: ma = t
      have hMsgInv2a_t := hMsgInv2a m ht_contains ht_type
      obtain ⟨_, hUnique⟩ := hMsgInv2a_t
      have hma_eq_t := hUnique ma hma_contains hma_type hma_bal_eq_tbal
      -- From hma_eq_t: ma = t, so ma.val = t.val
      -- From hma_val: ma.val = x.val, so x.val = t.val, hence v1 = t.val
      -- Goal: v1 = v2, we have v2 = t.val
      calc v1 = x.val := hx_val.symm
           _ = ma.val := hma_val.symm
           _ = m.val := by rw [hma_eq_t]
           _ = v2 := hv2_eq_tval.symm
    · -- Both x and x_1 are from pre-state
      rw [TSet.contains_insert_other _ _ _ hx1new] at hx1_contains
      exact hVotedOnce x x_1 a1 a2 b v1 v2 hx_contains hx_type hx_val hx_bal hx_acc hx1_contains hx1_type hx1_val hx1_bal hx1_acc
