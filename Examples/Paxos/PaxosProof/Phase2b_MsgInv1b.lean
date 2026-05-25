import Veil
import Examples.Paxos.Paxos

open Paxos

theorem Phase2b_MsgInv1b (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@MsgInv1b ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro hcontains_t hcontains hmsgtype
  revert hmsgtype hcontains m
  intro msg hcontains hmsgtype
  have hne : msg ≠ { msgType := MsgType.Phase2b, acc := a, val := m.val, bal := m.bal, maxVBal := default } := by
    intro heq
    rw [heq] at hmsgtype
    cases hmsgtype
  rw [TSet.contains_insert_other _ _ _ hne] at hcontains
  obtain ⟨_, _, hMsgInv1b, _⟩ := hinv
  obtain ⟨hbal, hmaxVBal_or, hnoVote⟩ := hMsgInv1b msg hcontains hmsgtype
  have ht_pred := TSet.contains_filter _ _ _ hcontains_t
  simp only [decide_eq_true_eq] at ht_pred
  obtain ⟨ht_type, ht_ge⟩ := ht_pred
  refine ⟨?_, ?_, ?_⟩
  · by_cases hacc : a = msg.acc
    · simp only [hacc, ite_true]
      rw [← hacc] at hbal
      exact TotalOrderWithZeroAndNone.le_trans _ _ _ hbal ht_ge
    · simp only [hacc, ite_false]
      exact hbal
  · rcases hmaxVBal_or with ⟨hne', ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩⟩ | heq_none
    · left
      refine ⟨hne', m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
      by_cases hm'eq : m' = { msgType := MsgType.Phase2b, acc := a, val := m.val, bal := m.bal, maxVBal := default }
      · rw [hm'eq]
        exact TSet.contains_insert_self _ _
      · rw [TSet.contains_insert_other _ _ _ hm'eq]
        exact hm'contains
    · right; exact heq_none
  · intro x c hle1 hne1 hle2 hne2 hxcontains hxtype hxbal
    by_cases hxeq : x = { msgType := MsgType.Phase2b, acc := a, val := m.val, bal := m.bal, maxVBal := default }
    · subst hxeq
      simp only at hxbal
      intro hmacc
      simp only at hmacc
      rw [← hmacc] at hbal
      have hle_m_t := TotalOrderWithZeroAndNone.le_trans _ _ _ hbal ht_ge
      rw [← hxbal] at hle2 hne2
      have heq_bal := TotalOrderWithZeroAndNone.le_antisymm _ _ hle_m_t hle2
      exact hne2 heq_bal.symm
    · rw [TSet.contains_insert_other _ _ _ hxeq] at hxcontains
      exact hnoVote x c hle1 hne1 hle2 hne2 hxcontains hxtype hxbal
