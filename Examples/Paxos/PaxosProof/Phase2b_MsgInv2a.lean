import Veil
import Examples.Paxos.Paxos

open Paxos

theorem Phase2b_MsgInv2a (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@MsgInv2a ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
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
  have hne : msg ≠ newMsg := by
    intro heq
    rw [heq] at hmsgtype
    cases hmsgtype
  rw [TSet.contains_insert_other _ _ _ hne] at hm_in_post
  obtain ⟨_, hTypeOK, _, hMsgInv2a, _⟩ := hinv
  obtain ⟨hSafeAt, hUnique⟩ := hMsgInv2a msg hm_in_post hmsgtype
  have hpred := TSet.contains_filter _ _ _ hfilter
  simp only [decide_eq_true_eq] at hpred
  obtain ⟨_, hle_filter⟩ := hpred
  refine ⟨?_, ?_⟩
  · intro c hlt hne' hne_none
    obtain ⟨Q, hQ⟩ := hSafeAt c hlt hne' hne_none
    refine ⟨Q, ?_⟩
    intro a' ha'
    rcases hQ a' ha' with ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩ | ⟨hnoVote, hmaxBal1, hmaxBal2⟩
    · left
      refine ⟨m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
      by_cases hm'eq : m' = newMsg
      · rw [hm'eq]; exact TSet.contains_insert_self _ _
      · rw [TSet.contains_insert_other _ _ _ hm'eq]; exact hm'contains
    · right
      refine ⟨?_, ?_, ?_⟩
      · intro x hxcontains hxtype hxbal
        by_cases hxeq : x = newMsg
        · subst hxeq
          intro ha'eq
          rw [← ha'eq] at hmaxBal1 hmaxBal2
          rw [hxbal] at hle_filter
          have heq_bal := TotalOrderWithZeroAndNone.le_antisymm _ _ hle_filter hmaxBal1
          rw [heq_bal] at hmaxBal2
          exact hmaxBal2 rfl
        · rw [TSet.contains_insert_other _ _ _ hxeq] at hxcontains
          exact hnoVote x hxcontains hxtype hxbal
      · by_cases hacc : a = a'
        · simp only [hacc, ite_true]
          rw [← hacc] at hmaxBal1
          exact TotalOrderWithZeroAndNone.le_trans _ _ _ hmaxBal1 hle_filter
        · simp only [hacc, ite_false]
          exact hmaxBal1
      · by_cases hacc : a = a'
        · simp only [hacc, ite_true]
          intro hc_eq_tbal
          rw [hc_eq_tbal, hacc] at hle_filter
          have heq_bal := TotalOrderWithZeroAndNone.le_antisymm _ _ hle_filter hmaxBal1
          rw [heq_bal] at hmaxBal2
          exact hmaxBal2 rfl
        · simp only [hacc, ite_false]
          exact hmaxBal2
  · intro ma hmacontains hmatype hmabal
    have hmane : ma ≠ newMsg := by
      intro heq'
      rw [heq'] at hmatype
      cases hmatype
    rw [TSet.contains_insert_other _ _ _ hmane] at hmacontains
    exact hUnique ma hmacontains hmatype hmabal
