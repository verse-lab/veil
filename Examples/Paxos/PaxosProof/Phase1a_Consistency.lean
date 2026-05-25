import Veil
import Examples.Paxos.Paxos

open Paxos

theorem Phase1a_Consistency (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
    [ρ_sub : IsSubReaderOf (@Theory acceptor value quorum ballot MsgSet AcceptorSet) ρ] :
    ∀ (b : ballot),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Phase1a.ext ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub b)
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
  -- Goal: show Consistency is preserved when Phase1a inserts a Phase1a message
  -- Key insight: Phase1a only adds a Phase1a message, but Consistency/Chosen/VotedForIn
  -- only care about Phase2b messages. So any Phase2b message in the new set
  -- was already in the old set.
  intro _ _ v1 v2 b1 q1 hv1 b2 q2 hv2
  -- Extract the Consistency invariant from hinv (it's the first component)
  obtain ⟨hcons, _⟩ := hinv
  -- Use the pre-state Consistency invariant
  apply hcons v1 v2 b1 q1 _ b2 q2
  -- Goal 1 (reversed): show ∀ a, member a q2 → VotedForIn a v2 b2 (in the old set)
  · intro a ha
    obtain ⟨m, hcontains, htype, hval, hbal, hacc⟩ := hv2 a ha
    refine ⟨m, ?_, htype, hval, hbal, hacc⟩
    have hne : m ≠ { msgType := MsgType.Phase1a, acc := default, val := default, bal := b, maxVBal := default } := by
      intro heq
      rw [heq] at htype
      simp at htype
    rw [TSet.contains_insert_other _ _ _ hne] at hcontains
    exact hcontains
  -- Goal 2 (reversed): show ∀ a, member a q1 → VotedForIn a v1 b1 (in the old set)
  · intro a ha
    obtain ⟨m, hcontains, htype, hval, hbal, hacc⟩ := hv1 a ha
    refine ⟨m, ?_, htype, hval, hbal, hacc⟩
    have hne : m ≠ { msgType := MsgType.Phase1a, acc := default, val := default, bal := b, maxVBal := default } := by
      intro heq
      rw [heq] at htype
      simp at htype
    rw [TSet.contains_insert_other _ _ _ hne] at hcontains
    exact hcontains
