import Veil
import Examples.Paxos.PaxosSpec

namespace Paxos

@[veil]
theorem Phase1a_MsgInv2a (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@MsgInv2a ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  -- Phase1a only adds a Phase1a message, so MsgInv2a for Phase2a messages is preserved
  intro _ _ hcontains hmsgtype
  -- The newly inserted message is a Phase1a message, not Phase2a
  have hne : m ≠ { msgType := MsgType.Phase1a, acc := default, val := default, bal := b, maxVBal := default } := by
    intro heq
    rw [heq] at hmsgtype
    simp at hmsgtype
  -- So m was in the pre-state msgs
  rw [TSet.contains_insert_other _ _ _ hne] at hcontains
  -- Extract MsgInv2a from hinv (it's the 4th component)
  obtain ⟨_, _, _, hMsgInv2a, _⟩ := hinv
  -- Apply the pre-state MsgInv2a invariant
  obtain ⟨hSafeAt, hUnique⟩ := hMsgInv2a m hcontains hmsgtype
  refine ⟨?_, ?_⟩
  -- SafeAt: need to show VotedForIn/WontVoteIn witnesses exist in post-state
  -- SafeAt involves ∃ Q, ∀ a ∈ Q, VotedForIn or WontVoteIn
  -- VotedForIn witnesses are Phase2b messages which lift to post-state
  -- WontVoteIn involves ¬VotedForIn (which is about Phase2b messages) and maxBal (unchanged)
  · intro c hlt hne' hne_none
    obtain ⟨Q, hQ⟩ := hSafeAt c hlt hne' hne_none
    refine ⟨Q, ?_⟩
    intro a ha
    rcases hQ a ha with ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩ | ⟨hnoVote, hmaxBal1, hmaxBal2⟩
    -- Case: VotedForIn - lift the Phase2b witness to post-state
    · left
      have hm'ne : m' ≠ { msgType := MsgType.Phase1a, acc := default, val := default, bal := b, maxVBal := default } := by
        intro heq'
        rw [heq'] at hm'type
        simp at hm'type
      refine ⟨m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
      rw [TSet.contains_insert_other _ _ _ hm'ne]
      exact hm'contains
    -- Case: WontVoteIn - Phase1a doesn't add Phase2b messages and doesn't change maxBal
    · right
      refine ⟨?_, hmaxBal1, hmaxBal2⟩
      intro x hxcontains hxtype hxbal
      have hxne : x ≠ { msgType := MsgType.Phase1a, acc := default, val := default, bal := b, maxVBal := default } := by
        intro heq'
        rw [heq'] at hxtype
        simp at hxtype
      rw [TSet.contains_insert_other _ _ _ hxne] at hxcontains
      exact hnoVote x hxcontains hxtype hxbal
  -- Uniqueness: any Phase2a message in post-state was in pre-state
  · intro ma hmacontains hmatype hmabal
    have hmane : ma ≠ { msgType := MsgType.Phase1a, acc := default, val := default, bal := b, maxVBal := default } := by
      intro heq'
      rw [heq'] at hmatype
      simp at hmatype
    rw [TSet.contains_insert_other _ _ _ hmane] at hmacontains
    exact hUnique ma hmacontains hmatype hmabal

end Paxos
