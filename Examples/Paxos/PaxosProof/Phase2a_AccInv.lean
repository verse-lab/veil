import Veil
import Examples.Paxos.PaxosSpec

namespace Paxos

@[veil]
theorem Phase2a_AccInv (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
    [Phase2a_dec_0 :
      (b c : ballot) → Decidable (And (@TotalOrderWithZeroAndNone.le ballot tot c b) (Not (@Eq.{1} ballot c b)))]
    [Phase2a_dec_1 :
      (c : ballot) → (m : Msg acceptor value ballot) → Decidable (@TotalOrderWithZeroAndNone.le ballot tot m.5 c)] :
    ∀ (b : ballot),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Phase2a.ext ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub
          Phase2a_dec_0 Phase2a_dec_1 b)
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
  -- Phase2a doesn't change maxVBal, maxBal, or maxVal; only adds a Phase2a message
  -- After unveil: guards come before picks in the goal structure
  -- Skip first 2 guards (b ≠ none, filterMsgs count = 0), then picks (v, Q, selectedAcceptors),
  -- then remaining guards (acceptors have 1b, quorumCovered, allMinusOne ∨ vb), then ∀ a
  intro _ _ v Q selectedAcceptors _ _ _ a
  -- Extract AccInv from hinv (it's the 6th component)
  obtain ⟨_, _, _, _, _, hAccInv, _⟩ := hinv
  obtain ⟨hle, hVoted, hNoVote⟩ := hAccInv a
  refine ⟨hle, ?_, ?_⟩
  -- VotedForIn witness (Phase2b message) is preserved
  · intro hne
    obtain ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩ := hVoted hne
    refine ⟨m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
    have hmne : m' ≠ { msgType := MsgType.Phase2a, acc := default, val := v, bal := b, maxVBal := default } := by
      intro heq
      rw [heq] at hm'type
      simp at hm'type
    rw [TSet.contains_insert_other _ _ _ hmne]
    exact hm'contains
  -- No votes above maxVBal: any Phase2b in post-state was in pre-state
  · intro x c hle' hne hxcontains hxtype hxbal
    have hmne : x ≠ { msgType := MsgType.Phase2a, acc := default, val := v, bal := b, maxVBal := default } := by
      intro heq
      rw [heq] at hxtype
      simp at hxtype
    rw [TSet.contains_insert_other _ _ _ hmne] at hxcontains
    exact hNoVote x c hle' hne hxcontains hxtype hxbal

end Paxos
