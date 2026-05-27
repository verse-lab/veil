import Veil
import Examples.Paxos.PaxosSpec

namespace Paxos

@[veil]
theorem Phase1a_VotedInv (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@VotedInv ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  -- VotedForIn (Phase2b witnesses) preserved since Phase1a only adds Phase1a message
  -- Intro: m, guard1, guard2, a, v, b', contains, msgtype, val=, bal=, acc=
  intro m _ _ a v b' hcontains hmsgtype hval hbal hacc
  -- m cannot be the newly added Phase1a message since m.msgType = Phase2b
  have hmne : m ≠ { msgType := MsgType.Phase1a, acc := default, val := default, bal := b, maxVBal := default } := by
    intro heq
    rw [heq] at hmsgtype
    simp at hmsgtype
  rw [TSet.contains_insert_other _ _ _ hmne] at hcontains
  -- Extract VotedInv from hinv (it's the 8th component)
  obtain ⟨_, _, _, _, _, _, _, hVotedInv, _⟩ := hinv
  obtain ⟨hSafeAt, hle⟩ := hVotedInv m a v b' hcontains hmsgtype hval hbal hacc
  refine ⟨?_, hle⟩
  -- SafeAt: need to lift Phase2b witnesses to post-state
  intro c hlt hne' hne_none
  obtain ⟨Q, hQ⟩ := hSafeAt c hlt hne' hne_none
  refine ⟨Q, ?_⟩
  intro a' ha'
  rcases hQ a' ha' with ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩ | ⟨hnoVote, hmaxBal1, hmaxBal2⟩
  -- Case: VotedForIn - lift the Phase2b witness
  · left
    have hm'ne : m' ≠ { msgType := MsgType.Phase1a, acc := default, val := default, bal := b, maxVBal := default } := by
      intro heq'
      rw [heq'] at hm'type
      simp at hm'type
    refine ⟨m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
    rw [TSet.contains_insert_other _ _ _ hm'ne]
    exact hm'contains
  -- Case: WontVoteIn - Phase1a doesn't add Phase2b and doesn't change maxBal
  · right
    refine ⟨?_, hmaxBal1, hmaxBal2⟩
    intro x hxcontains hxtype hxbal
    have hxne : x ≠ { msgType := MsgType.Phase1a, acc := default, val := default, bal := b, maxVBal := default } := by
      intro heq'
      rw [heq'] at hxtype
      simp at hxtype
    rw [TSet.contains_insert_other _ _ _ hxne] at hxcontains
    exact hnoVote x hxcontains hxtype hxbal

end Paxos
