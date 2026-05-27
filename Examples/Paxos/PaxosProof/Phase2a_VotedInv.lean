import Veil
import Examples.Paxos.PaxosSpec

namespace Paxos

@[veil]
theorem Phase2a_VotedInv (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@VotedInv ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  -- VotedForIn (Phase2b witnesses) preserved since Phase2a only adds Phase2a message
  -- Phase2a doesn't change maxVBal, so the le constraint still holds
  -- Based on error output, the goal structure after unveil is:
  -- m (Msg), guards (2), picked values (value, quorum, AcceptorSet), guards (3),
  -- then VotedInv args: a (acceptor), v (value), b' (ballot),
  -- then hypotheses: contains, msgtype, val=, bal=, acc=
  intro m _ _ pickedVal _ _ _ _ _ a v' b' hcontains hmsgtype hval hbal hacc
  -- m cannot be the newly added Phase2a message since m.msgType = Phase2b
  let newMsg : Msg acceptor value ballot := { msgType := MsgType.Phase2a, acc := default, val := pickedVal, bal := b, maxVBal := default }
  have hmne : m ≠ newMsg := by
    intro heq
    rw [heq] at hmsgtype
    simp at hmsgtype
  rw [TSet.contains_insert_other _ _ _ hmne] at hcontains
  -- Extract VotedInv from hinv (it's the 8th component)
  obtain ⟨_, _, _, _, _, _, _, hVotedInv, _⟩ := hinv
  obtain ⟨hSafeAt, hle⟩ := hVotedInv m a v' b' hcontains hmsgtype hval hbal hacc
  -- maxVBal is unchanged by Phase2a, so the le constraint still holds
  refine ⟨?_, hle⟩
  -- SafeAt: need to lift Phase2b witnesses to post-state
  intro c hlt hne' hne_none
  obtain ⟨Q', hQ⟩ := hSafeAt c hlt hne' hne_none
  refine ⟨Q', ?_⟩
  intro a'' ha''
  rcases hQ a'' ha'' with ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩ | ⟨hnoVote, hmaxBal1, hmaxBal2⟩
  -- Case: VotedForIn - lift the Phase2b witness
  · left
    have hm'ne : m' ≠ newMsg := by
      intro heq'
      rw [heq'] at hm'type
      simp at hm'type
    refine ⟨m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
    rw [TSet.contains_insert_other _ _ _ hm'ne]
    exact hm'contains
  -- Case: WontVoteIn - Phase2a doesn't add Phase2b and doesn't change maxBal
  · right
    refine ⟨?_, hmaxBal1, hmaxBal2⟩
    intro x hxcontains hxtype hxbal
    have hxne : x ≠ newMsg := by
      intro heq'
      rw [heq'] at hxtype
      simp at hxtype
    rw [TSet.contains_insert_other _ _ _ hxne] at hxcontains
    exact hnoVote x hxcontains hxtype hxbal

end Paxos
