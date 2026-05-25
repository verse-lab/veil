import Veil
import Examples.Paxos.Paxos

open Paxos

theorem Phase1a_MsgInv1b (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@MsgInv1b ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  -- Phase1a only adds a Phase1a message, so MsgInv1b for Phase1b messages is preserved
  -- Introduce the guards and hypotheses
  intro _ _ hcontains hmsgtype
  -- The newly inserted message is a Phase1a message, not Phase1b
  have hne : m ≠ { msgType := MsgType.Phase1a, acc := default, val := default, bal := b, maxVBal := default } := by
    intro heq
    rw [heq] at hmsgtype
    simp at hmsgtype
  -- So m was in the pre-state msgs
  rw [TSet.contains_insert_other _ _ _ hne] at hcontains
  -- Extract MsgInv1b from hinv (it's the 3rd component)
  obtain ⟨_, _, hMsgInv1b, _⟩ := hinv
  -- Apply the pre-state MsgInv1b invariant
  obtain ⟨hbal, hmaxVBal_or, hnoVote⟩ := hMsgInv1b m hcontains hmsgtype
  refine ⟨hbal, ?_, ?_⟩
  -- For the second conjunct (maxVBal), if there's a VotedForIn witness in pre-state,
  -- it's also in post-state since we only added a Phase1a message
  · rcases hmaxVBal_or with ⟨hne', ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩⟩ | heq
    · left
      refine ⟨hne', m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
      -- m' is a Phase2b message, so it's different from the newly inserted Phase1a message
      have hm'ne : m' ≠ { msgType := MsgType.Phase1a, acc := default, val := default, bal := b, maxVBal := default } := by
        intro heq'
        rw [heq'] at hm'type
        simp at hm'type
      rw [TSet.contains_insert_other _ _ _ hm'ne]
      exact hm'contains
    · right; exact heq
  -- For the third conjunct (no votes in gap), if a 2b message is in post-state,
  -- it was in pre-state (since we only added a Phase1a message)
  · intro x c hle1 hne1 hle2 hne2 hxcontains hxtype hxbal
    have hxne : x ≠ { msgType := MsgType.Phase1a, acc := default, val := default, bal := b, maxVBal := default } := by
      intro heq'
      rw [heq'] at hxtype
      simp at hxtype
    rw [TSet.contains_insert_other _ _ _ hxne] at hxcontains
    exact hnoVote x c hle1 hne1 hle2 hne2 hxcontains hxtype hxbal
