import Veil
import Examples.Paxos.Paxos

open Paxos

theorem Phase2a_VotedOnce (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@VotedOnce ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  -- VotedOnce: ∀ a1 a2 b v1 v2, VotedForIn a1 v1 b → VotedForIn a2 v2 b → v1 = v2
  -- VotedForIn requires Phase2b messages
  -- Phase2a only adds a Phase2a message, so Phase2b messages are preserved
  -- Use `intros` to introduce all hypotheses automatically
  intros
  rename_i m1 m2 _ _ selectedVal _ _ _ _ _ _ _ _ _ _ hm1_contains hm1_type hm1_val hm1_bal hm1_acc hm2_contains hm2_type hm2_val hm2_bal hm2_acc
  -- The newly added message is a Phase2a message
  let newMsg : Msg acceptor value ballot := { msgType := MsgType.Phase2a, acc := default, val := selectedVal, bal := b, maxVBal := default }
  -- m1 cannot be the newly added Phase2a message (m1 must be Phase2b)
  have hm1_ne : m1 ≠ newMsg := by
    intro heq; rw [heq] at hm1_type; simp at hm1_type
  -- m2 cannot be the newly added Phase2a message (m2 must be Phase2b)
  have hm2_ne : m2 ≠ newMsg := by
    intro heq; rw [heq] at hm2_type; simp at hm2_type
  -- Since m1 ≠ newMsg and m2 ≠ newMsg, they were in the pre-state
  rw [TSet.contains_insert_other _ _ _ hm1_ne] at hm1_contains
  rw [TSet.contains_insert_other _ _ _ hm2_ne] at hm2_contains
  -- Extract VotedOnce from hinv (it's the 9th/last component)
  obtain ⟨_, _, _, _, _, _, _, _, hVotedOnce⟩ := hinv
  exact hVotedOnce m1 m2 _ _ _ _ _ hm1_contains hm1_type hm1_val hm1_bal hm1_acc hm2_contains hm2_type hm2_val hm2_bal hm2_acc
