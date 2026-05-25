import Veil
import Examples.Paxos.Paxos

open Paxos

theorem initializer_two_a_valid_ballot (ρ : Type) (σ : Type) (acceptor : Type)
    [acceptor_dec_eq : DecidableEq.{1} acceptor] [acceptor_inhabited : Inhabited.{1} acceptor] (value : Type)
    [value_dec_eq : DecidableEq.{1} value] [value_inhabited : Inhabited.{1} value] (quorum : Type)
    [quorum_dec_eq : DecidableEq.{1} quorum] [quorum_inhabited : Inhabited.{1} quorum] (ballot : Type)
    [ballot_dec_eq : DecidableEq.{1} ballot] [ballot_inhabited : Inhabited.{1} ballot]
    [tot : TotalOrderWithZeroAndNone ballot] (MsgSet : Type) [MsgSet_dec_eq : DecidableEq.{1} MsgSet]
    [MsgSet_inhabited : Inhabited.{1} MsgSet] (AcceptorSet : Type) [AcceptorSet_dec_eq : DecidableEq.{1} AcceptorSet]
    [AcceptorSet_inhabited : Inhabited.{1} AcceptorSet] [msgTset : TSet (Msg acceptor value ballot) MsgSet]
    [acSet : TSet acceptor AcceptorSet] (χ : State.Label → Type)
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
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@initializer.ext ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
        quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
        AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
        quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
        AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet ρ_sub)
      (fun _ _ => True)
      (@two_a_valid_ballot ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
        quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
        AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  -- two_a_valid_ballot holds vacuously because msgs is empty
  intro hcontains
  have hempty := @TSet.empty_contains _ _ msgTset m
  simp_all
