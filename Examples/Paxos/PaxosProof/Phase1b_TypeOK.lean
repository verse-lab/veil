import Veil
import Examples.Paxos.PaxosSpec

namespace Paxos

@[veil]
theorem Phase1b_TypeOK (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
    [Phase1b_dec_0 :
      (a : acceptor) →
        (__do_lift : State χ) →
          (m : Msg acceptor value ballot) →
            Decidable
              (And
                (@TotalOrderWithZeroAndNone.le ballot tot
                  (@Veil.FieldRepresentation.get
                    (State.Label.toDomain acceptor value quorum ballot MsgSet AcceptorSet State.Label.maxBal)
                    (State.Label.toCodomain acceptor value quorum ballot MsgSet AcceptorSet State.Label.maxBal)
                    (χ State.Label.maxBal) (χ_rep State.Label.maxBal) __do_lift.3 a)
                  m.4)
                (Not
                  (@Eq.{1} ballot m.4
                    (@Veil.FieldRepresentation.get
                      (State.Label.toDomain acceptor value quorum ballot MsgSet AcceptorSet State.Label.maxBal)
                      (State.Label.toCodomain acceptor value quorum ballot MsgSet AcceptorSet State.Label.maxBal)
                      (χ State.Label.maxBal) (χ_rep State.Label.maxBal) __do_lift.3 a))))] :
    ∀ (a : acceptor),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Phase1b.ext ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub
          Phase1b_dec_0 a)
        (@Assumptions ρ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet ρ_sub)
        (@Invariants ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@TypeOK ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum quorum_dec_eq
          quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited AcceptorSet
          AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  -- Goal: TSet.contains t (filter ...) → ∀ a_2, le (st.maxVBal a_2) (if a = a_2 then t.bal else st.maxBal a_2)
  intro hcontains a'
  -- Extract the guard from hcontains: t is Phase1a and le (st.maxBal a) t.bal
  have hpred := TSet.contains_filter _ _ _ hcontains
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
  obtain ⟨_, hle_guard, _⟩ := hpred
  -- Extract TypeOK from hinv
  obtain ⟨_, hTypeOK, _⟩ := hinv
  -- Case split on whether a' = a
  by_cases h : a = a'
  · -- a = a': need le (st.maxVBal a) t.bal
    subst h
    simp only [ite_true]
    -- By transitivity: le (st.maxVBal a) (st.maxBal a) and le (st.maxBal a) t.bal
    exact TotalOrderWithZeroAndNone.le_trans _ _ _ (hTypeOK a) hle_guard
  · -- a ≠ a': unchanged, need le (st.maxVBal a') (st.maxBal a')
    simp only [h, ite_false]
    exact hTypeOK a'

end Paxos
