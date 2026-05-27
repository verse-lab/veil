import Veil
import Examples.Paxos.PaxosSpec

namespace Paxos

@[veil]
theorem Phase1b_VotedInv (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@VotedInv ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro voteMsg hguard a' v b' hmcontains hmsgtype hval hbal hacc
  let newMsg : Msg acceptor value ballot := { msgType := MsgType.Phase1b, acc := a, val := st.maxVal a, bal := m.bal, maxVBal := st.maxVBal a }
  have hmne : voteMsg ≠ newMsg := by
    intro heq
    rw [heq] at hmsgtype
    simp at hmsgtype
  rw [TSet.contains_insert_other _ _ _ hmne] at hmcontains
  obtain ⟨_, _, _, _, _, _, _, hVotedInv, _⟩ := hinv
  obtain ⟨hSafeAt, hle⟩ := hVotedInv voteMsg a' v b' hmcontains hmsgtype hval hbal hacc
  refine ⟨?_, hle⟩
  intro c hlt hne' hne_none
  obtain ⟨Q, hQ⟩ := hSafeAt c hlt hne' hne_none
  refine ⟨Q, ?_⟩
  intro a'' ha''
  rcases hQ a'' ha'' with ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩ | ⟨hnoVote, hmaxBal1, hmaxBal2⟩
  · left
    have hm'ne : m' ≠ newMsg := by
      intro heq'
      rw [heq'] at hm'type
      simp at hm'type
    refine ⟨m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
    rw [TSet.contains_insert_other _ _ _ hm'ne]
    exact hm'contains
  · right
    have hfilter := TSet.contains_filter _ _ _ hguard
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfilter
    obtain ⟨_, hgt_le, hgt_ne⟩ := hfilter
    refine ⟨?_, ?_, ?_⟩
    · intro y hycontains hytype hybal
      have hyne : y ≠ newMsg := by
        intro heq'
        rw [heq'] at hytype
        simp at hytype
      rw [TSet.contains_insert_other _ _ _ hyne] at hycontains
      exact hnoVote y hycontains hytype hybal
    · by_cases ha''eq : a = a''
      · subst ha''eq
        simp only [ite_true]
        exact TotalOrderWithZeroAndNone.le_trans c (st.maxBal a) m.bal hmaxBal1 hgt_le
      · simp only [if_neg ha''eq]
        exact hmaxBal1
    · by_cases ha''eq : a = a''
      · subst ha''eq
        simp only [ite_true]
        intro heq
        rw [heq] at hgt_le
        have hle_anti := TotalOrderWithZeroAndNone.le_antisymm c (st.maxBal a) hmaxBal1 hgt_le
        exact hmaxBal2 hle_anti.symm
      · simp only [if_neg ha''eq]
        exact hmaxBal2

end Paxos
