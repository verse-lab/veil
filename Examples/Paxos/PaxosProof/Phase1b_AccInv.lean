import Veil
import Examples.Paxos.Paxos

open Paxos

theorem Phase1b_AccInv (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@AccInv ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum quorum_dec_eq
          quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited AcceptorSet
          AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  -- Goal: prove AccInv in post-state
  -- After unveil, `a` (the acceptor doing Phase1b), `t` (trigger Phase1a message), `st` (pre-state) are in scope
  -- Phase1b creates message: { msgType := Phase1b, acc := a, val := st.maxVal a, bal := t.bal, maxVBal := st.maxVBal a }
  -- Updates: maxBal a := t.bal, maxVBal and maxVal unchanged
  intro hcontains a'
  -- Extract the guard from hcontains: t is Phase1a and gt t.bal (st.maxBal a)
  have hpred := TSet.contains_filter _ _ _ hcontains
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
  obtain ⟨_, hle_guard, hne_guard⟩ := hpred
  -- Extract AccInv from hinv
  obtain ⟨_, _, _, _, _, hAccInv, _⟩ := hinv
  -- Case split on whether a' = a
  by_cases h : a = a'
  · -- a = a': need to prove AccInv for the acceptor doing Phase1b
    subst h
    simp only [ite_true]
    obtain ⟨hle_pre, hVoted_pre, hNoVote_pre⟩ := hAccInv a
    refine ⟨?_, ?_, ?_⟩
    -- 1. le (maxVBal a) t.bal: by transitivity from le (maxVBal a) (maxBal a) and le (maxBal a) t.bal
    · exact TotalOrderWithZeroAndNone.le_trans _ _ _ hle_pre hle_guard
    -- 2. maxVBal a ≠ none → VotedForIn a (maxVal a) (maxVBal a) in post-state
    --    maxVBal and maxVal unchanged, VotedForIn only changes with Phase2b messages
    · intro hmaxVBal_ne
      have hvf := hVoted_pre hmaxVBal_ne
      -- hvf : ∃ m, contains m msgs ∧ m.msgType = Phase2b ∧ ...
      obtain ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩ := hvf
      -- The new message is Phase1b, not Phase2b, so m' ≠ new message
      have hm'ne : m' ≠ { msgType := MsgType.Phase1b, acc := a, val := st.maxVal a, bal := m.bal, maxVBal := st.maxVBal a } := by
        intro heq; rw [heq] at hm'type; simp at hm'type
      refine ⟨m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
      rw [TSet.contains_insert_other _ _ _ hm'ne]
      exact hm'contains
    -- 3. For all c > maxVBal a, ¬VotedForIn a v c in post-state
    --    Phase1b sends Phase1b message, not Phase2b, so VotedForIn unchanged
    · intro x c hle hne hxcontains hxtype hxbal
      -- The new message is Phase1b, not Phase2b
      have hxne : x ≠ { msgType := MsgType.Phase1b, acc := a, val := st.maxVal a, bal := m.bal, maxVBal := st.maxVBal a } := by
        intro heq; rw [heq] at hxtype; simp at hxtype
      rw [TSet.contains_insert_other _ _ _ hxne] at hxcontains
      exact hNoVote_pre x c hle hne hxcontains hxtype hxbal
  · -- a ≠ a': all state for a' unchanged, invariant trivially preserved
    simp only [h, ite_false]
    obtain ⟨hle_pre, hVoted_pre, hNoVote_pre⟩ := hAccInv a'
    refine ⟨hle_pre, ?_, ?_⟩
    -- VotedForIn condition preserved
    · intro hmaxVBal_ne
      have hvf := hVoted_pre hmaxVBal_ne
      obtain ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩ := hvf
      have hm'ne : m' ≠ { msgType := MsgType.Phase1b, acc := a, val := st.maxVal a, bal := m.bal, maxVBal := st.maxVBal a } := by
        intro heq; rw [heq] at hm'type; simp at hm'type
      refine ⟨m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
      rw [TSet.contains_insert_other _ _ _ hm'ne]
      exact hm'contains
    -- NoVote condition preserved
    · intro x c hle hne hxcontains hxtype hxbal
      have hxne : x ≠ { msgType := MsgType.Phase1b, acc := a, val := st.maxVal a, bal := m.bal, maxVBal := st.maxVBal a } := by
        intro heq; rw [heq] at hxtype; simp at hxtype
      rw [TSet.contains_insert_other _ _ _ hxne] at hxcontains
      exact hNoVote_pre x c hle hne hxcontains hxtype hxbal
