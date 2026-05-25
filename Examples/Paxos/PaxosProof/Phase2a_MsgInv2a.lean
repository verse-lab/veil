import Veil
import Examples.Paxos.Paxos

open Paxos

theorem Phase2a_MsgInv2a (ρ : Type) (σ : Type) (acceptor : Type) [acceptor_dec_eq : DecidableEq.{1} acceptor]
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
        (@MsgInv2a ρ σ acceptor acceptor_dec_eq acceptor_inhabited value value_dec_eq value_inhabited quorum
          quorum_dec_eq quorum_inhabited ballot ballot_dec_eq ballot_inhabited tot MsgSet MsgSet_dec_eq MsgSet_inhabited
          AcceptorSet AcceptorSet_dec_eq AcceptorSet_inhabited msgTset acSet χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro hb_ne hno_existing_2a
  intro v Q selectedAcc
  intro hselectedAcc_have_1b hquorum_covered hallMinusOne_or_vb
  intro hcontains hmsgtype
  let newMsg : Msg acceptor value ballot := { msgType := MsgType.Phase2a, acc := default, val := v, bal := b, maxVBal := default }
  obtain ⟨hConsistency, hTypeOK, hMsgInv1b, hMsgInv2a, hMsgInv2b, hAccInv, h2a_valid_ballot, hVotedInv, hVotedOnce⟩ := hinv
  by_cases hmeq : m = newMsg
  · subst hmeq
    refine ⟨?safeAt_new, ?unique_new⟩
    case safeAt_new =>
      intro c hle_c_b hne_c_b hne_c_none
      simp only [newMsg] at hle_c_b hne_c_b
      -- Case split on allMinusOne vs vb FIRST, then choose quorum
      rcases hallMinusOne_or_vb with hallNone | ⟨maxMsg, hmaxMsg_valid, ⟨hmaxMsg_le_b, hmaxMsg_ne_b⟩, hmaxMsg_bound, hmaxMsg_in_S, hmaxMsg_val⟩
      · -- All 1b have maxVBal = none: use Q for all c, WontVoteIn via interval
        refine ⟨Q, ?_⟩
        intro a' ha'
        have ha'_univ : a' ∈ th.AcceptorsUNIV := has.2.1 a'
        have hquorum_a' := hquorum_covered a' ha'_univ
        simp only [ha'] at hquorum_a'
        rcases hquorum_a' with hfalse | ⟨m1b, hm1b_in_S, hm1b_acc⟩
        · simp at hfalse
        · have hm1b_contains_S : TSet.contains m1b (TSet.filter (TSet.filter st.msgs (fun m => decide (m.msgType = MsgType.Phase1b) && decide (m.bal = b))) (fun m => TSet.contains m.acc selectedAcc)) = true := by
            rw [TSet.toList_contains_iff]
            exact hm1b_in_S
          have hm1b_contains_inner := TSet.contains_of_contains_filter m1b _ _ hm1b_contains_S
          have hm1b_filter_pred := TSet.contains_filter _ _ _ hm1b_contains_inner
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hm1b_filter_pred
          obtain ⟨hm1b_type, hm1b_bal⟩ := hm1b_filter_pred
          have hm1b_contains : TSet.contains m1b st.msgs = true := TSet.contains_of_contains_filter m1b _ _ hm1b_contains_inner
          have hm1b_inv := hMsgInv1b m1b hm1b_contains hm1b_type
          obtain ⟨hm1b_bal_le_maxBal, _, hm1b_no_vote_interval⟩ := hm1b_inv
          have hmaxBal_ge_b : TotalOrderWithZeroAndNone.le b (st.maxBal a') := by
            rw [← hm1b_acc, ← hm1b_bal]
            exact hm1b_bal_le_maxBal
          have hmaxBal_gt_c : TotalOrderWithZeroAndNone.le c (st.maxBal a') ∧ ¬st.maxBal a' = c := by
            constructor
            · exact TotalOrderWithZeroAndNone.le_trans _ _ _ hle_c_b hmaxBal_ge_b
            · intro heq
              rw [heq] at hmaxBal_ge_b
              have hc_eq_b := TotalOrderWithZeroAndNone.le_antisymm _ _ hle_c_b hmaxBal_ge_b
              exact hne_c_b hc_eq_b
          have hm1b_maxVBal_none : m1b.maxVBal = TotalOrderWithZeroAndNone.none := hallNone m1b hm1b_in_S
          right
          refine ⟨?_, hmaxBal_gt_c.1, hmaxBal_gt_c.2⟩
          intro x hxcontains hxtype hxbal
          have hxne : x ≠ newMsg := by
            intro heq'
            rw [heq'] at hxtype
            simp at hxtype
          rw [TSet.contains_insert_other _ _ _ hxne] at hxcontains
          have hc_in_interval : TotalOrderWithZeroAndNone.le m1b.maxVBal c ∧ ¬m1b.maxVBal = c ∧
                               TotalOrderWithZeroAndNone.le c m1b.bal ∧ ¬c = m1b.bal := by
            rw [hm1b_maxVBal_none, hm1b_bal]
            refine ⟨TotalOrderWithZeroAndNone.none_le c, ?_, hle_c_b, hne_c_b⟩
            intro heq
            exact hne_c_none heq.symm
          rw [← hm1b_acc]
          exact hm1b_no_vote_interval x c hc_in_interval.1 hc_in_interval.2.1 hc_in_interval.2.2.1 hc_in_interval.2.2.2 hxcontains hxtype hxbal
      · -- There's a maxMsg with valid maxVBal
        -- First establish SafeAt(v, maxMsg.maxVBal) via VotedInv
        have hmaxMsg_maxVBal_ne_none : maxMsg.maxVBal ≠ TotalOrderWithZeroAndNone.none :=
          (has.2.2 maxMsg.maxVBal).mpr hmaxMsg_valid
        have hmaxMsg_contains_S : TSet.contains maxMsg (TSet.filter (TSet.filter st.msgs (fun m => decide (m.msgType = MsgType.Phase1b) && decide (m.bal = b))) (fun m => TSet.contains m.acc selectedAcc)) = true := by
          rw [TSet.toList_contains_iff]
          exact hmaxMsg_in_S
        have hmaxMsg_contains_inner := TSet.contains_of_contains_filter maxMsg _ _ hmaxMsg_contains_S
        have hmaxMsg_filter_pred := TSet.contains_filter _ _ _ hmaxMsg_contains_inner
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hmaxMsg_filter_pred
        obtain ⟨hmaxMsg_type, hmaxMsg_bal⟩ := hmaxMsg_filter_pred
        have hmaxMsg_contains : TSet.contains maxMsg st.msgs = true := TSet.contains_of_contains_filter maxMsg _ _ hmaxMsg_contains_inner
        have hmaxMsg_1b_inv := hMsgInv1b maxMsg hmaxMsg_contains hmaxMsg_type
        obtain ⟨_, hmaxMsg_voted_or_none, _⟩ := hmaxMsg_1b_inv
        rcases hmaxMsg_voted_or_none with ⟨_, hVotedForIn_maxMsg⟩ | hmaxMsg_none
        · -- maxMsg voted at maxMsg.maxVBal - get SafeAt via VotedInv
          obtain ⟨m2b_maxMsg, hm2b_maxMsg_contains, hm2b_maxMsg_type, hm2b_maxMsg_val, hm2b_maxMsg_bal, hm2b_maxMsg_acc⟩ := hVotedForIn_maxMsg
          obtain ⟨hSafeAt_maxMsg, _⟩ := hVotedInv m2b_maxMsg maxMsg.acc maxMsg.val maxMsg.maxVBal hm2b_maxMsg_contains hm2b_maxMsg_type hm2b_maxMsg_val hm2b_maxMsg_bal hm2b_maxMsg_acc
          have hSafeAt_v_maxVBal := hSafeAt_maxMsg
          rw [hmaxMsg_val] at hSafeAt_v_maxVBal

          -- Case split on c relative to maxMsg.maxVBal BEFORE choosing quorum
          by_cases hle_maxMsg_c : TotalOrderWithZeroAndNone.le maxMsg.maxVBal c
          · -- c ≥ maxMsg.maxVBal: use Q
            refine ⟨Q, ?_⟩
            intro a' ha'
            have ha'_univ : a' ∈ th.AcceptorsUNIV := has.2.1 a'
            have hquorum_a' := hquorum_covered a' ha'_univ
            simp only [ha'] at hquorum_a'
            rcases hquorum_a' with hfalse | ⟨m1b, hm1b_in_S, hm1b_acc⟩
            · simp at hfalse
            · have hm1b_contains_S : TSet.contains m1b (TSet.filter (TSet.filter st.msgs (fun m => decide (m.msgType = MsgType.Phase1b) && decide (m.bal = b))) (fun m => TSet.contains m.acc selectedAcc)) = true := by
                rw [TSet.toList_contains_iff]
                exact hm1b_in_S
              have hm1b_contains_inner := TSet.contains_of_contains_filter m1b _ _ hm1b_contains_S
              have hm1b_filter_pred := TSet.contains_filter _ _ _ hm1b_contains_inner
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hm1b_filter_pred
              obtain ⟨hm1b_type, hm1b_bal⟩ := hm1b_filter_pred
              have hm1b_contains : TSet.contains m1b st.msgs = true := TSet.contains_of_contains_filter m1b _ _ hm1b_contains_inner
              have hm1b_inv := hMsgInv1b m1b hm1b_contains hm1b_type
              obtain ⟨hm1b_bal_le_maxBal, hm1b_voted_or_none, hm1b_no_vote_interval⟩ := hm1b_inv
              have hmaxBal_ge_b : TotalOrderWithZeroAndNone.le b (st.maxBal a') := by
                rw [← hm1b_acc, ← hm1b_bal]
                exact hm1b_bal_le_maxBal
              have hmaxBal_gt_c : TotalOrderWithZeroAndNone.le c (st.maxBal a') ∧ ¬st.maxBal a' = c := by
                constructor
                · exact TotalOrderWithZeroAndNone.le_trans _ _ _ hle_c_b hmaxBal_ge_b
                · intro heq
                  rw [heq] at hmaxBal_ge_b
                  have hc_eq_b := TotalOrderWithZeroAndNone.le_antisymm _ _ hle_c_b hmaxBal_ge_b
                  exact hne_c_b hc_eq_b
              have hm1b_maxVBal_le : TotalOrderWithZeroAndNone.le m1b.maxVBal maxMsg.maxVBal := hmaxMsg_bound m1b hm1b_in_S
              -- Sub-case: c > maxMsg.maxVBal or c = maxMsg.maxVBal
              by_cases hc_eq_maxMsg : c = maxMsg.maxVBal
              · -- c = maxMsg.maxVBal
                subst hc_eq_maxMsg
                by_cases hm1b_eq : m1b.maxVBal = maxMsg.maxVBal
                · -- m1b voted at same ballot as maxMsg
                  have hm1b_maxVBal_ne_none : m1b.maxVBal ≠ TotalOrderWithZeroAndNone.none := by
                    rw [hm1b_eq]; exact hmaxMsg_maxVBal_ne_none
                  rcases hm1b_voted_or_none with ⟨_, hVotedForIn_m1b⟩ | hm1b_none
                  · left
                    obtain ⟨m2b_m1b, hm2b_m1b_contains, hm2b_m1b_type, hm2b_m1b_val, hm2b_m1b_bal, hm2b_m1b_acc⟩ := hVotedForIn_m1b
                    have hsame_bal : m2b_m1b.bal = m2b_maxMsg.bal := by rw [hm2b_m1b_bal, hm2b_maxMsg_bal, hm1b_eq]
                    have hval_eq : m2b_m1b.val = m2b_maxMsg.val := hVotedOnce m2b_m1b m2b_maxMsg m2b_m1b.acc m2b_maxMsg.acc m2b_m1b.bal m2b_m1b.val m2b_maxMsg.val
                      hm2b_m1b_contains hm2b_m1b_type rfl rfl rfl
                      hm2b_maxMsg_contains hm2b_maxMsg_type rfl hsame_bal.symm rfl
                    have hm1b_val_eq_v : m1b.val = v := by
                      rw [← hmaxMsg_val, ← hm2b_maxMsg_val, ← hval_eq, hm2b_m1b_val]
                    have hm2b_m1b_ne : m2b_m1b ≠ newMsg := by
                      intro heq'; rw [heq'] at hm2b_m1b_type; simp at hm2b_m1b_type
                    refine ⟨m2b_m1b, ?_, hm2b_m1b_type, ?_, ?_, ?_⟩
                    · rw [TSet.contains_insert_other _ _ _ hm2b_m1b_ne]; exact hm2b_m1b_contains
                    · rw [hm2b_m1b_val, hm1b_val_eq_v]
                    · rw [hm2b_m1b_bal, hm1b_eq]
                    · rw [hm2b_m1b_acc, hm1b_acc]
                  · exact absurd hm1b_none hm1b_maxVBal_ne_none
                · -- m1b.maxVBal < maxMsg.maxVBal: WontVoteIn via interval
                  right
                  have hc_in_interval : TotalOrderWithZeroAndNone.le m1b.maxVBal maxMsg.maxVBal ∧ ¬m1b.maxVBal = maxMsg.maxVBal ∧
                                       TotalOrderWithZeroAndNone.le maxMsg.maxVBal m1b.bal ∧ ¬maxMsg.maxVBal = m1b.bal := by
                    refine ⟨hm1b_maxVBal_le, hm1b_eq, ?_, ?_⟩
                    · rw [hm1b_bal]; exact hmaxMsg_le_b
                    · rw [hm1b_bal]; exact hmaxMsg_ne_b
                  refine ⟨?_, hmaxBal_gt_c.1, hmaxBal_gt_c.2⟩
                  intro x hxcontains hxtype hxbal
                  have hxne : x ≠ newMsg := by
                    intro heq'; rw [heq'] at hxtype; simp at hxtype
                  rw [TSet.contains_insert_other _ _ _ hxne] at hxcontains
                  rw [← hm1b_acc]
                  exact hm1b_no_vote_interval x maxMsg.maxVBal hc_in_interval.1 hc_in_interval.2.1 hc_in_interval.2.2.1 hc_in_interval.2.2.2 hxcontains hxtype hxbal
              · -- c > maxMsg.maxVBal: WontVoteIn via interval (c in (m1b.maxVBal, b))
                right
                have hc_in_interval : TotalOrderWithZeroAndNone.le m1b.maxVBal c ∧ ¬m1b.maxVBal = c ∧
                                     TotalOrderWithZeroAndNone.le c m1b.bal ∧ ¬c = m1b.bal := by
                  refine ⟨TotalOrderWithZeroAndNone.le_trans _ _ _ hm1b_maxVBal_le hle_maxMsg_c, ?_, ?_, ?_⟩
                  · intro heq
                    rw [heq] at hm1b_maxVBal_le
                    have heq' := TotalOrderWithZeroAndNone.le_antisymm _ _ hm1b_maxVBal_le hle_maxMsg_c
                    exact hc_eq_maxMsg heq'
                  · rw [hm1b_bal]; exact hle_c_b
                  · rw [hm1b_bal]; exact hne_c_b
                refine ⟨?_, hmaxBal_gt_c.1, hmaxBal_gt_c.2⟩
                intro x hxcontains hxtype hxbal
                have hxne : x ≠ newMsg := by
                  intro heq'; rw [heq'] at hxtype; simp at hxtype
                rw [TSet.contains_insert_other _ _ _ hxne] at hxcontains
                rw [← hm1b_acc]
                exact hm1b_no_vote_interval x c hc_in_interval.1 hc_in_interval.2.1 hc_in_interval.2.2.1 hc_in_interval.2.2.2 hxcontains hxtype hxbal
          · -- c < maxMsg.maxVBal: use Q' from SafeAt(v, maxMsg.maxVBal)
            have hle_c_maxVBal : TotalOrderWithZeroAndNone.le c maxMsg.maxVBal := by
              rcases TotalOrderWithZeroAndNone.le_total c maxMsg.maxVBal with h | h
              · exact h
              · exact absurd h hle_maxMsg_c
            have hne_c_maxVBal : c ≠ maxMsg.maxVBal := fun heq => hle_maxMsg_c (by rw [← heq]; exact TotalOrderWithZeroAndNone.le_refl _)
            obtain ⟨Q', hQ'⟩ := hSafeAt_v_maxVBal c hle_c_maxVBal hne_c_maxVBal hne_c_none
            refine ⟨Q', ?_⟩
            intro a'' ha''
            rcases hQ' a'' ha'' with ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩ | ⟨hnoVote, hmaxBal1', hmaxBal2'⟩
            · left
              have hm'ne : m' ≠ newMsg := by
                intro heq'; rw [heq'] at hm'type; simp at hm'type
              refine ⟨m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
              rw [TSet.contains_insert_other _ _ _ hm'ne]
              exact hm'contains
            · right
              refine ⟨?_, hmaxBal1', hmaxBal2'⟩
              intro x hxcontains hxtype hxbal
              have hxne : x ≠ newMsg := by
                intro heq'; rw [heq'] at hxtype; simp at hxtype
              rw [TSet.contains_insert_other _ _ _ hxne] at hxcontains
              exact hnoVote x hxcontains hxtype hxbal
        · -- maxMsg.maxVBal = none, contradicts hmaxMsg_maxVBal_ne_none
          exact absurd hmaxMsg_none hmaxMsg_maxVBal_ne_none
    case unique_new =>
      intro ma hmacontains hmatype hmabal
      by_cases hmaeq : ma = newMsg
      · exact hmaeq
      · rw [TSet.contains_insert_other _ _ _ hmaeq] at hmacontains
        have hma_2a := hMsgInv2a ma hmacontains hmatype
        have hcount_zero := hno_existing_2a
        have hma_in_filter : TSet.contains ma (TSet.filter st.msgs (fun m => decide (m.msgType = MsgType.Phase2a) && decide (m.bal = b))) = true := by
          apply TSet.contains_filter_of
          exact hmacontains
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hmatype, hmabal⟩
        have := TSet.count_zero_not_contains ma _ hcount_zero
        rw [this] at hma_in_filter
        exact absurd hma_in_filter (by simp)
  · rw [TSet.contains_insert_other _ _ _ hmeq] at hcontains
    obtain ⟨hSafeAt, hUnique⟩ := hMsgInv2a m hcontains hmsgtype
    refine ⟨?safeAt_old, ?unique_old⟩
    case safeAt_old =>
      intro c hlt hne' hne_none
      obtain ⟨Q', hQ⟩ := hSafeAt c hlt hne' hne_none
      refine ⟨Q', ?_⟩
      intro a' ha'
      rcases hQ a' ha' with ⟨m', hm'contains, hm'type, hm'val, hm'bal, hm'acc⟩ | ⟨hnoVote, hmaxBal1, hmaxBal2⟩
      · left
        have hm'ne : m' ≠ newMsg := by
          intro heq'
          rw [heq'] at hm'type
          simp at hm'type
        refine ⟨m', ?_, hm'type, hm'val, hm'bal, hm'acc⟩
        rw [TSet.contains_insert_other _ _ _ hm'ne]
        exact hm'contains
      · right
        refine ⟨?_, hmaxBal1, hmaxBal2⟩
        intro x hxcontains hxtype hxbal
        have hxne : x ≠ newMsg := by
          intro heq'
          rw [heq'] at hxtype
          simp at hxtype
        rw [TSet.contains_insert_other _ _ _ hxne] at hxcontains
        exact hnoVote x hxcontains hxtype hxbal
    case unique_old =>
      intro ma hmacontains hmatype hmabal
      have hmane : ma ≠ newMsg := by
        intro heq'
        subst heq'
        simp only [newMsg] at hmabal
        have hm_in_filter : TSet.contains m (TSet.filter st.msgs (fun m => decide (m.msgType = MsgType.Phase2a) && decide (m.bal = b))) = true := by
          apply TSet.contains_filter_of
          exact hcontains
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hmsgtype, hmabal.symm⟩
        have := TSet.count_zero_not_contains m _ hno_existing_2a
        rw [this] at hm_in_filter
        exact absurd hm_in_filter (by simp)
      rw [TSet.contains_insert_other _ _ _ hmane] at hmacontains
      exact hUnique ma hmacontains hmatype hmabal
