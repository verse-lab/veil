import Veil.Core.Tools.ModelChecker.ConcreteNew.Core
import Veil.Core.Tools.ModelChecker.ConcreteNew.Progress
import Veil.Core.Tools.ModelChecker.ConcreteNew.SequentialLemmas

namespace Veil.ModelChecker.Concrete
open Std
open Veil fQueue


/-- Process a single neighbor node during BFS traversal.
If the neighbor has been seen, return the current context unchanged.
Otherwise, add it to seen set and log, then enqueue it. -/
-- @[inline, specialize]
def SequentialSearchContext.tryExploreNeighbor {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (curr : σ)          -- current state being processed
  (fpSt : σₕ)         -- fingerprint of state we're coming from (pre-state), for logging
  (depth : Nat)       -- depth of the current state (neighbor will be at depth + 1)
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (neighbor : κ × σ)  -- Only successful transitions are passed here
  (h_neighbor : sys.reachable neighbor.2)
  (h_not_finished : !ctx.hasFinished)
  (h_deque_head : ∃tl, ctx.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tl))
  : {ctx' : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params //
      ctx'.finished = ctx.finished ∧
      ctx'.seen.contains (fp.view neighbor.2) ∧
      ∃tail', ctx'.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail') ∧
      ∀fp, ctx.seen.contains fp → ctx'.seen.contains fp } :=
  let ⟨label, succ⟩ := neighbor
  let fingerprint := fp.view succ
  have h_succ_reachable : sys.reachable succ := h_neighbor
  if h_has_seen : ctx.seen.contains fingerprint then
    ⟨ctx, by constructor <;> grind⟩
  else
    have h_not_in_seen : !ctx.seen.contains fingerprint := by simp [h_has_seen]
    let newActionStatsMap := match ctx.actionStatsMap[label]? with
      | some stat => ctx.actionStatsMap.insert label { stat with distinctStates := stat.distinctStates + 1 }
      | none => ctx.actionStatsMap.insert label { statesGenerated := 0, distinctStates := 1 }  -- shouldn't happen if processState ran first
    ⟨{ ctx with
        seen := ctx.seen.insert fingerprint,
        sq   := ctx.sq.enqueue ⟨fingerprint, succ, depth + 1⟩,
        log  := ctx.log.insert fingerprint (fpSt, label),
        invs := insert_and_enqueue_preserves_invs sys params ctx fingerprint succ depth h_neighbor rfl
        actionStatsMap := newActionStatsMap,
        stable_closed  := insert_and_enqueue_preserves_stable_closed sys params ctx fingerprint succ depth h_succ_reachable rfl
        terminate_empty_queue := by intro h_finished; unfold BaseSearchContext.hasFinished at h_not_finished; grind
    }, (by constructor <;> grind)⟩


-- @[inline, specialize]
def SequentialSearchContext.processSuccessors {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (curr : σ)      -- current state being processed
  (fpSt : σₕ)     -- fingerprint of curr
  (depth : Nat)   -- depth of curr
  (h_curr : sys.reachable curr)
  (successors : List (κ × σ))
  (h_succ_eq : successors = extractSuccessfulTransitions (sys.tr th curr))
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (h_deque_head : ∃tl, ctx.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tl))
  (h_not_finished : !ctx.hasFinished)
  : {ctx' : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params //
      ctx'.finished = ctx.finished ∧
      ∃tail', ctx'.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail') } :=
  let result := successors.attach.foldl
    (init := (⟨ctx, by constructor; rfl; exact h_deque_head⟩ :
      { p' : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params //
        p'.finished = ctx.finished ∧
        ∃tail', p'.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail') }))
    (fun current_ctx ⟨⟨tr, postState⟩, h_neighbor_in_successors⟩ =>
      have h_current_not_finished : !current_ctx.val.hasFinished := by unfold BaseSearchContext.hasFinished at h_not_finished ⊢; rw [current_ctx.property.1, ← h_not_finished]
      have h_in_sys_tr : (tr, ExecutionOutcome.success postState) ∈ sys.tr th curr := by
        have h_in_extracted : (tr, postState) ∈ extractSuccessfulTransitions (sys.tr th curr) := by rw [← h_succ_eq]; exact h_neighbor_in_successors
        unfold extractSuccessfulTransitions at h_in_extracted
        rw [List.mem_filterMap] at h_in_extracted
        obtain ⟨⟨label, outcome⟩, h_mem, h_eq⟩ := h_in_extracted
        cases outcome with
        | success st => simp at h_eq; grind
        | assertionFailure _ _ => simp at h_eq
        | divergence => simp at h_eq
      have h_next : sys.next curr postState := ⟨tr, h_in_sys_tr⟩
      let h_neighbor_reachable : sys.reachable postState := EnumerableTransitionSystem.reachable.step curr postState h_curr h_next
      have h_dequeue_head_curr : ∃tail, current_ctx.val.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail) := current_ctx.property.2
      let neighbor_result := SequentialSearchContext.tryExploreNeighbor sys curr fpSt depth current_ctx.val ⟨tr, postState⟩ h_neighbor_reachable h_current_not_finished h_dequeue_head_curr
      (⟨neighbor_result.val, by constructor <;> grind⟩))
  ⟨result.val, result.property⟩



/- Theorem: processSuccessors adds all successors to the seen set.
    This is a key property for proving completeness: after processing a state's successors,
    all of them will be marked as seen. -/
theorem SequentialSearchContext.processSuccessors_adds_all_to_seen {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (curr : σ)
  (fpSt : σₕ)
  (depth : Nat)
  (h_curr : sys.reachable curr)
  (successors : List (κ × σ))
  (h_succ_eq : successors = extractSuccessfulTransitions (sys.tr th curr))
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (h_deque_head : ∃tl, ctx.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tl))
  (h_not_finished : !ctx.hasFinished) :
  ∀ (l : κ) (v : σ), (l, v) ∈ successors →
    (processSuccessors sys curr fpSt depth h_curr successors h_succ_eq ctx h_deque_head h_not_finished).val.seen.contains (fp.view v) := by
  intro l v h_in_successors
  unfold processSuccessors
  simp only
  have h_in_attach : ⟨(l, v), h_in_successors⟩ ∈ successors.attach := List.mem_attach _ _
  let foldStep :
    { p' : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params //
      p'.finished = ctx.finished ∧
      ∃tail', p'.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail') } →
    { x // x ∈ successors } →
    { p' : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params //
      p'.finished = ctx.finished ∧
      ∃tail', p'.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail') } :=
    fun current_ctx neighbor =>
      match neighbor with
      | ⟨⟨tr, postState⟩, h_neighbor_in_successors⟩ =>
        have h_current_not_finished : !current_ctx.val.hasFinished := by
          unfold BaseSearchContext.hasFinished at h_not_finished ⊢
          rw [current_ctx.property.1, ← h_not_finished]
        have h_in_sys_tr : (tr, ExecutionOutcome.success postState) ∈ sys.tr th curr := by
          have h_in_extracted : (tr, postState) ∈ extractSuccessfulTransitions (sys.tr th curr) := by rw [← h_succ_eq]; exact h_neighbor_in_successors
          unfold extractSuccessfulTransitions at h_in_extracted
          rw [List.mem_filterMap] at h_in_extracted
          obtain ⟨⟨label, outcome⟩, h_mem, h_eq⟩ := h_in_extracted
          cases outcome with
          | success st =>
            simp at h_eq
            obtain ⟨h_label_eq, h_st_eq⟩ := h_eq
            rw [← h_label_eq, ← h_st_eq]
            exact h_mem
          | assertionFailure _ _ => simp at h_eq
          | divergence => simp at h_eq
        have h_next : sys.next curr postState := ⟨tr, h_in_sys_tr⟩
        let h_neighbor_reachable : sys.reachable postState :=
          EnumerableTransitionSystem.reachable.step curr postState h_curr h_next
        have h_dequeue_head_curr : ∃tail, current_ctx.val.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail) :=
          current_ctx.property.2
        let neighbor_result := SequentialSearchContext.tryExploreNeighbor sys curr fpSt depth current_ctx.val ⟨tr, postState⟩ h_neighbor_reachable h_current_not_finished h_dequeue_head_curr
        ⟨neighbor_result.val, by
          constructor
          · have h_finished_preserved := neighbor_result.property.1
            have h_ctx_finished := current_ctx.property.1
            simp [h_finished_preserved, h_ctx_finished]
          · grind
        ⟩
  have h_foldl_property : ∀
    (xs : List { x // x ∈ successors })
    (init_ctx : { p' : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params // p'.finished = ctx.finished ∧ ∃tail', p'.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail') }),
    ⟨(l, v), h_in_successors⟩ ∈ xs →
    (xs.foldl foldStep init_ctx).val.seen.contains (fp.view v) := by
    intro xs init_ctx h_mem
    induction xs generalizing init_ctx with
    | nil => contradiction
    | cons hd tl ih =>
      simp only [List.foldl]
      simp only [List.mem_cons] at h_mem
      cases h_mem with
      | inl h_eq =>
        -- The element we're looking for is the head
        have h_eq_subtype : hd = ⟨(l, v), h_in_successors⟩ := h_eq.symm
        -- After processing hd, fp.view v is in seen
        obtain ⟨⟨tr_hd, postState_hd⟩, h_hd_mem⟩ := hd
        have h_postState_eq : postState_hd = v := by
          have h_val_eq := congrArg Subtype.val h_eq_subtype
          simp at h_val_eq
          exact h_val_eq.2
        -- After processing hd with tryExploreNeighbor, fp.view postState_hd is in the result's seen
        let h_current_not_finished : !init_ctx.val.hasFinished := by
          unfold BaseSearchContext.hasFinished at h_not_finished ⊢
          rw [init_ctx.property.1, ← h_not_finished]
        let h_in_sys_tr : (tr_hd, ExecutionOutcome.success postState_hd) ∈ sys.tr th curr := by
          have h_in_extracted : (tr_hd, postState_hd) ∈ extractSuccessfulTransitions (sys.tr th curr) := by rw [← h_succ_eq]; exact h_hd_mem
          unfold extractSuccessfulTransitions at h_in_extracted
          rw [List.mem_filterMap] at h_in_extracted
          obtain ⟨⟨label, outcome⟩, h_mem, h_eq⟩ := h_in_extracted
          cases outcome with
          | success st => simp at h_eq; grind
          | assertionFailure _ _ => simp at h_eq
          | divergence => simp at h_eq
        let h_next : sys.next curr postState_hd := ⟨tr_hd, h_in_sys_tr⟩
        let h_neighbor_reachable : sys.reachable postState_hd :=
          EnumerableTransitionSystem.reachable.step curr postState_hd h_curr h_next
        let h_dequeue_head_curr : ∃tail, init_ctx.val.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail) :=
          init_ctx.property.2
        let neighbor_result := tryExploreNeighbor sys curr fpSt depth
          init_ctx.val ⟨tr_hd, postState_hd⟩ h_neighbor_reachable h_current_not_finished h_dequeue_head_curr
        -- tryExploreNeighbor ensures the neighbor is added to seen
        have h_in_result_seen : neighbor_result.val.seen.contains (fp.view postState_hd) :=
          neighbor_result.property.2.1
        -- The rest of the fold preserves this property (seen is monotonic)
        let next_ctx : { p' : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params //
          p'.finished = ctx.finished ∧
          ∃tail', p'.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail') } :=
          ⟨neighbor_result.val, by
            constructor
            · have h_finished_preserved := neighbor_result.property.1
              have h_ctx_finished := init_ctx.property.1

              simp [h_finished_preserved, h_ctx_finished]
            · obtain ⟨tail', h_deq, _⟩ := neighbor_result.property.2.2
              exact ⟨tail', h_deq⟩
          ⟩
        have h_seen_monotonic : ∀ fp_elem, init_ctx.val.seen.contains fp_elem →
          next_ctx.val.seen.contains fp_elem := by
          intro fp_elem h_contains
          -- The property is: ∃ tail', ctx'.sq.dequeue? = some (..., tail') ∧ ∀ fp, ...
          obtain ⟨_, _, h_mono⟩ := neighbor_result.property.2.2
          exact h_mono fp_elem h_contains
        -- Now we need to show that the final result of folding tl preserves fp.view v in seen
        have h_v_in_next : next_ctx.val.seen.contains (fp.view v) := by
          rw [← h_postState_eq]
          exact h_in_result_seen
        -- Apply monotonicity through the rest of the fold
        have h_mono : ∀
          (ctx1 : { p' : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params // p'.finished = ctx.finished ∧ ∃tail', p'.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail') })
          (xs : List { x // x ∈ successors })
          (fp_elem : σₕ),
          (ctx1.val.seen.contains fp_elem) →
          (xs.foldl foldStep ctx1).val.seen.contains fp_elem := by
          intro ctx1 xs fp_elem h_contains
          induction xs generalizing ctx1 with
          | nil => simp; exact h_contains
          | cons hd' tl' ih' =>
            simp only [List.foldl]
            apply ih'
            obtain ⟨⟨tr', post'⟩, h_mem'⟩ := hd'
            let h_not_fin' : !ctx1.val.hasFinished := by
              unfold BaseSearchContext.hasFinished at h_not_finished ⊢
              rw [ctx1.property.1, ← h_not_finished]
            let h_in_tr' : (tr', ExecutionOutcome.success post') ∈ sys.tr th curr := by
              have h_in_extracted : (tr', post') ∈ extractSuccessfulTransitions (sys.tr th curr) := by rw [← h_succ_eq]; exact h_mem'
              unfold extractSuccessfulTransitions at h_in_extracted
              rw [List.mem_filterMap] at h_in_extracted
              obtain ⟨⟨label, outcome⟩, h_mem, h_eq⟩ := h_in_extracted
              cases outcome with
              | success st =>
                simp at h_eq;
                obtain ⟨h_label_eq, h_st_eq⟩ := h_eq
                rw [← h_label_eq, ← h_st_eq]
                exact h_mem
              | assertionFailure _ _ => simp at h_eq
              | divergence => simp at h_eq
            let h_next' : sys.next curr post' := ⟨tr', h_in_tr'⟩
            let h_reach' : sys.reachable post' :=
              EnumerableTransitionSystem.reachable.step curr post' h_curr h_next'
            let h_deq' : ∃tail, ctx1.val.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail) := ctx1.property.2
            let result' := tryExploreNeighbor sys curr fpSt depth
              ctx1.val ⟨tr', post'⟩ h_reach' h_not_fin' h_deq'
            obtain ⟨_, _, h_mono'⟩ := result'.property.2.2
            exact h_mono' fp_elem h_contains
        exact h_mono next_ctx tl (fp.view v) h_v_in_next
      | inr h_in_tl =>
        -- The element is in the tail, so use the induction hypothesis
        -- First, process the head to get the next context
        obtain ⟨⟨tr_hd, postState_hd⟩, h_hd_mem⟩ := hd
        let h_current_not_finished : !init_ctx.val.hasFinished := by
          unfold BaseSearchContext.hasFinished at h_not_finished ⊢
          rw [init_ctx.property.1, ← h_not_finished]
        let h_in_sys_tr : (tr_hd, ExecutionOutcome.success postState_hd) ∈ sys.tr th curr := by
          have h_in_extracted : (tr_hd, postState_hd) ∈ extractSuccessfulTransitions (sys.tr th curr) := by rw [← h_succ_eq]; exact h_hd_mem
          unfold extractSuccessfulTransitions at h_in_extracted
          rw [List.mem_filterMap] at h_in_extracted
          obtain ⟨⟨label, outcome⟩, h_mem, h_eq⟩ := h_in_extracted
          cases outcome with
          | success st => simp at h_eq; grind
          | assertionFailure _ _ => simp at h_eq
          | divergence => simp at h_eq
        let h_next : sys.next curr postState_hd := ⟨tr_hd, h_in_sys_tr⟩
        let h_neighbor_reachable : sys.reachable postState_hd :=
          EnumerableTransitionSystem.reachable.step curr postState_hd h_curr h_next
        let h_dequeue_head_curr : ∃tail, init_ctx.val.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail) :=
          init_ctx.property.2
        let neighbor_result := SequentialSearchContext.tryExploreNeighbor sys curr fpSt depth
          init_ctx.val ⟨tr_hd, postState_hd⟩ h_neighbor_reachable h_current_not_finished h_dequeue_head_curr
        let next_ctx : { p' : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params //
          p'.finished = ctx.finished ∧
          ∃tail', p'.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail') } :=
          ⟨neighbor_result.val, by
            constructor
            · have h_finished_preserved := neighbor_result.property.1
              have h_ctx_finished := init_ctx.property.1
              simp [h_finished_preserved, h_ctx_finished]
            · have := (neighbor_result.property.2.2)
              rcases this with ⟨tail', hdeq, hseen⟩
              exact ⟨tail', hdeq⟩
          ⟩
        exact ih next_ctx h_in_tl
  let init := (⟨ctx, by constructor; rfl; exact h_deque_head⟩ :
    { p' : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params //
      p'.finished = ctx.finished ∧
      ∃tail', p'.sq.dequeue? = some (⟨fpSt, curr, depth⟩, tail') })
  exact h_foldl_property successors.attach init h_in_attach


-- @[inline, specialize]
def SequentialSearchContext.processState {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)
  (depth : Nat)  -- depth of the current state
  (curr : σ)
  (h_curr : sys.reachable curr)
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params)
  -- Dequeue information: the queue tail after removing curr
  (q_tail : fQueue (QueueItem σₕ σ))
  (h_dequeue : ctx.sq.dequeue? = some (⟨fpSt, curr, depth⟩, q_tail))
  -- Depth tracking information computed by caller
  (newCompletedDepth : Nat)
  (newFrontierDepth : Nat)
  (h_non_finished : !ctx.hasFinished) :
  m (@SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params) := do
  match h_process : ctx.toBaseSearchContext.processState sys fpSt curr with
  | (baseCtx', outcomesOpt) =>
    have h_seen_unchanged : baseCtx'.seen = ctx.seen := by
      have h_preserves := BaseSearchContext.processState_preserves_seen sys params fpSt curr ctx.toBaseSearchContext
      rw [h_process] at h_preserves
      exact h_preserves
    match outcomesOpt with
    | none =>
      -- Early termination case: processState returned none, meaning we're terminating early
      have h_invs_after_process : SearchContextInvariants sys params (· ∈ ctx.sq) (· ∈ baseCtx'.seen) := update_base_after_processState_preserves_invs sys ctx fpSt curr baseCtx' (by rw [h_process])
      have h_invs_after_dequeue' := dequeue_preserves_invs sys params ctx ⟨fpSt, curr, depth⟩ q_tail h_dequeue
      have h_invs_after_dequeue : SearchContextInvariants sys params (· ∈ q_tail) (· ∈ baseCtx'.seen) := by simp [h_seen_unchanged, h_invs_after_dequeue']
      pure { ctx with
        toBaseSearchContext := { baseCtx' with
          completedDepth := newCompletedDepth,
          currentFrontierDepth := newFrontierDepth },
        sq := q_tail,
        invs := h_invs_after_dequeue
        terminate_empty_queue := by
          intro h_finished'
          unfold BaseSearchContext.processState at h_process
          simp only at h_process
          split at h_process
          <;> (simp at h_process; try rw [← h_process] at h_finished'; simp at h_finished')
        stable_closed := by
          intro h_view_inj h_finished u h_in_seen h_not_in_new_queue l v h_tr
          cases h_finished with
          | inl h_exploredAll => unfold BaseSearchContext.processState at h_process; simp only at h_process; grind
          | inr h_none => unfold BaseSearchContext.processState at h_process; simp only at h_process; grind
      }
    | some ⟨outcomes, heq⟩ =>
      -- Extract only successful transitions for queueing
      let successfulTransitions := extractSuccessfulTransitions outcomes
      -- Update statesFound: count ALL successful transitions (before dedup)
      let newStatesFound := ctx.statesFound + successfulTransitions.length
      -- Update per-action statesGenerated counts
      let newActionStatsMap := successfulTransitions.foldl (init := ctx.actionStatsMap) fun acc (label, _) =>
        match acc[label]? with
        | some stat => acc.insert label { stat with statesGenerated := stat.statesGenerated + 1 }
        | none => acc.insert label { statesGenerated := 1, distinctStates := 0 }
      have h_finished_unchanged : baseCtx'.finished = ctx.finished := by
        unfold BaseSearchContext.processState at h_process
        simp at h_process
        have h_check := BaseSearchContext.checkViolationsAndMaybeTerminate_preserves_fields sys params ctx.toBaseSearchContext fpSt curr outcomes
        grind
      -- let baseCtx'' := { baseCtx' with statesFound := newStatesFound, actionStatsMap := newActionStatsMap }
      let ctx_updated : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params := { ctx with
        toBaseSearchContext := { baseCtx' with
          statesFound := newStatesFound,
          actionStatsMap := newActionStatsMap },
        invs := by grind [update_base_after_processState_preserves_invs]
        terminate_empty_queue := by
          intro h_finished';
          have h_non_finished : ctx.finished = none := by unfold BaseSearchContext.hasFinished at h_non_finished; simp at h_non_finished; exact h_non_finished
          grind
        stable_closed := by
          have h_seen_eq : baseCtx'.seen = ctx.seen := by grind
          intro h_view_inj h_finished' u h_in_seen h_not_in_new_queue l v h_tr
          have h_non_finished : ctx.finished = none := by
            unfold BaseSearchContext.hasFinished at h_non_finished
            simp at h_non_finished
            exact h_non_finished
          rw [h_finished_unchanged] at h_finished'
          rw [h_seen_eq] at h_in_seen
          have := ctx.stable_closed h_view_inj (Or.inr h_non_finished) u h_in_seen h_not_in_new_queue l v h_tr
          grind
      }
      have h_ctx_updated_not_finished : !ctx_updated.hasFinished := by
        rw [BaseSearchContext.hasFinished, h_finished_unchanged]
        exact h_non_finished
      have h_ctx_head : ctx_updated.sq.dequeue? = some (⟨fpSt, curr, depth⟩, q_tail) := by
        rw [← h_dequeue]
      -- Process all successors
      let result_with_proof := SequentialSearchContext.processSuccessors sys curr fpSt depth h_curr successfulTransitions (by grind) ctx_updated (by grind) h_ctx_updated_not_finished

      let ctx_after_add := result_with_proof.val
      have h_post := result_with_proof.property
      have h_finished_after_enqueue : ctx_after_add.finished = ctx.finished := by
        have h1 := h_post.1
        rw [h1, h_finished_unchanged]
      have h_all_successors_in_final_seen : ∀l v, (l, ExecutionOutcome.success v) ∈ sys.tr th curr → (fp.view v) ∈ ctx_after_add.seen := by
        intro l v h_tr
        have h_in_successors : (l, v) ∈ successfulTransitions := by
          show (l, v) ∈ extractSuccessfulTransitions outcomes
          rw [extractSuccessfulTransitions, List.mem_filterMap]
          exists (l, ExecutionOutcome.success v)
          constructor <;> grind
        grind [processSuccessors_adds_all_to_seen]
      -- Dequeue the head element (curr) and construct the final SequentialSearchContext
      match h_dequeue_after : ctx_after_add.sq.dequeue? with
      | none => pure ctx
      | some (item, new_tail) =>
        have h_item_is_curr : item = ⟨fpSt, curr, depth⟩ := by grind
        have h_dequeue_correct : ctx_after_add.sq.dequeue? = some (⟨fpSt, curr, depth⟩, new_tail) := by rw [← h_item_is_curr]; exact h_dequeue_after
        pure { ctx_after_add with
          completedDepth := newCompletedDepth,
          currentFrontierDepth := newFrontierDepth,
          sq := new_tail
          invs := dequeue_preserves_invs sys params ctx_after_add ⟨fpSt, curr, depth⟩ new_tail (by grind)
          terminate_empty_queue := dequeue_preserves_terminate_empty_queue sys ctx new_tail h_non_finished ctx_after_add.finished h_finished_after_enqueue
          stable_closed := dequeue_with_successors_in_seen_preserves_stable_closed sys ctx_after_add curr fpSt depth new_tail h_dequeue_correct h_all_successors_in_final_seen
        }



/-- Perform one step of BFS. -/
-- @[inline, specialize]
def SequentialSearchContext.bfsStep {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (h_finished : !ctx.hasFinished)
  :
  m (@SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params) :=
  match h : ctx.sq.dequeue? with
  | none => pure { ctx with
      finished := some (.exploredAllReachableStates)
      invs := ctx.invs
      terminate_empty_queue := by intro h_finished; grind
      stable_closed := by
        intro h_view_inj h_finished' h_pc_none h_pc_outside u h_in_seen h_not_in_queue l
        have h_pre_no_terminate : ctx.finished = none := by
          unfold BaseSearchContext.hasFinished at h_finished
          simp at h_finished; exact h_finished
        exact ctx.stable_closed h_view_inj ((Or.inr h_pre_no_terminate)) h_pc_none h_pc_outside u h_in_seen h_not_in_queue l
  }
  | some (⟨fpSt, curr, depth⟩, q_tail) => do
    have h_curr : sys.reachable curr := by
      have h_in_queue : ⟨fpSt, curr, depth⟩ ∈ ctx.sq := by grind
      have h_wellformed : fpSt = fp.view curr :=  ctx.invs.queue_wellformed fpSt curr depth h_in_queue
      have h_in_queue' : ⟨fp.view curr, curr, depth⟩ ∈ ctx.sq := by grind
      exact ctx.invs.queue_sound curr depth h_in_queue'

    -- Update completed depth when we move to a new frontier level
    let (newCompletedDepth, newFrontierDepth) :=
      if depth > ctx.currentFrontierDepth then
        (depth - 1, depth)  -- All states at previous depth are now fully explored
      else
        (ctx.completedDepth, ctx.currentFrontierDepth)
    -- Process curr: add successors to seen, enqueue them, and dequeue curr
    -- processState handles the complete lifecycle of processing a state
    SequentialSearchContext.processState sys fpSt depth curr h_curr ctx q_tail h newCompletedDepth newFrontierDepth h_finished


-- @[specialize]
def breadthFirstSearchSequential {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ] [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken) :
  m (@SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params) := do
  let mut ctx : @SequentialSearchContext ρ σ κ σₕ fp _ _ th sys params := SequentialSearchContext.initial sys params
  let mut lastUpdateTime : Nat := 0
  while h_not_finished : !ctx.hasFinished do
    let currentCtx := ctx
    ctx := ← SequentialSearchContext.bfsStep sys currentCtx h_not_finished
    -- If we found a violation, mark it so handoff is prevented
    if let some (.earlyTermination cond) := ctx.finished then
      if EarlyTerminationReason.isViolation cond then setViolationFound progressInstanceId
    -- Update progress on every diameter change (ensures all levels appear in history)
    if ctx.currentFrontierDepth > currentCtx.currentFrontierDepth then
      updateProgress progressInstanceId
        ctx.currentFrontierDepth ctx.statesFound ctx.seen.size ctx.sq.size
        (toActionStatsList ctx.actionStatsMap)
    -- Check for cancellation/handoff at most once per second
    let now ← IO.monoMsNow
    if now - lastUpdateTime >= 1000 then
      lastUpdateTime := now
      if ← shouldStop cancelToken progressInstanceId then
        ctx := { ctx with
          finished := some (.earlyTermination .cancelled),
          terminate_empty_queue := by
            intro h_finished
            simp at h_finished
          stable_closed := by
            intro h_view_inj h_finished u h_in_seen h_not_in_queue l v h_tr
            cases h_finished with
            | inl h_explored => simp at h_explored
            | inr h_none => simp at h_none
        }
        break
  -- Final update to ensure stats reflect finished state
  updateProgress progressInstanceId
    ctx.currentFrontierDepth
    ctx.statesFound
    ctx.seen.size
    ctx.sq.size
    (toActionStatsList ctx.actionStatsMap)
  return ctx

end Veil.ModelChecker.Concrete
