import Veil.Core.Tools.ModelChecker.Concrete.Core
import Veil.Core.Tools.ModelChecker.Concrete.Progress

namespace Veil.ModelChecker.Concrete
open Std

structure SequentialSearchContext {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
extends @BaseSearchContext ρ σ κ σₕ fp th sys params
where
  /-- Queue storing (fingerprint, state, depth) tuples for BFS traversal -/
  sq    : fQueue (QueueItem σₕ σ)
  invs  : @SearchContextInvariants ρ σ κ σₕ fp th sys params (Membership.mem sq) (Membership.mem seen)

def SequentialSearchContext.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ) :
  @SequentialSearchContext ρ σ κ σₕ fp th sys params := {
    BaseSearchContext.initial sys params with
    sq := fQueue.ofList (sys.initStates |> Functor.map (fun s => ⟨fp.view s, s, 0⟩)),
    invs := sorry
  }

/-- Process a single neighbor node during BFS traversal.
If the neighbor has been seen, return the current context unchanged.
Otherwise, add it to seen set and log, then enqueue it. -/
@[inline, specialize]
def SequentialSearchContext.tryExploreNeighbor {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)  -- fingerprint of state we're coming from (pre-state), for logging
  (depth : Nat)  -- depth of the current state (neighbor will be at depth + 1)
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp th sys params)
  (neighbor : κ × σ)  -- Only successful transitions are passed here
  (h_neighbor : sys.reachable neighbor.2) :
  m (@SequentialSearchContext ρ σ κ σₕ fp th sys params) :=
  let ⟨label, succ⟩ := neighbor
  let fingerprint := fp.view succ
  if ctx.seen.contains fingerprint then pure ctx
  else pure <|
    let ctx_with_seen : @SequentialSearchContext ρ σ κ σₕ fp th sys params := {
      ctx with
        seen := ctx.seen.insert fingerprint,
        log := ctx.log.insert fingerprint (fpSt, label),
        invs := by
          constructor
          · -- queue_sound: queue unchanged, so invariant preserved
            intro x d h_in_queue
            exact ctx.invs.queue_sound x d h_in_queue
          · -- visited_sound: new seen element is the reachable neighbor
            intro h_view_inj x h_in_seen
            rw [Membership.mem] at h_in_seen
            by_cases h : fp.view x = fingerprint
            · have : x = succ := h_view_inj h
              rw [this]; exact h_neighbor
            · have h_in_old : ctx.seen.contains (fp.view x) := by grind
              exact ctx.invs.visited_sound h_view_inj x h_in_old
          · -- queue_sub_visited: queue unchanged, but seen expanded
            intro x d h_in_queue
            have h_old := ctx.invs.queue_sub_visited x d h_in_queue
            rw [Membership.mem]
            grind
          · -- queue_wellformed: queue unchanged
            intro fp' st d h_in_queue
            exact ctx.invs.queue_wellformed fp' st d h_in_queue
    }
    { ctx_with_seen with
        sq := ctx_with_seen.sq.enqueue ⟨fingerprint, succ, depth + 1⟩,
        invs := by
          constructor
          · -- queue_sound: new element in queue is reachable
            intro x d h_in_queue
            simp only [Membership.mem, fQueue.enqueue] at h_in_queue
            rcases h_in_queue with h_in_front | h_in_back
            · -- x was already in the old queue (front unchanged)
              exact ctx_with_seen.invs.queue_sound x d (Or.inl h_in_front)
            · -- x is in the back, which now includes the new element
              have : ⟨fp.view x, x, d⟩ ∈ (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ) :: ctx_with_seen.sq.back := h_in_back
              simp only [List.mem_cons] at this
              rcases this with h_eq | h_in_old_back
              · -- x is the newly enqueued element: ⟨fp.view x, x, d⟩ = ⟨fingerprint, succ, depth + 1⟩
                have h_x : x = succ := by
                  have := congrArg QueueItem.state h_eq
                  exact this
                rw [h_x]
                exact h_neighbor
              · -- x was in the old back
                exact ctx_with_seen.invs.queue_sound x d (Or.inr h_in_old_back)
          · -- visited_sound: seen unchanged
            intro h_view_inj x h_in_seen
            exact ctx_with_seen.invs.visited_sound h_view_inj x h_in_seen
          · -- queue_sub_visited: new queue element's fingerprint is in seen
            intro x d h_in_queue
            simp only [Membership.mem, fQueue.enqueue] at h_in_queue
            rcases h_in_queue with h_in_front | h_in_back
            · exact ctx_with_seen.invs.queue_sub_visited x d (Or.inl h_in_front)
            · have : ⟨fp.view x, x, d⟩ ∈ (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ) :: ctx_with_seen.sq.back := h_in_back
              simp only [List.mem_cons] at this
              rcases this with h_eq | h_in_old_back
              · -- The new element: its fingerprint was just added to seen
                have h_fp : fp.view x = fingerprint := by
                  have := congrArg QueueItem.fingerprint h_eq
                  exact this
                rw [h_fp, Membership.mem]
                grind
              · exact ctx_with_seen.invs.queue_sub_visited x d (Or.inr h_in_old_back)
          · -- queue_wellformed: new element has matching fingerprint
            intro fp' st d h_in_queue
            simp only [Membership.mem, fQueue.enqueue] at h_in_queue
            rcases h_in_queue with h_in_front | h_in_back
            · exact ctx_with_seen.invs.queue_wellformed fp' st d (Or.inl h_in_front)
            · have : ⟨fp', st, d⟩ ∈ (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ) :: ctx_with_seen.sq.back := h_in_back
              simp only [List.mem_cons] at this
              rcases this with h_eq | h_in_old_back
              · -- The new element: fp' = fingerprint and st = succ
                have h_fp' : fp' = fingerprint := by
                  have := congrArg QueueItem.fingerprint h_eq
                  exact this
                have h_st : st = succ := by
                  have := congrArg QueueItem.state h_eq
                  exact this
                rw [h_st, h_fp']
              · exact ctx_with_seen.invs.queue_wellformed fp' st d (Or.inr h_in_old_back)
    }

@[inline, specialize]
def SequentialSearchContext.processState {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)
  (depth : Nat)  -- depth of the current state
  (curr : σ)
  (h_curr : sys.reachable curr)
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp th sys params) :
  m (@SequentialSearchContext ρ σ κ σₕ fp th sys params) := do
  let (baseCtx', outcomesOpt) := ctx.toBaseSearchContext.processState sys fpSt curr
  match outcomesOpt with
  | none => pure { ctx with
      toBaseSearchContext := baseCtx'
      invs := sorry
    }
  | some ⟨outcomes, heq⟩ =>
      -- Extract only successful transitions for queueing
      let successfulTransitions := extractSuccessfulTransitions outcomes
      let ctx_updated := { ctx with toBaseSearchContext := baseCtx', invs := sorry }
      successfulTransitions.attach.foldlM (init := ctx_updated) (fun current_ctx ⟨⟨tr, postState⟩, h_neighbor_in_tr⟩ => do
      if current_ctx.hasFinished then pure current_ctx
      else
        -- Reachability proof: the neighbor is in successful transitions extracted from outcomes
        let h_neighbor_reachable : sys.reachable postState := by
          apply EnumerableTransitionSystem.reachable.step curr postState h_curr
          exists tr
          -- h_neighbor_in_tr proves (tr, postState) ∈ successfulTransitions
          -- successfulTransitions = extractSuccessfulTransitions outcomes
          -- This means (tr, .success postState) ∈ outcomes = sys.tr th curr
          have h_in_filtered : (tr, postState) ∈ extractSuccessfulTransitions outcomes := h_neighbor_in_tr
          unfold extractSuccessfulTransitions at h_in_filtered
          rw [List.mem_filterMap] at h_in_filtered
          obtain ⟨⟨label, outcome⟩, h_mem, h_eq⟩ := h_in_filtered
          cases outcome with
          | success st =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h_eq
            obtain ⟨h_label, h_st⟩ := h_eq
            rw [← h_label, ← h_st, ← heq]
            exact h_mem
          | assertionFailure _ _ => simp at h_eq
          | divergence => simp at h_eq
        SequentialSearchContext.tryExploreNeighbor sys fpSt depth current_ctx ⟨tr, postState⟩ h_neighbor_reachable
    )

/-- Perform one step of BFS. -/
@[inline, specialize]
def SequentialSearchContext.bfsStep {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp th sys params) :
  m (@SequentialSearchContext ρ σ κ σₕ fp th sys params) :=
  match ctx.sq.dequeue? with
  | none => pure { ctx with finished := some (.exploredAllReachableStates) }
  | some (⟨fpSt, curr, depth⟩, q_tail) => do
    have h_curr : sys.reachable curr := sorry
    -- Update completed depth when we move to a new frontier level
    let (newCompletedDepth, newFrontierDepth) :=
      if depth > ctx.currentFrontierDepth then
        (depth - 1, depth)  -- All states at previous depth are now fully explored
      else
        (ctx.completedDepth, ctx.currentFrontierDepth)
    let ctx_dequeued : @SequentialSearchContext ρ σ κ σₕ fp th sys params := {
      ctx with
        sq := q_tail,
        completedDepth := newCompletedDepth,
        currentFrontierDepth := newFrontierDepth,
        invs := sorry
    }
    SequentialSearchContext.processState sys fpSt depth curr h_curr ctx_dequeued

@[specialize]
def breadthFirstSearchSequential {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken) :
  m (@SequentialSearchContext ρ σ κ σₕ fp th sys params) := do
  let mut ctx : @SequentialSearchContext ρ σ κ σₕ fp th sys params := SequentialSearchContext.initial sys params
  let mut statesProcessed : Nat := 0
  let mut lastUpdateTime : Nat := 0
  while !ctx.hasFinished do
    statesProcessed := statesProcessed + 1
    -- Update progress and check for cancellation/handoff at most once per second
    let now ← IO.monoMsNow
    if now - lastUpdateTime >= 1000 then
      lastUpdateTime := now
      updateProgress progressInstanceId ctx.seen.size statesProcessed ctx.sq.size ctx.currentFrontierDepth ctx.completedDepth
      if ← shouldStop cancelToken progressInstanceId then
        ctx := { ctx with finished := some (.earlyTermination .cancelled) }
        break
    ctx := ← SequentialSearchContext.bfsStep sys ctx
    -- If we found a violation, mark it so handoff is prevented
    if let some (.earlyTermination cond) := ctx.finished then
      if EarlyTerminationReason.isViolation cond then setViolationFound progressInstanceId
  -- Final update to ensure stats reflect finished state
  updateProgress progressInstanceId ctx.seen.size statesProcessed ctx.sq.size ctx.currentFrontierDepth ctx.completedDepth
  return ctx

end Veil.ModelChecker.Concrete
