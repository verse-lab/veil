import Veil.Core.Tools.ModelChecker.Concrete.Core
import Veil.Core.Tools.ModelChecker.Concrete.Progress

namespace Veil.ModelChecker.Concrete
open Std

structure ParallelSearchContextMain {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
extends @BaseSearchContext ρ σ κ σₕ fp instBEq instHash th sys params
where
  /-- Recording the nodes to visit in the next depth. Due to the way
  parallel BFS works, it could be any data structure that supports `O(1)`
  element insertion (e.g., `Array`); but to support efficient merging,
  it's made to be an `HashMap`. -/
  tovisit : Std.HashMap σₕ (σ × Nat)
  invs  : @SearchContextInvariants ρ σ κ σₕ fp th sys params (fun ⟨h, x, d⟩ => tovisit[h]? = some (x, d)) (Membership.mem seen)

structure ParallelSearchContextSub {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
extends @BaseSearchContext ρ σ κ σₕ fp instBEq instHash th sys params
where
  tovisit : Array (QueueItem σₕ σ)
  localSeen : Std.HashSet σₕ
  localLog : Std.HashMap σₕ (σₕ × κ)
  invs  : @SearchContextInvariants ρ σ κ σₕ fp th sys params (Membership.mem tovisit) (fun h => h ∈ seen ∨ h ∈ localSeen)
  /-- Local count of post-states generated (before deduplication) -/
  localStatesFound : Nat := 0
  /-- Local per-action statistics: label → stats -/
  localActionStatsMap : Std.HashMap κ ActionStat := {}

/-- Merge action stats maps by summing counts for each action. -/
private def mergeActionStatsMaps [BEq κ] [Hashable κ] (m1 m2 : Std.HashMap κ ActionStat) : Std.HashMap κ ActionStat :=
  m2.fold (init := m1) fun acc label stat2 =>
    match acc[label]? with
    | some stat1 => acc.insert label { statesGenerated := stat1.statesGenerated + stat2.statesGenerated, distinctStates := stat1.distinctStates + stat2.distinctStates }
    | none => acc.insert label stat2

def ParallelSearchContextSub.merge1 {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] {th : ρ} {sys : _} {params : _}
  (mainCtx : @ParallelSearchContextMain ρ σ κ σₕ fp _ _ th sys params)
  (subCtx : @ParallelSearchContextSub ρ σ κ σₕ fp _ _ th sys params) :
  @ParallelSearchContextMain ρ σ κ σₕ fp _ _ th sys params := {
    mainCtx with
      seen := mainCtx.seen.union subCtx.localSeen,
      log := mainCtx.log.union subCtx.localLog,
      violatingStates := subCtx.violatingStates ++ mainCtx.violatingStates,
      finished := Option.or mainCtx.finished subCtx.finished
      -- do not update depth information here
      tovisit := subCtx.tovisit.foldl (init := mainCtx.tovisit) fun acc ⟨h, x, d⟩ => acc.insertIfNew h (x, d)
      -- Merge stats from sub-context
      statesFound := mainCtx.statesFound + subCtx.localStatesFound
      actionStatsMap := mergeActionStatsMaps mainCtx.actionStatsMap subCtx.localActionStatsMap
      invs := sorry
  }

def ParallelSearchContextSub.merge2 {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] {th : ρ} {sys : _} {params : _}
  (mainCtx : @ParallelSearchContextMain ρ σ κ σₕ fp _ _ th sys params)
  (subCtx : @ParallelSearchContextSub ρ σ κ σₕ fp _ _ th sys params) :
  @ParallelSearchContextMain ρ σ κ σₕ fp _ _ th sys params := {
    mainCtx with
      tovisit := subCtx.tovisit.foldl (init := mainCtx.tovisit) fun acc ⟨h, x, d⟩ =>
        if !mainCtx.seen.contains h then acc.insertIfNew h (x, d) else acc
      invs := sorry
  }

def ParallelSearchContextMain.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ) :
  @ParallelSearchContextMain ρ σ κ σₕ fp _ _ th sys params := {
    BaseSearchContext.initial sys params with
    tovisit := Std.HashMap.ofList (sys.initStates |> Functor.map (fun s => ⟨fp.view s, s, 0⟩))
    invs := sorry
  }

@[inline, specialize]
def ParallelSearchContextSub.tryExploreNeighbor {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)  -- fingerprint of state we're coming from (pre-state), for logging
  (depth : Nat)  -- depth of the current state (neighbor will be at depth + 1)
  (ctx : @ParallelSearchContextSub ρ σ κ σₕ fp _ _ th sys params)
  (neighbor : κ × σ)
  (h_neighbor : sys.reachable neighbor.2) :
  m (@ParallelSearchContextSub ρ σ κ σₕ fp _ _ th sys params) :=
  let ⟨label, succ⟩ := neighbor
  let fingerprint := fp.view succ
  if ctx.seen.contains fingerprint || ctx.localSeen.contains fingerprint then pure ctx
  else
    -- This is a new distinct state - update per-action distinctStates count
    let newActionStatsMap := match ctx.localActionStatsMap[label]? with
      | some stat => ctx.localActionStatsMap.insert label { stat with distinctStates := stat.distinctStates + 1 }
      | none => ctx.localActionStatsMap.insert label { statesGenerated := 0, distinctStates := 1 }
    pure <|
    let ctx_with_seen : @ParallelSearchContextSub ρ σ κ σₕ fp _ _ th sys params := {
      ctx with
        localSeen := ctx.localSeen.insert fingerprint,
        localLog := ctx.localLog.insert fingerprint (fpSt, label),
        localActionStatsMap := newActionStatsMap,
        invs := sorry
    }
    { ctx_with_seen with
        tovisit := ctx_with_seen.tovisit.push ⟨fingerprint, succ, depth + 1⟩,
        invs := sorry
    }

@[inline, specialize]
def ParallelSearchContextSub.processState {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr σ] [Repr σₕ] [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)
  (depth : Nat)  -- depth of the current state
  (curr : σ)
  (h_curr : sys.reachable curr)
  (ctx : @ParallelSearchContextSub ρ σ κ σₕ fp _ _ th sys params) :
  m (@ParallelSearchContextSub ρ σ κ σₕ fp _ _ th sys params) := do
  let (baseCtx', outcomesOpt) := ctx.toBaseSearchContext.processState sys fpSt curr
  match outcomesOpt with
  | none => pure { ctx with
      toBaseSearchContext := baseCtx'
      invs := sorry
    }
  | some ⟨outcomes, heq⟩ =>
      -- Extract only successful transitions for queueing
      let successfulTransitions := extractSuccessfulTransitions outcomes
      -- Update localStatesFound: count ALL successful transitions (before dedup)
      let newLocalStatesFound := ctx.localStatesFound + successfulTransitions.length
      -- Update per-action statesGenerated counts
      let newLocalActionStatsMap := successfulTransitions.foldl (init := ctx.localActionStatsMap) fun acc (label, _) =>
        match acc[label]? with
        | some stat => acc.insert label { stat with statesGenerated := stat.statesGenerated + 1 }
        | none => acc.insert label { statesGenerated := 1, distinctStates := 0 }
      let ctx_updated := { ctx with
        toBaseSearchContext := baseCtx'
        localStatesFound := newLocalStatesFound
        localActionStatsMap := newLocalActionStatsMap
        invs := sorry
      }
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
        ParallelSearchContextSub.tryExploreNeighbor sys fpSt depth current_ctx ⟨tr, postState⟩ h_neighbor_reachable
    )

@[inline, specialize]
def ParallelSearchContextSub.bfsBigStep {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr σ] [Repr σₕ] [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (queue : Array (σₕ × σ × Nat)) :
  m (@ParallelSearchContextSub ρ σ κ σₕ fp _ _ th sys params) := do
  -- let startTime ← IO.monoMsNow
  let ctx : @ParallelSearchContextSub ρ σ κ σₕ fp _ _ th sys params := {
    baseCtx with
    tovisit := #[],
    localSeen := HashSet.emptyWithCapacity,
    localLog := Std.HashMap.emptyWithCapacity,
    invs := sorry
  }
  let queueSz := queue.size
  let res ← queue.foldlM (init := ctx) fun current_ctx ⟨fpSt, curr, depth⟩ => do
    have h_curr : sys.reachable curr := sorry
    ParallelSearchContextSub.processState sys fpSt depth curr h_curr current_ctx
  -- let endTime ← IO.monoMsNow
  -- IO.eprintln s!"[{endTime} @ tid {← IO.getTID}] took {endTime - startTime}ms to process {queueSz} states (queue size now: {queue.size})"
  return res

@[specialize]
def breadthFirstSearchParallel {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr σ] [Repr σₕ] [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (parallelCfg : ParallelConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken) :
  m (@ParallelSearchContextMain ρ σ κ σₕ fp _ _ th sys params) := do
  let mut ctx : @ParallelSearchContextMain ρ σ κ σₕ fp _ _ th sys params := ParallelSearchContextMain.initial sys params
  let mut lastUpdateTime : Nat := 0
  while !ctx.hasFinished do
    -- In this setting, the queue emptiness check needs to be done here
    if ctx.tovisit.isEmpty then
      ctx := { ctx with finished := some (.exploredAllReachableStates) }
      -- Final update before early return
      updateProgress progressInstanceId
        ctx.currentFrontierDepth ctx.statesFound ctx.seen.size ctx.tovisit.size
        (toActionStatsList ctx.actionStatsMap)
      return ctx
    let tovisitArr := ctx.tovisit.toArray
    ctx := {ctx with
      tovisit := Std.HashMap.emptyWithCapacity,
      completedDepth := ctx.currentFrontierDepth,
      currentFrontierDepth := ctx.currentFrontierDepth + 1,
      invs := sorry
    }
    let tasks ← (parallelCfg.taskSplit (ParallelSearchContextSub.bfsBigStep sys ctx.toBaseSearchContext) tovisitArr)
    -- IO.eprintln s!"[{← IO.monoMsNow} @ tid {← IO.getTID}] spawned {tasks.length} tasks"
    let results ← (tasks.mapM (fun task => IO.ofExcept task.get))
    -- compute `seen` first, and then merge the `tovisit`s, since need to
    -- filter out already seen states when merging
    ctx := results.foldl (init := ctx) ParallelSearchContextSub.merge1
    ctx := results.foldl (init := ctx) ParallelSearchContextSub.merge2
    -- If we found a violation, mark it so handoff is prevented
    if let some (.earlyTermination cond) := ctx.finished then
      if EarlyTerminationReason.isViolation cond then setViolationFound progressInstanceId
    -- Update progress and check for cancellation/handoff at most once per second
    let now ← IO.monoMsNow
    if now - lastUpdateTime >= 1000 then
      lastUpdateTime := now
      -- TLC-style stats: diameter, statesFound, distinctStates, queue, actionStats
      updateProgress progressInstanceId
        ctx.currentFrontierDepth ctx.statesFound ctx.seen.size ctx.tovisit.size
        (toActionStatsList ctx.actionStatsMap)
      if ← shouldStop cancelToken progressInstanceId then
        ctx := { ctx with finished := some (.earlyTermination .cancelled) }
        break
  -- Final update to ensure stats reflect finished state
  updateProgress progressInstanceId
    ctx.currentFrontierDepth ctx.statesFound ctx.seen.size ctx.tovisit.size
    (toActionStatsList ctx.actionStatsMap)
  return ctx

end Veil.ModelChecker.Concrete
