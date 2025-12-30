import Veil.Core.Tools.ModelChecker.Concrete.Core
import Veil.Core.Tools.ModelChecker.Concrete.Progress

namespace Veil.ModelChecker.Concrete
open Std

structure ParallelSearchContextMain {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ)
extends @BaseSearchContext ρ σ κ σₕ fp th sys params
where
  /-- Recording the nodes to visit in the next depth. Due to the way
  parallel BFS works, it could be any data structure that supports `O(1)`
  element insertion (e.g., `Array`); but to support efficient merging,
  it's made to be an `HashMap`. -/
  tovisit : Std.HashMap σₕ (σ × Nat)
  invs  : @SearchContextInvariants ρ σ κ σₕ fp th sys params (fun ⟨h, x, d⟩ => tovisit[h]? = some (x, d)) (Membership.mem seen)

structure ParallelSearchContextSub {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ)
extends @BaseSearchContext ρ σ κ σₕ fp th sys params
where
  tovisit : Array (QueueItem σₕ σ)
  localSeen : Std.HashSet σₕ
  localLog : Std.HashMap σₕ (σₕ × κ)
  invs  : @SearchContextInvariants ρ σ κ σₕ fp th sys params (Membership.mem tovisit) (fun h => h ∈ seen ∨ h ∈ localSeen)

def ParallelSearchContextSub.merge1 {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] {th : ρ} {sys : _} {params : _}
  (mainCtx : @ParallelSearchContextMain ρ σ κ σₕ fp th sys params)
  (subCtx : @ParallelSearchContextSub ρ σ κ σₕ fp th sys params) :
  @ParallelSearchContextMain ρ σ κ σₕ fp th sys params := {
    mainCtx with
      seen := mainCtx.seen.union subCtx.localSeen,
      log := mainCtx.log.union subCtx.localLog,
      violatingStates := subCtx.violatingStates ++ mainCtx.violatingStates,
      finished := Option.or mainCtx.finished subCtx.finished
      -- do not update depth information here
      tovisit := subCtx.tovisit.foldl (init := mainCtx.tovisit) fun acc ⟨h, x, d⟩ => acc.insertIfNew h (x, d)
      invs := sorry
  }

def ParallelSearchContextSub.merge2 {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] {th : ρ} {sys : _} {params : _}
  (mainCtx : @ParallelSearchContextMain ρ σ κ σₕ fp th sys params)
  (subCtx : @ParallelSearchContextSub ρ σ κ σₕ fp th sys params) :
  @ParallelSearchContextMain ρ σ κ σₕ fp th sys params := {
    mainCtx with
      tovisit := subCtx.tovisit.foldl (init := mainCtx.tovisit) fun acc ⟨h, x, d⟩ =>
        if !mainCtx.seen.contains h then acc.insertIfNew h (x, d) else acc
      invs := sorry
  }

def ParallelSearchContextMain.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ) :
  @ParallelSearchContextMain ρ σ κ σₕ fp th sys params := {
    BaseSearchContext.initial sys params with
    tovisit := Std.HashMap.ofList (sys.initStates |> Functor.map (fun s => ⟨fp.view s, s, 0⟩))
    invs := sorry
  }

@[inline, specialize]
def ParallelSearchContextSub.tryExploreNeighbor {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)  -- fingerprint of state we're coming from (pre-state), for logging
  (depth : Nat)  -- depth of the current state (neighbor will be at depth + 1)
  (ctx : @ParallelSearchContextSub ρ σ κ σₕ fp th sys params)
  (neighbor : κ × σ)
  (h_neighbor : sys.reachable neighbor.2) :
  m (@ParallelSearchContextSub ρ σ κ σₕ fp th sys params) :=
  let ⟨label, succ⟩ := neighbor
  let fingerprint := fp.view succ
  if ctx.seen.contains fingerprint || ctx.localSeen.contains fingerprint then pure ctx
  else pure <|
    let ctx_with_seen : @ParallelSearchContextSub ρ σ κ σₕ fp th sys params := {
      ctx with
        localSeen := ctx.localSeen.insert fingerprint,
        localLog := ctx.localLog.insert fingerprint (fpSt, label),
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
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)
  (depth : Nat)  -- depth of the current state
  (curr : σ)
  (h_curr : sys.reachable curr)
  (ctx : @ParallelSearchContextSub ρ σ κ σₕ fp th sys params) :
  m (@ParallelSearchContextSub ρ σ κ σₕ fp th sys params) := do
  let (baseCtx', successorsOpt) := ctx.toBaseSearchContext.processState sys fpSt curr
  match successorsOpt with
  | none => pure { ctx with
      toBaseSearchContext := baseCtx'
      invs := sorry
    }
  | some ⟨successors, heq⟩ =>
      let ctx_updated := { ctx with toBaseSearchContext := baseCtx', invs := sorry }
      successors.attach.foldlM (init := ctx_updated) (fun current_ctx ⟨⟨tr, postState⟩, h_neighbor_in_tr⟩ => do
      if current_ctx.hasFinished then pure current_ctx
      else
        let h_neighbor_reachable : sys.reachable postState :=
          EnumerableTransitionSystem.reachable.step curr postState h_curr ⟨tr, heq ▸ h_neighbor_in_tr⟩
        ParallelSearchContextSub.tryExploreNeighbor sys fpSt depth current_ctx ⟨tr, postState⟩ h_neighbor_reachable
    )

@[inline, specialize]
def ParallelSearchContextSub.bfsBigStep {ρ σ κ σₕ : Type} {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp th sys params)
  (queue : Array (σₕ × σ × Nat)) :
  m (@ParallelSearchContextSub ρ σ κ σₕ fp th sys params) := do
  -- let startTime ← IO.monoMsNow
  let ctx : @ParallelSearchContextSub ρ σ κ σₕ fp th sys params := {
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
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ)
  (parallelCfg : ParallelConfig) :
  m (@ParallelSearchContextMain ρ σ κ σₕ fp th sys params) := do
  let mut ctx : @ParallelSearchContextMain ρ σ κ σₕ fp th sys params := ParallelSearchContextMain.initial sys params
  let mut statesProcessed : Nat := 0
  let mut lastUpdateTime : Nat := 0
  while !ctx.hasFinished do
    -- In this setting, the queue emptiness check needs to be done here
    if ctx.tovisit.isEmpty then
      ctx := { ctx with finished := some (.exploredAllReachableStates) }
      return ctx
    let tovisitArr := ctx.tovisit.toArray
    statesProcessed := statesProcessed + tovisitArr.size
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
    -- Update progress at most once per second
    let now ← IO.monoMsNow
    if now - lastUpdateTime >= 1000 then
      lastUpdateTime := now
      updateProgress ctx.seen.size statesProcessed ctx.tovisit.size ctx.currentFrontierDepth ctx.completedDepth
  return ctx

end Veil.ModelChecker.Concrete
