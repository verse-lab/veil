import Veil.Core.Tools.ModelChecker.ConcreteNew.ParallelLemmas
import Veil.Core.Tools.ModelChecker.ConcreteNew.Progress
import Veil.Core.Tools.ModelChecker.Concrete.Subtypes

namespace Veil.ModelChecker.Concrete
open Veil

variable {ρ σ κ σₕ : Type} [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ]
  (params : SearchParameters ρ σ) (th : ρ)

@[inline]
def MapReduceSearchContextMain.hasFinished (mctx : MapReduceSearchContextMain σ κ σₕ) : Bool :=
  mctx.base.hasFinished

@[inline]
def MapReduceSearchContextLocal.hasFinished (lctx : MapReduceSearchContextLocal σ κ σₕ) : Bool :=
  lctx.1.hasFinished

-- FIXME: The logic of `tryExploreNeighbor`, `processSuccessors`, and `processState`
-- seems very similar to the sequential processing logic. We should try to unify them

omit params th in
/-- Process a single neighbor in the local context.
    `globalLog` is the main context's log, used to check if a state is already globally seen. -/
@[inline]
def MapReduceSearchContextLocal.tryExploreNeighbor
  (globalLog : Std.HashMap σₕ (Option (σₕ × κ)))
  (fpSt : σₕ) (nextDepth : Nat)
  (lctx : MapReduceSearchContextLocal σ κ σₕ)
  (label : κ) (succ : σ) : MapReduceSearchContextLocal σ κ σₕ :=
  let (ctx, q) := lctx
  let fingerprint := fp.view succ
  if globalLog.contains fingerprint || ctx.log.contains fingerprint then
    ({ ctx with actionStatsMap := ctx.actionStatsMap.update false label  }, q)
  else
    ({ ctx with
      log := ctx.log.insert fingerprint (Option.some (fpSt, label)),
      actionStatsMap := ctx.actionStatsMap.update true label
    }, q.push ⟨fingerprint, succ, nextDepth⟩)

omit params th in
/-- Process all successors of a state in the local context. -/
def MapReduceSearchContextLocal.processSuccessors
  (globalLog : Std.HashMap σₕ (Option (σₕ × κ)))
  (fpSt : σₕ) (depth : Nat)
  (successors : List (κ × σ))
  (lctx : MapReduceSearchContextLocal σ κ σₕ) : MapReduceSearchContextLocal σ κ σₕ :=
  let nextDepth := depth + 1
  successors.foldl (init := lctx) fun current_lctx (label, postState) =>
    MapReduceSearchContextLocal.tryExploreNeighbor globalLog fpSt nextDepth current_lctx label postState

/-- Process a single state: check violations via BaseSearchContext.processState,
    then process successors if no early termination. -/
def MapReduceSearchContextLocal.processState
  (globalLog : Std.HashMap σₕ (Option (σₕ × κ)))
  (fpSt : σₕ) (depth : Nat) (curr : σ)
  (outcomes : List (κ × ExecutionOutcome ℤ σ))
  (lctx : MapReduceSearchContextLocal σ κ σₕ) : MapReduceSearchContextLocal σ κ σₕ :=
  let (ctx, q) := lctx
  let (ctx', outcomesOpt) := ctx.processState params th fpSt curr outcomes
  match outcomesOpt with
  | none => (ctx', q)
  | some successfulTransitions =>
    -- CHECK Is it useful/possible to remove the call to `successfulTransitions.length`?
    let ctx'' := { ctx' with statesFound := ctx'.statesFound + successfulTransitions.length }
    MapReduceSearchContextLocal.processSuccessors globalLog fpSt depth successfulTransitions (ctx'', q)

def MapReduceSearchContextLocal.processWorkQueue
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (globalLog : Std.HashMap σₕ (Option (σₕ × κ)))
  (queueList : List (QueueItem σₕ σ))
  (lctx : MapReduceSearchContextLocal σ κ σₕ) : MapReduceSearchContextLocal σ κ σₕ :=
  match queueList with
  | [] => lctx
  | ⟨fpSt, curr, depth⟩ :: rest =>
    let lctx' := MapReduceSearchContextLocal.processState params th globalLog fpSt depth curr (sys.tr th curr) lctx
    if lctx'.hasFinished then lctx'
    else processWorkQueue sys globalLog rest lctx'

/-- Main worker entry point. Creates a neutral context and processes the work queue.
    This function is called by each parallel task. -/
def MapReduceSearchContextLocal.bfsBigStep
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (globalLog : Std.HashMap σₕ (Option (σₕ × κ)))
  (completedDepth : Nat)
  (queue : Array (QueueItem σₕ σ)) : MapReduceSearchContextLocal σ κ σₕ :=
  let lctx : MapReduceSearchContextLocal σ κ σₕ := MapReduceSearchContextLocal.initial completedDepth
  MapReduceSearchContextLocal.processWorkQueue params th sys globalLog queue.toList lctx

omit params th in
def MapReduceSearchContextMain.mergeWithLocalOnes {as : List α}
  (mctx : MapReduceSearchContextMain σ κ σₕ)
  (lctxs : IteratedProd (as.map fun _ => MapReduceSearchContextLocal σ κ σₕ)) : MapReduceSearchContextMain σ κ σₕ :=
  IteratedProd.foldl (elements := lctxs) (init := mctx) fun acc r =>
    let ⟨mbase, mq, st⟩ := acc
    -- TODO need to think about the semantics of `st`
    let (lbase, lq) := r
    let (mq', st') := lq.foldl (init := (mq, st)) fun (mq_acc, st_acc) item =>
      if !st_acc.contains item.fingerprint then
        (mq_acc.push item, st_acc.insert item.fingerprint)
      else
        (mq_acc, st_acc)
    ⟨mbase.mergeWithoutDepthChange lbase, mq', st'⟩

-- FIXME: This is also very similar to the sequential version
@[inline]
def updateProgressDuringBFSParallel [Monad m]
  [MonadLiftT BaseIO m] [MonadLiftT IO m] [Repr κ]
  (progressInstanceId : Nat)
  (ctx : BaseSearchContext σ κ σₕ)
  (sq : Array (QueueItem σₕ σ)) : m Unit := do
  updateProgress progressInstanceId
    ctx.currentFrontierDepth ctx.statesFound ctx.log.size sq.size
    (toActionStatsList ctx.actionStatsMap)

omit th in
@[specialize]
def breadthFirstSearchParallel {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (parallelCfg : ParallelConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken) :
  m (MapReduceSearchContextMain σ κ σₕ) := do
  let mut mctx : MapReduceSearchContextMain σ κ σₕ := MapReduceSearchContextMain.initial sys
  let mut lastUpdateTime : Nat := 0
  let mut cancelled := false
  while h_not_finished : mctx.hasFinished = false do
    -- FIXME: Need to add a sequential fallback if the frontier is too small
    -- Check if the frontier is empty
    if mctx.tovisitQueue.isEmpty then
      mctx := { mctx with base := { mctx.base with finished := some (.exploredAllReachableStates) } }
      break
    else
      let tovisitArr := mctx.tovisitQueue
      -- Compute chunk ranges for splitting the work
      let ranges := ParallelConfig.chunkRanges parallelCfg tovisitArr.size
      -- Split the queue into sub-arrays of `QueueItems`
      -- CHECK Is the memory usage of this split correct? In any case, if we replace the `Array` with `List`,
      -- we should be able to somehow minimize the additional memory allocation.
      -- A similar issue happens above in the `queueList` above.
      let splitArrays := ranges.map fun lr => tovisitArr.extract lr.1 lr.2
      let globalLog := mctx.base.log    -- CHECK sharing --> bad copy?
      let completedDepth := mctx.base.completedDepth
      -- Map step: spawn parallel tasks
      -- **CAVEAT**: The call to `IO.asTask` **SHOULD NOT** be put in this procedure,
      -- as that might cause parallelism to vanish!!! Instead, the call should be defined
      -- in some other file.
      let tasks ← IteratedProd.taskSplit splitArrays fun subArr _h_subArr_in =>
        (pure (MapReduceSearchContextLocal.bfsBigStep params th sys globalLog completedDepth subArr) : IO _)
      let results ← IteratedProd.mapM (fun task => IO.ofExcept task.get) tasks
      -- Reduce step
      mctx := mctx.mergeWithLocalOnes results

      trySetViolationFound progressInstanceId mctx.base
      -- Update progress on every diameter change
      updateProgressDuringBFS progressInstanceId mctx.base mctx.tovisitQueue.size
      -- Check for cancellation/handoff at most once per second
      let newtime? ← checkCancellationWithoutPeriodicUpdate progressInstanceId lastUpdateTime 1000 cancelToken
      -- sctx := Subtype.mk (ctx', sq') (heq.symm ▸ h_sctx')
      match newtime? with
      | .updateTime t => lastUpdateTime := t
      | .searchCancelled => cancelled := true ; break
      | .noUpdate => pure ()
  -- Final update to ensure stats reflect finished state
  updateProgressDuringBFS progressInstanceId mctx.base mctx.tovisitQueue.size
  if cancelled then
    let mctx' := { mctx with base := {mctx.base with finished := some (.earlyTermination .cancelled) }}
    return mctx'
  else
    return mctx

end Veil.ModelChecker.Concrete
