import Veil.Core.Tools.ModelChecker.ConcreteNew.MapReduce

namespace Veil.ModelChecker.Concrete
open Veil

variable {ρ σ κ σₕ : Type} [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] [Ord σₕ]
  (params : SearchParameters ρ σ) (th : ρ)

-- For now, do not bother with it
/-
omit th in
def breadthFirstSearchParallelWithPredefinedInterruptions {m : Type → Type}
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
    match mctx with
    | (base, tovisitArr, globalSeen) =>
      -- Check if the frontier is empty
      if tovisitArr.isEmpty then
        mctx := ({ base with finished := some (.exploredAllReachableStates) }, tovisitArr, globalSeen)
        break
      else
        -- Split the frontier into fine-grained chunks for sub-stepping.
        -- Each BFS layer is processed in `numSubSteps` sub-steps, with a reduce
        -- (merge) after each sub-step to update `globalSeen`, reducing redundant
        -- state exploration across threads.
        let numSubSteps := max 1 parallelCfg.numSubSteps
        let totalChunks := if tovisitArr.size < parallelCfg.thresholdToParallel then 1
          else max 1 parallelCfg.numSubTasks * numSubSteps
        let fineRanges := computeChunkRanges totalChunks tovisitArr.size
        let allChunkArrays := fineRanges.toArray.map fun lr => tovisitArr.extract lr.1 lr.2
        -- Compute sub-step intervals: each covers ~numSubTasks consecutive chunk arrays
        let effectiveSubSteps := if tovisitArr.size < parallelCfg.thresholdToParallel then 1 else numSubSteps
        let subStepIntervals := computeChunkRanges effectiveSubSteps allChunkArrays.size
        let completedDepth := base.completedDepth
        let mut currentGlobalSeen := globalSeen
        let mut currentBase := base
        let mut accumulatedQueue : Array (QueueItem σₕ σ) := #[]
        -- Inner loop: process each sub-step, merging after each to update globalSeen
        for (subL, subR) in subStepIntervals do
          if currentBase.hasFinished || cancelled then break
          let splitArrays := (allChunkArrays.extract subL subR).toList
          -- Map step: spawn parallel tasks
          -- **CAVEAT**: The call to `IO.asTask` **SHOULD NOT** be put in this procedure,
          -- as that might cause parallelism to vanish!!! Instead, the call should be defined
          -- in some other file.
          let tasks ← IteratedProd.taskSplit splitArrays fun subArr _ =>
            (pure (MapReduceSearchContextLocal.bfsBigStep params th currentGlobalSeen sys.tr completedDepth subArr) : IO _)
          let results ← IteratedProd.mapM (fun task => IO.ofExcept task.get) tasks
          -- Reduce step: merge results and update globalSeen
          let tempMctx : MapReduceSearchContextMain σ κ σₕ := (currentBase, #[], currentGlobalSeen)
          let merged := tempMctx.mergeWithLocalOnes results
          match merged with
          | (newBase, newQueueItems, newGlobalSeen) =>
            currentBase := newBase
            accumulatedQueue := accumulatedQueue ++ newQueueItems
            currentGlobalSeen := newGlobalSeen
            trySetViolationFound progressInstanceId newBase
            updateProgressDuringBFS progressInstanceId newBase accumulatedQueue.size
            let newtime? ← checkCancellationWithoutPeriodicUpdate progressInstanceId lastUpdateTime 1000 cancelToken
            match newtime? with
            | .updateTime t => lastUpdateTime := t
            | .searchCancelled => cancelled := true
            | .noUpdate => pure ()
        mctx := (currentBase, accumulatedQueue, currentGlobalSeen)
        if cancelled then break
  -- Final update to ensure stats reflect finished state
  updateProgressDuringBFS progressInstanceId mctx.1 mctx.2.1.size
  if cancelled then
    let mctx' := ({ mctx.1 with finished := some (.earlyTermination .cancelled) }, mctx.2)
    return mctx'
  else
    return mctx
-/

end Veil.ModelChecker.Concrete
