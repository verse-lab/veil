import Veil.Core.Tools.ModelChecker.ConcreteNew.MapReduceLemmas
import Veil.Core.Tools.ModelChecker.ConcreteNew.Progress
import Veil.Core.Tools.ModelChecker.Concrete.Containers
import Std
namespace Veil.ModelChecker.Concrete
open Std

/-
Parallel BFS using:
- A single `IO.Ref (TreeSet)` for the seen set. `TreeSet` (persistent red-black
  tree) provides O(log n) insert regardless of reference uniqueness, avoiding the
  O(n) array-copy penalty that `HashSet` incurs when its refcount > 1.
  `IO.Ref.modify` gives unique ownership (refcount 1) via `take`, and
  `IO.Ref.get` supports concurrent reads.
- A work queue protected by `Mutex` + `Condvar` for blocking wait/notify
  (Condvar requires Mutex; IO.Ref cannot support Condvar).
- Search results in `IO.Ref (BaseSearchContext)` (no Condvar needed; modify is
  atomic via spinlock).

Workers run a uniform loop:
1. Dequeue a batch of states (blocking, with distributed termination detection)
2. For each state in the batch:
   a. Compute successors and check violations (pure, via BaseSearchContext.processState)
   b. For each successor: atomic check-and-insert via `IO.Ref.modifyGet` on TreeSet
3. Merge local results into shared `IO.Ref` via `modify` (using mergeWithoutDepthChange)
4. Enqueue new states, check cancellation, wake progress task
-/


/-- Mutable state of the work queue, held inside a `Mutex`.
    Includes distributed termination detection:
    when `numWaiting = numWorkers` and the queue is empty, search is done. -/
structure WorkQueueState (σₕ σ : Type) where
  /-- Pending states to explore. Workers pop from the front. -/
  queue : fQueue (QueueItem σₕ σ) := fQueue.empty
  /-- `true` when all workers should stop (search completed or early termination). -/
  finished : Bool := false
  /-- Number of workers currently blocked waiting for work. -/
  numWaiting : Nat := 0


structure ParallelSearchContext (σ κ σₕ : Type)
  [fp : StateFingerprint σ σₕ] [Ord σₕ] [BEq κ] [Hashable κ] where
  /-- Seen set: persistent TreeSet for O(log n) insert regardless of refcount. -/
  seen : IO.Ref (Std.TreeSet σₕ)
  /-- Work queue with termination detection. -/
  workQueue : Std.Mutex (WorkQueueState σₕ σ)
  /-- Condition variable for work queue: workers wait here when idle,
      get notified when new states are enqueued or search finishes. -/
  workAvailable : Std.Condvar
  /-- Search results / metadata. -/
  results : IO.Ref (BaseSearchContext σ κ σₕ)
  /-- Number of worker threads. -/
  numWorkers : Nat
  /-- Progress notification: workers set the flag to `true` and notify after
      each batch or on termination. The progress task waits on this condvar
      instead of using `IO.sleep`, so it can be woken instantly when search ends. -/
  progressLock : Std.Mutex Bool
  progressNotify : Std.Condvar

/-! ## Initialization -/

/-- Create a new `ParallelSearchContext` populated with initial states. -/
def ParallelSearchContext.new {σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [Ord σₕ] [BEq κ] [Hashable κ]
  (initialStates : List σ) (numWorkers : Nat) :
  IO (ParallelSearchContext σ κ σₕ) := do
  let fps := initialStates.map fp.view
  let seen ← IO.mkRef (Std.TreeSet.ofList fps)
  -- Queue: initial states at depth 0
  let initQueue : fQueue (QueueItem σₕ σ) :=
    fQueue.ofList (fps.zipWith (fun fp st => ⟨fp, st, 0⟩) initialStates)
  let workQueue ← Std.Mutex.new { queue := initQueue : WorkQueueState σₕ σ }
  let workAvailable ← Std.Condvar.new
  let results ← IO.mkRef (BaseSearchContext.initial (fp := fp) initialStates : BaseSearchContext σ κ σₕ)
  let progressLock ← Std.Mutex.new false
  let progressNotify ← Std.Condvar.new
  return { seen, workQueue, workAvailable, results, numWorkers, progressLock, progressNotify }

/- Worker operations -/

/-- Result of a dequeue attempt: either items or a signal to retry. -/
inductive DequeueResult (α : Type) where
  | done (result : α)
  | retry

/-- Dequeue up to `batchSize` states from the work queue in a single lock
    acquisition. Blocks until at least one state is available, or distributed
    termination is detected (all workers idle + queue empty).
    Returns an empty list on termination. -/
partial def ParallelSearchContext.dequeueBatch {σ κ σₕ : Type}
    [fp : StateFingerprint σ σₕ] [Ord σₕ] [BEq κ] [Hashable κ]
    (ctx : ParallelSearchContext σ κ σₕ) (batchSize : Nat)
    : IO (List (QueueItem σₕ σ)) := do
  let action : DequeueResult (List (QueueItem σₕ σ)) ← ctx.workQueue.atomically do
    let wqs ← get
    -- Already finished (another worker triggered termination)
    if wqs.finished then return .done []
    if !wqs.queue.isEmpty then
      let (batch, remainingQueue) := wqs.queue.dequeueBatch batchSize
      set { wqs with queue := remainingQueue }
      return .done batch
    -- Queue empty: distributed termination detection
    let newWaiting := wqs.numWaiting + 1
    if newWaiting >= ctx.numWorkers then
      -- All workers idle + queue empty → search is complete
      set { wqs with finished := true, numWaiting := newWaiting }
      ctx.workAvailable.notifyAll
      return .done []
    set { wqs with numWaiting := newWaiting }
    ctx.workAvailable.wait ctx.workQueue.mutex
    modify fun s => { s with numWaiting := s.numWaiting - 1 }
    return .retry
  match action with
  | .done batch => return batch
  | .retry => ctx.dequeueBatch batchSize

/- Enqueue new states into the work queue and notify waiting workers.
    Uses `notifyOne` for single items, `notifyAll` for batches. -/
def ParallelSearchContext.enqueueStates {σ κ σₕ : Type}
    [fp : StateFingerprint σ σₕ] [Ord σₕ] [BEq κ] [Hashable κ]
    (ctx : ParallelSearchContext σ κ σₕ)
    (items : Array (QueueItem σₕ σ)) : IO Unit := do
  if items.isEmpty then return
  ctx.workQueue.atomically do
    modify fun wqs => { wqs with queue := wqs.queue.enqueueBatch items.toList }
  -- Notify after releasing the lock so woken workers can acquire immediately
  if items.size == 1 then ctx.workAvailable.notifyOne
  else ctx.workAvailable.notifyAll

/-- Atomic check-and-insert on the seen set using `IO.Ref.modifyGet`.
    Uses `TreeSet.containsThenInsert` for a single-pass O(log n) operation.
    Returns `true` if the fingerprint was newly inserted. -/
def ParallelSearchContext.tryInsertSeen {σ κ σₕ : Type}
    [fp : StateFingerprint σ σₕ] [Ord σₕ] [BEq κ] [Hashable κ]
    (ctx : ParallelSearchContext σ κ σₕ) (fingerprint : σₕ) : IO Bool :=
  ctx.seen.modifyGet fun set =>
    let (alreadyPresent, newSet) := set.containsThenInsert fingerprint
    (!alreadyPresent, newSet)

/-- Wake the progress task so it can check for updates or exit. -/
@[inline]
def ParallelSearchContext.wakeProgressTask {σ κ σₕ : Type}
    [fp : StateFingerprint σ σₕ] [Ord σₕ] [BEq κ] [Hashable κ]
    (ctx : ParallelSearchContext σ κ σₕ) : IO Unit := do
  ctx.progressLock.atomically fun ref => ref.set true
  ctx.progressNotify.notifyOne

/- Signal early termination: set the finished flag, wake all workers and
   the progress task. -/
def ParallelSearchContext.signalTermination {σ κ σₕ : Type}
    [fp : StateFingerprint σ σₕ] [Ord σₕ] [BEq κ] [Hashable κ]
    (ctx : ParallelSearchContext σ κ σₕ) : IO Unit := do
  ctx.workQueue.atomically do
    modify fun wqs => { wqs with finished := true }
  ctx.workAvailable.notifyAll
  ctx.wakeProgressTask

/-! ## Worker loop -/

section
variable {ρ σ κ σₕ : Type} [fp : StateFingerprint σ σₕ] [Ord σₕ] [BEq κ] [Hashable κ]
  (params : SearchParameters ρ σ) (th : ρ)

omit params th in
/-- IO-adapted version of `MapReduceSearchContextLocal.processSuccessors` from Parallel.lean.
    For each successor, atomically checks the shared seen set and updates
    the local context (log, action stats, queue).
    Mirrors `tryExploreNeighbor` but uses IO for the seen-set check. -/
def processSuccessorsIO
  (pctx : ParallelSearchContext σ κ σₕ)
  (fpSt : σₕ) (depth : Nat)
  (successors : List (κ × σ))
  (lctx : MapReduceSearchContextLocal σ κ σₕ) : IO (MapReduceSearchContextLocal σ κ σₕ) := do
  let nextDepth := depth + 1
  let mut ctx := lctx.1
  let mut q := lctx.2
  for (label, postState) in successors do
    let fingerprint := fp.view postState
    if ctx.log.contains fingerprint then
      -- Already in local log (duplicate within this batch)
      ctx := { ctx with actionStatsMap := ctx.actionStatsMap.update true label }
    else
      let isNew ← pctx.tryInsertSeen fingerprint
      if isNew then
        ctx := { ctx with
          log := ctx.log.insert fingerprint (Option.some (fpSt, label))
          actionStatsMap := ctx.actionStatsMap.update true label }
        q := q.push ⟨fingerprint, postState, nextDepth⟩
      else
        ctx := { ctx with actionStatsMap := ctx.actionStatsMap.update false label }
  return (ctx, q)

/-- IO-adapted version of `MapReduceSearchContextLocal.processWorkQueue` from Parallel.lean.
    Processes a batch of states using `BaseSearchContext.processState` for violation checking
    and `processSuccessorsIO` for IO-based seen-set deduplication. -/
def processWorkQueueIO
  (pctx : ParallelSearchContext σ κ σₕ)
  (outcomesComputer : ρ → σ → List (κ × ExecutionOutcome ℤ σ))
  (batch : List (QueueItem σₕ σ))
  : IO (MapReduceSearchContextLocal σ κ σₕ) := do
  let mut lctx : MapReduceSearchContextLocal σ κ σₕ := MapReduceSearchContextLocal.initial 0
  for item in batch do
    if lctx.1.hasFinished then break else pure ()
    let ⟨fpSt, curr, depth⟩ := item
    -- Set completedDepth to this state's depth for correct depth-bound checking
    -- in BaseSearchContext.processState
    let localBase := { lctx.1 with completedDepth := depth }
    let (ctx', outcomesOpt) := localBase.processState params th fpSt curr (outcomesComputer th curr)
    match outcomesOpt with
    | none => lctx := (ctx', lctx.2)
    | some successfulTransitions =>
      let ctx'' := { ctx' with statesFound := ctx'.statesFound + successfulTransitions.length }
      lctx ← processSuccessorsIO pctx fpSt depth successfulTransitions (ctx'', lctx.2)
  return lctx

end

/-- Worker loop: dequeues batches, processes them locally, merges results,
    and enqueues new states. Runs until termination or cancellation. -/
partial def ParallelSearchContext.workerLoop {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [Ord σₕ] [BEq κ] [Hashable κ]
  (ctx : ParallelSearchContext σ κ σₕ)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (outcomesComputer : ρ → σ → List (κ × ExecutionOutcome ℤ σ))
  (cancelToken : IO.CancelToken)
  (progressInstanceId : Nat)
  (updateTimeInterval : Nat)
  (batchSize : Nat)
  : IO Unit := do
  let mut lastCheckTime : Nat := 0
  while true do
    -- 1. Dequeue a batch (one lock acquisition for up to batchSize items)
    let batch ← ctx.dequeueBatch batchSize
    if batch.isEmpty then
      -- Queue empty + all workers idle → search complete.
      -- Set finished if no early termination was triggered.
      ctx.results.modify fun res =>
        if res.finished.isNone then
          { res with finished := some .exploredAllReachableStates }
        else res
      ctx.wakeProgressTask
      break

    -- 2. Process batch locally (IO-adapted processWorkQueue pattern)
    let lctx ← processWorkQueueIO params th ctx outcomesComputer batch
    let batchMaxDepth := batch.foldl (fun acc item => max acc item.depth) 0

    -- 3. Merge local results into shared state (using mergeWithoutDepthChange)
    ctx.results.modify fun sharedCtx =>
      let merged := sharedCtx.mergeWithoutDepthChange lctx.1
      { merged with
        completedDepth := max sharedCtx.completedDepth batchMaxDepth
        currentFrontierDepth := max sharedCtx.currentFrontierDepth batchMaxDepth }

    -- 4. If early termination triggered, signal all workers and stop
    if lctx.1.hasFinished then
      trySetViolationFound progressInstanceId lctx.1
      ctx.signalTermination
      break

    -- 5. Time-throttled cancellation check
    match ← checkCancellationWithoutPeriodicUpdate progressInstanceId lastCheckTime updateTimeInterval cancelToken with
    | .searchCancelled =>
      ctx.results.modify fun res =>
        { res with finished := some (.earlyTermination .cancelled) }
      ctx.signalTermination
      break
    | .updateTime t => lastCheckTime := t
    | .noUpdate => pure ()

    -- 6. Enqueue all new items from entire batch (one lock acquisition)
    ctx.enqueueStates lctx.2

    -- 7. Notify progress task that new results are available
    ctx.wakeProgressTask


/-- Parallel BFS using:
- `IO.Ref (TreeSet)` for the seen set (O(log n) insert, no array copying)
- `Mutex` + `Condvar` for the work queue (blocking dequeue)
- `IO.Ref (BaseSearchContext)` for search results (atomic modify via spinlock) -/
def breadthFirstSearchParallel2 {ρ σ κ σₕ : Type}
    [fp : StateFingerprint σ σₕ] [Ord σₕ] [BEq κ] [Hashable κ] [Repr κ]
    {th : ρ}
    (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ
      (List (κ × ExecutionOutcome Int σ)) th)
    (params : SearchParameters ρ σ)
    (numWorkers : Nat := 4)
    (updateTimeInterval : Nat := 1000)
    (batchSize : Nat := 1024)
    (progressInstanceId : Nat)
    (cancelToken : IO.CancelToken)
    : IO (BaseSearchContext σ κ σₕ) := do
  let nWorkers := max numWorkers 1
  -- Create parallel BFS context with initial states
  let ctx ← ParallelSearchContext.new sys.initStates nWorkers

  -- Spawn worker threads on dedicated OS threads.
  -- IMPORTANT: Workers block on `Condvar.wait`, which consumes OS threads.
  -- Using `.default` priority (thread pool) would cause deadlock when
  -- numWorkers > pool size, because blocked workers consume all pool threads
  -- and remaining workers/progress task never get scheduled.
  let tasks ← (List.range nWorkers).mapM fun _ =>
    IO.asTask (prio := .dedicated) do
      ctx.workerLoop params th sys.tr cancelToken progressInstanceId
        updateTimeInterval batchSize

  -- Progress task: waits on condvar (woken by workers after each batch or
  -- on termination), so it exits instantly when search ends instead of
  -- sleeping for up to `updateTimeInterval` ms.
  let progressTask ← IO.asTask (prio := .dedicated) do
    let mut lastUpdateTime : Nat := 0
    while true do
      -- Wait until a worker signals (batch done or termination)
      ctx.progressLock.atomically fun ref => do
        if !(← ref.get) then
          ctx.progressNotify.wait ctx.progressLock.mutex
        ref.set false  -- reset flag for next round
      -- Check if search is finished
      let finished ← ctx.workQueue.atomically fun ref =>
        return (← ref.get).finished
      -- Throttled progress update
      let now ← IO.monoMsNow
      if now - lastUpdateTime ≥ updateTimeInterval then
        let res ← ctx.results.get
        let seenSize := (← ctx.seen.get).size
        let queueSize ← ctx.workQueue.atomically fun ref =>
          return (← ref.get).queue.size
        updateProgress progressInstanceId
          res.completedDepth res.statesFound seenSize queueSize
          (toActionStatsList res.actionStatsMap)
        lastUpdateTime := now
      if finished then break

  -- Wait for all workers to complete
  for task in tasks do
    match ← IO.wait task with
    | .ok () => pure ()
    | .error e => throw e

  -- Cancel progress polling (workers are done, so finished flag is set)
  let _ ← IO.wait progressTask

  -- Final progress update
  let result ← ctx.results.get
  updateProgress progressInstanceId
    result.completedDepth result.statesFound (← ctx.seen.get).size 0
    (toActionStatsList result.actionStatsMap)
  return result

end Veil.ModelChecker.Concrete
