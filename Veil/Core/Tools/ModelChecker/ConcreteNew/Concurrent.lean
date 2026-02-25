import Veil.Core.Tools.ModelChecker.ConcreteNew.Core
import Veil.Core.Tools.ModelChecker.ConcreteNew.Progress
import Std
namespace Veil.ModelChecker.Concrete
open Std

/-
- A `striped seen set`: multiple `SharedMutex` shards (like TLC's `MemFPSet`),
  indexed by fingerprint hash. Reduces lock contention by a factor of `numStripes`.
- A single work queue protected by `Mutex` + `Condvar` for wait/notify
- Shared search results protected by `Mutex`

Workers run a uniform loop:
1. Dequeue a state (blocking, with distributed termination detection)
2. Compute successors (pure, no lock needed)
3. For each successor:
   a. Determine stripe from fingerprint hash
   b. Read-lock that stripe → check if fingerprint exists
   c. If not found: write-lock that stripe → double-check & insert (TLC put pattern)
   d. Enqueue new state, update log/stats
4. Check violations, possibly signal early termination
-/


/-- Mutable state of the work queue, held inside a `Mutex`.
    Includes TLC-style distributed termination detection:
    when `numWaiting = numWorkers` and the queue is empty, search is done. -/
structure WorkQueueState (σₕ σ : Type) where
  /-- Pending states to explore. Workers pop from the back (LIFO / stack order). -/
  queue : Array (QueueItem σₕ σ) := #[]
  /-- `true` when all workers should stop (search completed or early termination). -/
  finished : Bool := false
  /-- Number of workers currently blocked waiting for work. -/
  numWaiting : Nat := 0


/-- Striped seen set: multiple independent `SharedMutex` shards, indexed by fingerprint hash.
    Like TLC's `MemFPSet` with `2^(log2(workers)+8)` striped `ReadWriteLock`s,
    this distributes lock contention across `N` stripes so workers rarely block each other. -/
structure StripedSeenSet (σₕ : Type) [BEq σₕ] [Hashable σₕ] where
  stripes : Array (Std.SharedMutex (Std.HashSet σₕ))
  h_pos : 0 < stripes.size

namespace StripedSeenSet

variable {σₕ : Type} [BEq σₕ] [Hashable σₕ]

/-- Create a new striped seen set, distributing initial fingerprints across stripes. -/
def new (initialFps : List σₕ) (numStripes : Nat := 256)
    : IO (StripedSeenSet σₕ) := do
  let n := max numStripes 1
  -- Build per-stripe initial HashSets
  let mut initSets := Array.replicate n ({} : Std.HashSet σₕ)
  for fp in initialFps do
    initSets := initSets.modify ((hash fp).toNat % n) (·.insert fp)
  -- Create a SharedMutex for each stripe
  let stripes ← initSets.mapM (SharedMutex.new ·)
  if h : 0 < stripes.size then
    return ⟨stripes, h⟩
  else
    -- Unreachable: mapM preserves array size and n ≥ 1
    throw <| IO.userError "StripedSeenSet: unexpected empty stripes"

/-- Get the `SharedMutex` stripe responsible for a fingerprint. -/
@[inline]
def getStripe (s : StripedSeenSet σₕ) (fingerprint : σₕ)
    : Std.SharedMutex (Std.HashSet σₕ) :=
  s.stripes[(hash fingerprint).toNat % s.stripes.size]'(Nat.mod_lt _ s.h_pos)

/-- TLC-style "put": read-lock check, then write-lock double-check and insert.
    Returns `true` if the fingerprint was newly inserted. -/
def tryInsert (s : StripedSeenSet σₕ) (fingerprint : σₕ) : IO Bool := do
  let stripe := s.getStripe fingerprint
  -- Phase 1: read-lock fast path
  let alreadySeen ← stripe.atomicallyRead fun set => pure (set.contains fingerprint)
  if alreadySeen then return false
  -- Phase 2: write-lock double-check and insert
  stripe.atomically fun ref => do
    let set ← ref.get
    if set.contains fingerprint then return false
    ref.set (set.insert fingerprint)
    return true

/-- Sum sizes across all stripes (approximate, for progress reporting). -/
def totalSize (s : StripedSeenSet σₕ) : IO Nat := do
  let mut total := 0
  for stripe in s.stripes do
    total := total + (← stripe.atomicallyRead fun set => pure set.size)
  return total

/-- Merge all stripes into a single `HashSet` (for final result extraction). -/
def mergeAll (s : StripedSeenSet σₕ) : IO (Std.HashSet σₕ) := do
  let mut result : Std.HashSet σₕ := {}
  for stripe in s.stripes do
    let set' ← stripe.atomicallyRead fun set => pure set
    result := set'.fold (fun acc x => acc.insert x) result
    -- result := result.union set'
  return result

end StripedSeenSet

/-- Search metadata accumulated during parallel BFS.
    Held inside a separate `Mutex` to reduce contention with the hot-path
    `seen` set and the work queue. -/
structure SearchResultState (σ κ σₕ : Type) [BEq σₕ] [Hashable σₕ] [BEq κ] [Hashable κ] where
  /-- Transition log: post-state fingerprint → (pre-state fingerprint, action label).
      Used for counterexample trace reconstruction. -/
  log : Std.HashMap σₕ (Option (σₕ × κ))
  /-- Collected invariant/safety violations. -/
  violatingStates : List (σₕ × ViolationKind) := []
  /-- Reason for search termination, if any. -/
  terminationReason : Option (TerminationReason σₕ) := none
  /-- Total successor states generated (before dedup). -/
  statesFound : Nat := 0
  /-- Per-action statistics. -/
  actionStatsMap : Std.HashMap κ ActionStat := {}
  /-- Maximum depth of any state processed so far (= diameter for progress). -/
  maxDepthProcessed : Nat := 0

structure ParallelSearchContext (σ κ σₕ : Type)
  [BEq σₕ] [Hashable σₕ] [BEq κ] [Hashable κ] where
  /-- Striped seen set: fingerprint hash determines which shard to lock. -/
  seen : StripedSeenSet σₕ
  /-- Work queue with termination detection. -/
  workQueue : Std.Mutex (WorkQueueState σₕ σ)
  /-- Condition variable for work queue: workers wait here when idle,
      get notified when new states are enqueued or search finishes. -/
  workAvailable : Std.Condvar
  /-- Search results / metadata. -/
  results : Std.Mutex (SearchResultState σ κ σₕ)
  /-- Number of worker threads. -/
  numWorkers : Nat
  /-- Progress notification: workers set the flag to `true` and notify after
      each batch or on termination. The progress task waits on this condvar
      instead of using `IO.sleep`, so it can be woken instantly when search ends. -/
  progressLock : Std.Mutex Bool
  progressNotify : Std.Condvar

/-! ## Initialization -/

-- variable {σ κ σₕ : Type} [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ]

/-- Create a new `ParallelSearchContext` populated with initial states. -/
def ParallelSearchContext.new {σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ]
  (initialStates : List σ) (numWorkers : Nat) :
  IO (ParallelSearchContext σ κ σₕ) := do
  -- Striped seen set with initial fingerprints distributed across shards
  let fps := initialStates.map fp.view
  let seen ← StripedSeenSet.new fps
  -- Queue: initial states at depth 0
  let initQueue := initialStates.foldl (fun acc s =>
    acc.push ⟨fp.view s, s, 0⟩) #[]
  let workQueue ← Mutex.new { queue := initQueue : WorkQueueState σₕ σ }
  let workAvailable ← Condvar.new
  let results ← Mutex.new {
    log := Std.HashMap.ofList (fps.map fun fp => (fp, none))  -- initial states have no predecessor
    statesFound := initialStates.length : SearchResultState σ κ σₕ }
  let progressLock ← Mutex.new false
  let progressNotify ← Condvar.new
  return { seen, workQueue, workAvailable, results, numWorkers, progressLock, progressNotify }

/-! ## Result extraction -/

/-- Extract accumulated results into a `BaseSearchContext` (for compatibility
    with the rest of the model checker pipeline). -/
def ParallelSearchContext.toBaseSearchContext {σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ]
  (ctx : ParallelSearchContext σ κ σₕ) :
  IO (BaseSearchContext σ κ σₕ) := do
  let res ← ctx.results.atomically fun ref => ref.get
  return {
    log := res.log
    violatingStates := res.violatingStates
    finished := res.terminationReason
    completedDepth := res.maxDepthProcessed
    currentFrontierDepth := res.maxDepthProcessed
    statesFound := res.statesFound
    actionStatsMap := res.actionStatsMap
  }

/- Worker operations -/

/-- Result of a dequeue attempt: either items or a signal to retry. -/
inductive DequeueResult (α : Type) where
  | done (result : α)
  | retry

/-- Dequeue up to `batchSize` states from the work queue in a single lock
    acquisition. Blocks until at least one state is available, or distributed
    termination is detected (all workers idle + queue empty).
    Returns an empty array on termination. -/
partial def ParallelSearchContext.dequeueBatch {σ κ σₕ : Type}
    [BEq σₕ] [Hashable σₕ] [BEq κ] [Hashable κ]
    (ctx : ParallelSearchContext σ κ σₕ) (batchSize : Nat)
    : IO (Array (QueueItem σₕ σ)) := do
  let action : DequeueResult (Array (QueueItem σₕ σ)) ← ctx.workQueue.atomically do
    let wqs ← get
    -- Already finished (another worker triggered termination)
    if wqs.finished then return .done #[]
    if !wqs.queue.isEmpty then
      let queueSize := wqs.queue.size
      let n := min batchSize queueSize
      let batch := wqs.queue.extract 0 n
      set { wqs with queue := wqs.queue.extract n queueSize }
      return .done batch
    -- Queue empty: distributed termination detection
    let newWaiting := wqs.numWaiting + 1
    if newWaiting >= ctx.numWorkers then
      -- All workers idle + queue empty → search is complete
      set { wqs with finished := true, numWaiting := newWaiting }
      ctx.workAvailable.notifyAll
      return .done #[]
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
    [BEq σₕ] [Hashable σₕ] [BEq κ] [Hashable κ]
    (ctx : ParallelSearchContext σ κ σₕ)
    (items : Array (QueueItem σₕ σ)) : IO Unit := do
  if items.isEmpty then return
  ctx.workQueue.atomically do
    modify fun wqs => { wqs with queue := wqs.queue ++ items }
  -- Notify after releasing the lock so woken workers can acquire immediately
  if items.size == 1 then ctx.workAvailable.notifyOne
  else ctx.workAvailable.notifyAll

/- TLC-style "put" on the striped seen set.
  Returns `true` if the fingerprint was newly inserted. -/
def ParallelSearchContext.tryInsertSeen {σ κ σₕ : Type}
    [BEq σₕ] [Hashable σₕ] [BEq κ] [Hashable κ]
    (ctx : ParallelSearchContext σ κ σₕ) (fingerprint : σₕ) : IO Bool :=
  ctx.seen.tryInsert fingerprint

/- Batch seen-set check and insert using striped locks.
  Each successor's fingerprint is checked/inserted on its own stripe,
  so different fingerprints rarely contend with each other.
  Returns the array of newly inserted (label, postState, fingerprint) tuples. -/
def ParallelSearchContext.batchInsertSeen {σ κ σₕ : Type}
    [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ]
    (ctx : ParallelSearchContext σ κ σₕ)
    (successors : List (κ × σ))
    : IO (Array (κ × σ × σₕ)) := do
  if successors.isEmpty then return #[]
  let mut result : Array (κ × σ × σₕ) := #[]
  for (label, postState) in successors do
    let fingerprint := fp.view postState
    let isNew ← ctx.seen.tryInsert fingerprint
    if isNew then
      result := result.push (label, postState, fingerprint)
  return result

/-- Wake the progress task so it can check for updates or exit. -/
@[inline]
def ParallelSearchContext.wakeProgressTask {σ κ σₕ : Type}
    [BEq σₕ] [Hashable σₕ] [BEq κ] [Hashable κ]
    (ctx : ParallelSearchContext σ κ σₕ) : IO Unit := do
  ctx.progressLock.atomically fun ref => ref.set true
  ctx.progressNotify.notifyOne

/- Signal early termination: set the finished flag, wake all workers and
   the progress task. -/
def ParallelSearchContext.signalTermination {σ κ σₕ : Type}
    [BEq σₕ] [Hashable σₕ] [BEq κ] [Hashable κ]
    (ctx : ParallelSearchContext σ κ σₕ) : IO Unit := do
  ctx.workQueue.atomically do
    modify fun wqs => { wqs with finished := true }
  ctx.workAvailable.notifyAll
  ctx.wakeProgressTask

/- Update action stats map (same as sequential version). -/
-- @[inline]
private def updateActionStatsMapP {κ : Type} [BEq κ] [Hashable κ]
    (distinct? : Bool) (label : κ)
    (amap : Std.HashMap κ ActionStat) : Std.HashMap κ ActionStat :=
  if distinct? then
    amap.alter label fun
      | some ⟨as, ds⟩ => Option.some ⟨as + 1, ds + 1⟩
      | none => Option.some { statesGenerated := 1, distinctStates := 1 }
  else
    amap.alter label fun
      | some ⟨as, ds⟩ => Option.some ⟨as + 1, ds⟩
      | none => Option.some { statesGenerated := 1, distinctStates := 0 }

/-! ## Worker loop -/

/-- Process a single state from the batch:
- compute successors,
- check violations,
- insert new fingerprints, and
- accumulate results locally.
Return:
  `(newItems, localLog, localActionStats, totalStatesFound, newViolations, earlyTermination)`.
All shared-state mutations are deferred to the caller. -/
@[inline]
private def processOneState {ρ σ κ σₕ : Type}
    [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ]
    (ctx : ParallelSearchContext σ κ σₕ)
    (params : SearchParameters ρ σ)
    (th : ρ)
    (outcomesComputer : ρ → σ → List (κ × ExecutionOutcome ℤ σ))
    (fpSt : σₕ) (curr : σ) (depth : Nat)
    -- Accumulators (passed in, returned modified)
    (newItems : Array (QueueItem σₕ σ))
    (localLog : Std.HashMap σₕ (σₕ × κ))
    (localActionStats : Std.HashMap κ ActionStat)
    (totalStatesFound : Nat)
    (allViolations : List (σₕ × ViolationKind))
    : IO (Array (QueueItem σₕ σ) × Std.HashMap σₕ (σₕ × κ) × Std.HashMap κ ActionStat
          × Nat × List (σₕ × ViolationKind) × Option (EarlyTerminationReason σₕ)) := do
  -- 1. Compute transitions (pure, no lock needed)
  let outcomes := outcomesComputer th curr
  let (successfulTransitions, assertionFailures) := partitionExecutionOutcome outcomes
  let hasSuccessfulTransition := !successfulTransitions.isEmpty

  -- 2. Check violations (pure)
  let (newViolations, earlyTermination) :=
    checkViolationsAndMaybeTerminate params th fpSt curr
      depth hasSuccessfulTransition assertionFailures

  -- 3. Seen-set insert (per-element, distributed across stripes → low contention)
  let newStates ← ctx.batchInsertSeen successfulTransitions

  -- 4. Build queue items, log entries, action stats locally
  let newFps := newStates.foldl (fun (s : Std.HashSet σₕ) (_, _, f) => s.insert f) {}
  let mut newItems := newItems
  let mut localLog := localLog
  let mut localActionStats := localActionStats
  for (label, postState) in successfulTransitions do
    let fingerprint := fp.view postState
    if newFps.contains fingerprint then
      if !localLog.contains fingerprint then
        newItems := newItems.push ⟨fingerprint, postState, depth + 1⟩
        localLog := localLog.insert fingerprint (fpSt, label)
      localActionStats := updateActionStatsMapP true label localActionStats
    else
      localActionStats := updateActionStatsMapP false label localActionStats

  return (newItems, localLog, localActionStats,
          totalStatesFound + successfulTransitions.length,
          newViolations ++ allViolations, earlyTermination)

/-- A single worker thread's main loop.
    Dequeues a _batch_ of states, processes them locally with no shared-state
    locks (except per-element stripe locks on the seen set), then performs
    exactly _one_ results merge + _one_ queue enqueue per batch.
    This reduces queue/results lock contention by a factor of `batchSize`. -/
partial def ParallelSearchContext.workerLoop {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ]
  (ctx : ParallelSearchContext σ κ σₕ)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (outcomesComputer : ρ → σ → List (κ × ExecutionOutcome ℤ σ))
  (cancelToken : IO.CancelToken)
  (progressInstanceId : Nat)
  (updateTimeInterval : Nat)
  (batchSize : Nat)
  (lastCheckTime : Nat := 0)
  : IO Unit := do
  -- 1. Dequeue a batch (one lock acquisition for up to batchSize items)
  let batch ← ctx.dequeueBatch batchSize
  if batch.isEmpty then
    -- Queue empty + all workers idle → search complete.
    -- Set terminationReason if no early termination was triggered.
    ctx.results.atomically fun ref => do
      let res ← ref.get
      if res.terminationReason.isNone then
        ref.set { res with terminationReason := some .exploredAllReachableStates }
    ctx.wakeProgressTask
    return

  -- 2. Process batch locally: accumulate new items, log, stats, violations
  let mut newItems : Array (QueueItem σₕ σ) := #[]
  let mut localLog : Std.HashMap σₕ (σₕ × κ) := {}
  let mut localActionStats : Std.HashMap κ ActionStat := {}
  let mut totalStatesFound : Nat := 0
  let mut allViolations : List (σₕ × ViolationKind) := []
  let mut earlyTerminationReason : Option (EarlyTerminationReason σₕ) := none
  let mut batchMaxDepth : Nat := 0

  -- Local search and manipulation
  for ⟨fpSt, curr, depth⟩ in batch do
    batchMaxDepth := max batchMaxDepth depth
    let (ni, ll, las, tsf, av, et) ←
      processOneState ctx params th outcomesComputer fpSt curr depth
        newItems localLog localActionStats totalStatesFound allViolations
    newItems := ni
    localLog := ll
    localActionStats := las
    totalStatesFound := tsf
    allViolations := av
    -- If a violation triggers early termination, stop processing this batch
    if et.isSome then
      earlyTerminationReason := et
      break

  -- 3. Write local search results into shared state (one lock acquisition)
  ctx.results.atomically fun ref => do
    let res ← ref.get
    let mergedLog := localLog.fold (fun m k v => m.insert k v) res.log
    let mergedStats := localActionStats.fold (fun m label stat =>
      m.alter label fun
        | some ⟨g, d⟩ => some ⟨g + stat.statesGenerated, d + stat.distinctStates⟩
        | none => some stat) res.actionStatsMap
    let newTermReason := match earlyTerminationReason with
      | some reason => some (.earlyTermination reason)
      | none => res.terminationReason
    ref.set { res with
      statesFound := res.statesFound + totalStatesFound
      violatingStates := allViolations ++ res.violatingStates
      log := mergedLog
      actionStatsMap := mergedStats
      terminationReason := newTermReason
      maxDepthProcessed := max res.maxDepthProcessed batchMaxDepth
    }

  -- 4. If early termination triggered, signal all workers and stop
  if earlyTerminationReason.isSome then
    if !allViolations.isEmpty then setViolationFound progressInstanceId
    ctx.signalTermination
    return

  -- 5. Time-throttled cancellation check
  let now ← IO.monoMsNow
  let newLastCheckTime ←
    if now - lastCheckTime ≥ updateTimeInterval then do
      if ← shouldStop cancelToken progressInstanceId then
        ctx.results.atomically fun ref => do
          let res ← ref.get
          ref.set { res with terminationReason := some (.earlyTermination .cancelled) }
        ctx.signalTermination
        return
      pure now
    else
      pure lastCheckTime

  -- 6. Enqueue all new items from entire batch (one lock acquisition)
  ctx.enqueueStates newItems

  -- 7. Notify progress task that new results are available
  ctx.wakeProgressTask

  ctx.workerLoop params th outcomesComputer cancelToken progressInstanceId
    updateTimeInterval batchSize newLastCheckTime


/-- Uses TLC-style shared-memory architecture:
- `StripedSeenSet` (256 `SharedMutex` shards) for the seen set
- `Mutex` + `Condvar` for the work queue
- `Mutex` for search results -/
def breadthFirstSearchParallel {ρ σ κ σₕ : Type}
    [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] [Repr κ]
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
        let res ← ctx.results.atomically fun ref => ref.get
        let seenSize ← StripedSeenSet.totalSize ctx.seen
        let queueSize ← ctx.workQueue.atomically fun ref =>
          return (← ref.get).queue.size
        updateProgress progressInstanceId
          res.maxDepthProcessed res.statesFound seenSize queueSize
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
  let result ← ctx.toBaseSearchContext
  updateProgress progressInstanceId
    result.completedDepth result.statesFound result.log.size 0
    (toActionStatsList result.actionStatsMap)
  return result

end Veil.ModelChecker.Concrete
