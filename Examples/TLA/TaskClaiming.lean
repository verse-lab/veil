module

public import Veil

/-!
Upstream license: Apache-2.0; see Benchmarks/TLA/TaskClaiming/LICENSE.
Copyright 2026 StreamNative, Inc.
Modified locally: translated and adapted to Veil.

Safety translation of Ursa's coordination-delegated task claiming protocol.
Source:
https://github.com/openlakestream/leaderless-log-protocol/blob/df7a398718dc3b6f726514ba4b99b0e5ae6aa521/tlaplus/TaskClaiming.tla
Workers/tasks map to their respective Fin domains; the string NONE maps to none.
Lock versions and failure counts remain Nat. The unused PREPARED status remains
in the enum. Fairness, TaskCompletion, CrashRecovery and NoStarvation are omitted
from this safety check. LockVersionBound is a state constraint, not an action guard.
-/

veil module TaskClaiming

type worker
type task
param maxFailures : Nat
param maxLockVersion : Nat

enum TaskStatus = {tsInit, tsPrepared, tsCommitted, tsDLQ}
enum WorkerState = {wsIdle, wsScanning, wsExecuting, wsUnlocking}

@[veil_decl]
structure Lock (worker : Type) where
  worker : Option worker
  version : Nat

function taskStatus : task → TaskStatus
function lockState : task → Lock worker
relation workerAlive : worker → Bool
function workerState : worker → WorkerState
function workerTask : worker → Option task
function taskFailCount : task → Nat
individual lockVersion : Nat

set_option veil.deferVCGeneration true

veil_set_field_representation relation Veil.ArrayAsFinset
veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

assumption [positive_failure_limit] maxFailures ≥ 1

ghost relation IsLocked (t : task) := (lockState t).worker.isSome
ghost relation IsLockedBy (t : task) (w : worker) := (lockState t).worker = some w

after_init {
  taskStatus T := tsInit
  lockState T := { worker := none, version := 0 }
  workerAlive WW := true
  workerState WW := wsIdle
  workerTask WW := none
  taskFailCount T := 0
  lockVersion := 1
}

-- ScanTasks(w,t): choose any INIT task while alive and idle.
action ScanTasks (w : worker) (t : task) {
  require workerAlive w
  require workerState w = wsIdle
  require taskStatus t = tsInit
  workerState w := wsScanning
  workerTask w := some t
}

-- The task parameter exposes the source's workerTask[w] lookup. SCANNING,
-- EXECUTING and UNLOCKING always have a task on reachable states.
action TryLockSuccess (w : worker) (t : task) {
  require workerAlive w
  require workerState w = wsScanning
  require workerTask w = some t
  require ¬ IsLocked t
  require taskStatus t = tsInit
  lockState t := { worker := some w, version := lockVersion }
  lockVersion := lockVersion + 1
  workerState w := wsExecuting
}

action TryLockFail (w : worker) (t : task) {
  require workerAlive w
  require workerState w = wsScanning
  require workerTask w = some t
  require (IsLocked t ∧ ¬ IsLockedBy t w) ∨ taskStatus t ≠ tsInit
  workerState w := wsIdle
  workerTask w := none
}

action ExecuteTaskSuccess (w : worker) (t : task) {
  require workerAlive w
  require workerState w = wsExecuting
  require workerTask w = some t
  require taskStatus t = tsInit
  taskStatus t := tsCommitted
  workerState w := wsUnlocking
}

-- The status decision reads the incremented failure count (old count + 1).
action ExecuteTaskFailure (w : worker) (t : task) {
  require workerAlive w
  require workerState w = wsExecuting
  require workerTask w = some t
  taskFailCount t := taskFailCount t + 1
  if taskFailCount t ≥ maxFailures then
    taskStatus t := tsDLQ
  workerState w := wsUnlocking
}

action UnlockTask (w : worker) (t : task) {
  require workerAlive w
  require workerState w = wsUnlocking
  require workerTask w = some t
  if IsLockedBy t w then
    lockState t := { worker := none, version := 0 }
  workerState w := wsIdle
  workerTask w := none
}

-- Crash retains lock, worker state, and task until SessionExpiry/WorkerRecover.
action WorkerCrash (w : worker) {
  require workerAlive w
  workerAlive w := false
}

action SessionExpiry (w : worker) {
  require ¬ workerAlive w
  require ∃ t : task, IsLockedBy t w
  lockState T := if IsLockedBy T w then { worker := none, version := 0 } else lockState T
  workerState w := wsIdle
  workerTask w := none
}

action WorkerRecover (w : worker) {
  require ¬ workerAlive w
  require ∀ t : task, ¬ IsLockedBy t w
  workerAlive w := true
  workerState w := wsIdle
  workerTask w := none
}

-- Preserve TypeOK's semantic bounds; types encode its remaining conjuncts.
invariant [TypeOK]
  (∀ t : task, taskFailCount t ≤ maxFailures) ∧ lockVersion ≥ 1

-- Cardinality <= 1, including dead workers whose EXECUTING state is retained.
invariant [MutualExclusion]
  ∀ t : task, ∀ w1 w2 : worker,
    workerState w1 = wsExecuting ∧ workerTask w1 = some t ∧
      workerState w2 = wsExecuting ∧ workerTask w2 = some t → w1 = w2

invariant [NoDoubleExecution]
  ∀ t : task, taskStatus t = tsCommitted →
    ¬ ∃ w : worker, workerState w = wsExecuting ∧ workerTask w = some t

invariant [DLQOnlyAfterMaxFailures]
  ∀ t : task, taskStatus t = tsDLQ → taskFailCount t ≥ maxFailures

invariant [LockConsistency]
  ∀ t : task, ∀ w : worker,
    IsLockedBy t w ∧ workerAlive w → workerTask w = some t

invariant [NoOrphanExecution]
  ∀ t : task, ∀ w : worker, IsLockedBy t w ∧ ¬ workerAlive w →
    ¬ ∃ w2 : worker, w2 ≠ w ∧ workerState w2 = wsExecuting ∧ workerTask w2 = some t

state_constraint [LockVersionBound] lockVersion ≤ maxLockVersion

#gen_spec
#gen_executable

-- The check below uses the instance of the TLC model
-- `Benchmarks/TLA/TaskClaiming/TaskClaiming.cfg`. It is commented out; uncomment it to run it.
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s:
-- * `worker := Fin 3`: the workers are `0`, `1`, `2` (cfg: `Workers = {w1, w2, w3}`).
-- * `task := Fin 3`: the tasks are `0`, `1`, `2` (cfg: `Tasks = {t1, t2, t3}`).
-- * `maxFailures := 3`: a task goes to the dead-letter queue (DLQ) after 3 failures
--   (cfg: `MaxFailures = 3`).
-- * `maxLockVersion := 10`: the state constraint bounds `lockVersion` by 10
--   (cfg: `MaxLockVersion = 10`).
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields. There are none,
-- hence `{}`.
--
-- Before searching, `#model_check` checks `maxFailures` against the `assumption` above, which is
-- the spec's `ASSUME MaxFailures >= 1`.
--
-- The other settings of the cfg:
-- * `CONSTRAINT LockVersionBound`: the `state_constraint [LockVersionBound]` above. Unlike TLC,
--   Veil does not check the invariants in the states that the constraint drops.
-- * `INVARIANTS TypeOK MutualExclusion ... NoOrphanExecution`: `#model_check` checks every
--   `invariant` of the module, which here has the same six names. The `TypeOK` here keeps the
--   numeric bounds of the spec's `TypeOK`; Lean's types ensure the rest.
-- * `CHECK_DEADLOCK FALSE`: this module has no `termination` clause, so Veil reports no
--   deadlocks either.
-- Options:
-- * `compiled` runs the search only in a compiled checker, not in Lean's interpreter.
-- * `(seenSet := HAMTMapShard)`: the sharded map of visited states uses `HAMTMapShard`.
/- EVAL
#model_check compiled
  { worker := Fin 3, task := Fin 3, maxFailures := 3, maxLockVersion := 10 } {}
  (seenSet := HAMTMapShard)
-/

-- Boundary: first failure sends a task to DLQ; retain both workers and tasks.
-- #model_check { worker := Fin 2, task := Fin 2, maxFailures := 1, maxLockVersion := 3 } {}

end TaskClaiming
