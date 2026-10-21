module
meta import VeilTest.Regression.VerifierObserverSupport

open Lean Elab Command Veil Veil.Verifier VeilTest.VerifierObserver
meta section

private def check (failures : IO.Ref (Array String)) (b : Bool) (message : String) : IO Unit := do
  unless b do failures.modify (·.push message)

private def observe (name : Name) : CommandElabM (Array (Language.SnapshotTask Language.SnapshotTree)) := do
  let before := (← get).snapshotTasks
  modify fun st => { st with snapshotTasks := #[] }
  try
    let _ ← waitFilteredSync (matching name)
    return (← get).snapshotTasks
  finally
    modify fun st => { st with snapshotTasks := before }

private def run : CommandElabM Unit := do
  runManager
  let owner ← getVCManagerOwner
  let vcManager := owner.manager
  let managerLoopErrors := owner.errors
  let savedManager ← vcManager.atomically fun ref => ref.get
  let savedSnapshots := (← get).snapshotTasks
  let savedErrors ← managerLoopErrors.get
  let nested ← IO.Promise.new (α := Language.SnapshotTree)
  let cleanupObserver ← IO.mkRef (none : Option (Language.SnapshotTask Language.SnapshotTree))
  try
    let failures ← IO.mkRef #[]
    let mgr ← VCManager.new vcManagerCh
    let nestedToken ← IO.CancelToken.new
    -- Retain owner until all assertions. Child exists but does not finish until
    -- after cancelRec; that exercises recursive cancellation of future snapshots.
    let grandchildToken ← IO.CancelToken.new
    let rootA ← tree "A" #[{ stx? := none, cancelTk? := nestedToken, task := nested.resultD default }]
    let a ← worker mgr 0 0 `A (.pure rootA)
    let b ← worker mgr 1 0 `B (.pure (← tree "B"))
    let (mgr, _) := mgr.addVC (← data `A) {} #[a]
    let (mgr, _) := mgr.addVC (← data `B) {} #[b]
    let mgr ← mgr.recordDischargerResult a.id (.unknown none 0)
    let mgr ← mgr.recordDischargerResult b.id (.unknown none 0)
    vcManager.atomically fun ref => ref.set mgr
    let firstA ← observe `A
    let firstB ← observe `B
    let secondA ← observe `A
    check failures (firstA.size == 1) "filter A registered another filter's work"
    check failures (firstB.size == 1) "filter B lost its registration to observer A"
    check failures (secondA.size == 1) "second observer of A lost its registration"
    for snapshots in #[firstA, firstB, secondA] do
      if let some snap := snapshots[0]? then
        let some result ← awaitTask "registered snapshot" snap.task | throwError "snapshot did not finish"
        check failures ((result.element.traces.tid == 41 && result.element.traces.traces.size == 1)) "snapshot profiling traces lost"
        check failures (result.element.diagnostics.msgLog.toArray.size == 1) "snapshot diagnostics lost"
    -- Exercise real Lean cancellation, with an unfinished child and a grandchild
    -- revealed only once the child's promise resolves.
    firstA.forM (·.cancelRec)
    check failures (!(← a.cancelTk.isSet)) "observer cancellation set A worker token"
    check failures (!(← b.cancelTk.isSet)) "observer cancellation set unrelated B worker token"
    check failures (!(← nestedToken.isSet)) "observer cancellation set nested worker token"
    nested.resolve (← tree "nested" #[{ stx? := none, cancelTk? := grandchildToken, task := .pure (← tree "grandchild") }])
    -- cancelRec also on the now-finished projection gives a deterministic barrier
    -- for inspecting every descendant, with no reliance on callback scheduling.
    if let some snap := secondA[0]? then
      let root := snap.task.get
      let child := root.children[0]!
      let some childTree ← awaitTask "nested snapshot" child.task | throwError "nested snapshot missing"
      let grandchild := childTree.children[0]!
      let some grandTree ← awaitTask "grandchild snapshot" grandchild.task | throwError "grandchild snapshot missing"
      check failures (childTree.element.desc == "nested" && grandTree.element.desc == "grandchild")
        "nested snapshot contents lost"
      check failures (childTree.element.diagnostics.msgLog.toArray.size == 1 &&
        grandTree.element.diagnostics.msgLog.toArray.size == 1 &&
        (childTree.element.traces.tid == 41 && childTree.element.traces.traces.size == 1) && (grandTree.element.traces.tid == 41 && grandTree.element.traces.traces.size == 1))
        "nested diagnostics or profiling lost"
      check failures (child.cancelTk?.isNone && grandchild.cancelTk?.isNone)
        "nested snapshot retained cancellation tokens"
      child.cancelRec
    check failures (!(← nestedToken.isSet)) "late child retained cancellation ownership"
    check failures (!(← grandchildToken.isSet)) "late grandchild retained cancellation ownership"

    -- Successful asynchronous waits must carry the same diagnostic and
    -- profiling trees as synchronous waits, independently of earlier observers.
    let successfulCalls ← IO.mkRef 0
    modify fun st => { st with snapshotTasks := #[] }
    runFilteredAsync (matching `A) (fun _ => successfulCalls.modify (· + 1))
    let some successfulObserver := (← get).snapshotTasks[0]? | throwError "missing successful observer"
    cleanupObserver.set (some successfulObserver)
    let some successfulSnapshot ← awaitTask "successful asynchronous observer" successfulObserver.task
      | throwError "successful observer did not terminate"
    check failures ((← successfulCalls.get) == 1) "successful async callback did not execute exactly once"
    check failures (successfulSnapshot.children.size == 1) "async waiter lost worker snapshot"
    if let some child := successfulSnapshot.children[0]? then
      check failures (child.task.get.element.desc == "A") "async waiter observed wrong filter"
      check failures (child.task.get.element.diagnostics.msgLog.toArray.size == 1) "async waiter lost diagnostics"
      check failures ((child.task.get.element.traces.tid == 41 && child.task.get.element.traces.traces.size == 1)) "async waiter lost profiling"
    successfulObserver.cancelRec

    -- A canceled pending asynchronous observer must finish even while the manager
    -- stays pending. No manager loop or solver is needed; cancellation is the only
    -- way to finish before the bounded failure guard.
    let pending := { mgr with _doneWith := {} }
    vcManager.atomically fun ref => ref.set pending
    let calls ← IO.mkRef 0
    let old := (← get).snapshotTasks
    modify fun st => { st with snapshotTasks := #[] }
    managerLoopErrors.set #["observer entered polling sentinel"]
    runFilteredAsync (matching `A) (fun _ => calls.modify (· + 1))
    let some observer := (← get).snapshotTasks[0]? | throwError "missing observer task"
    cleanupObserver.set (some observer)
    modify fun st => { st with snapshotTasks := old }
    -- The real waiter consumes this sentinel on entering its polling loop.
    -- Cancel only after that event, rather than relying on task scheduling.
    let deadline := (← IO.monoMsNow) + 10000
    while !(← managerLoopErrors.get).isEmpty do
      if (← IO.monoMsNow) > deadline then throwError "observer never began polling"
      IO.sleep 1
    observer.cancelRec
    let exited ← awaitTask "canceled observer" observer.task
    check failures exited.isSome "canceled observer kept polling"
    check failures ((← calls.get) == 0) "canceled observer ran callback"
    -- Release baseline's non-terminating poller after recording the failure.
    vcManager.atomically fun ref => ref.set mgr
    let _ ← awaitTask "cleanup observer" observer.task
    check failures (!(← a.cancelTk.isSet) && !(← b.cancelTk.isSet)) "async observer cancellation set worker token"
    mgr.cancelAllDischargers
    check failures ((← a.cancelTk.isSet) && (← b.cancelTk.isSet)) "explicit reset did not cancel workers"
    let errors ← failures.get
    for error in errors do liftIO <| IO.println s!"FAIL: {error}"
    unless errors.isEmpty do throwError "{errors.size} observer regressions"
    liftIO <| IO.println "observer registration, recursive cancellation and observer exit: PASS"
  finally
    nested.resolve default
    -- Empty manager lets the baseline poller exit even when an earlier test
    -- assertion throws; no worker or observer survives this fixture.
    vcManager.atomically fun ref => do ref.set (← VCManager.new vcManagerCh)
    if let some observer ← cleanupObserver.get then
      observer.cancelRec
      let _ ← awaitTask "finally cleanup observer" observer.task
    managerLoopErrors.set savedErrors
    vcManager.atomically fun ref => ref.set savedManager
    modify fun st => { st with snapshotTasks := savedSnapshots }

run_cmd run
