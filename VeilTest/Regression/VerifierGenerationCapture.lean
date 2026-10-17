module
meta import VeilTest.Regression.VerifierGenerationSupport
open Lean Elab Command Veil Veil.Verifier VeilTest.VerifierGeneration
meta section

-- A synchronous channel continuation replaces the manager as the start request
-- is sent, before runFilteredAsync can launch its waiter. This distinguishes
-- capture on the caller from capture at the async task's first poll.
run_cmd do
  let saved ← manager
  let savedSnapshots := (← get).snapshotTasks
  let observerRef ← IO.mkRef (none : Option (Language.SnapshotTask Language.SnapshotTree))
  let replaced ← IO.Promise.new
  try
    let original ← fresh #[`original]
    let replacement ← VCManager.new vcManagerCh (currentManagerId := original._managerId)
    let request ← vcManagerCh.recv
    check (!(← IO.hasFinished request)) "earlier queued request invalidated capture fixture"
    BaseIO.chainTask request (sync := true) fun _ => do
      vcManager.atomically fun ref => ref.set replacement
      replaced.resolve ()
    let calls ← IO.mkRef 0
    modify fun st => { st with snapshotTasks := #[] }
    runFilteredAsync (fun _ => true) (fun _ => calls.modify (· + 1))
    let some observer := (← get).snapshotTasks[0]? | throwError "missing observer"
    observerRef.set (some observer)
    check (← replaced.isResolved) "test did not replace synchronously during start enqueue"
    await "observer exits after synchronous replacement" (IO.hasFinished observer.task)
    discard <| IO.wait observer.task
    check ((← calls.get) == 0) "observer adopted manager installed before its task began"
    liftIO <| IO.println "manager identity captured before async launch: PASS"
  finally
    let _ ← fresh #[]
    if let some observer ← observerRef.get then
      observer.cancelRec
      await "observer cleanup" (IO.hasFinished observer.task)
    replaced.resolve ()
    vcManager.atomically fun ref => ref.set saved
    modify fun st => { st with snapshotTasks := savedSnapshots }
