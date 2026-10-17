module
meta import Veil.Core.Tools.Verifier.TheoremDischarger
meta import Veil.Core.Tools.Verifier.Server
open Lean Elab Command Veil Veil.Verifier
meta section

private def check (b : Bool) (s : String) : CommandElabM Unit := unless b do throwError s
private def await (s : String) (p : BaseIO Bool) : IO Unit := do
  let deadline := (← IO.monoMsNow) + 10000
  while !(← p) do
    if (← IO.monoMsNow) > deadline then throw <| IO.userError s!"timeout: {s}"
    IO.sleep 1
private def readOwner (o : VCManagerEnvironment) : BaseIO (VCManager VCMetadata SmtResult) :=
  o.manager.atomically fun ref => ref.get
private def data (n : Name) : CommandElabM (VCData VCMetadata) := do
  return { name := n, params := #[], statement := ← `(True)
           metadata := .induction { (default : InductionVCMetadata) with property := n } }
private def barrier (o : VCManagerEnvironment) : CommandElabM Unit := do
  let n ← o.manager.atomically fun ref => do
    let mgr ← ref.get
    let (mgr, id) := mgr.addVC (← data `barrier) {}
    ref.set mgr
    return id
  enqueue o (.startFiltered (← readOwner o)._managerId (fun m => m.propertyName? == some `barrier))
  await "dispatcher barrier" do return (← readOwner o).enabledVCs.contains n

private structure Worker where
  d : Discharger SmtResult
  publish : IO.Promise Unit
  finish : IO.Promise Unit
  tasks : IO.Ref (Array SnapshotTreeTask)
private def worker (o : VCManagerEnvironment) (res : DischargerResult SmtResult) : BaseIO Worker := do
  let mgr ← readOwner o
  let publish ← IO.Promise.new
  let finish ← IO.Promise.new
  let tasks ← IO.mkRef #[]
  let resultPromise ← IO.Promise.new
  let startTimePromise ← IO.Promise.new
  let id := { managerId := mgr._managerId, vcId := 0, dischargerId := 0, name := `same : DischargerIdentifier }
  let mkTask := do
    let task ← BaseIO.asTask (prio := .dedicated) do
      startTimePromise.resolve 0
      discard <| IO.wait publish.result?
      publishDischargerResult resultPromise vcManagerCh id res
      discard <| IO.wait finish.result?
      return (default : Language.SnapshotTree)
    tasks.modify (·.push task)
    return task
  return { publish, finish, tasks, d := {
    id, resultPromise, startTimePromise, mkTask, task := none, cancelTk := ← IO.CancelToken.new } }
private def started (w : Worker) : BaseIO Bool := IO.hasFinished w.d.startTimePromise.result?
private def register (w : Worker) : CommandElabM Unit := withVCManager fun ref => do
  let (mgr, _) := (← ref.get).addVC (← data `same) {} #[w.d]
  ref.set mgr
private def cleanup (ws : Array Worker) : IO Unit := do
  for w in ws do
    w.publish.resolve (); w.finish.resolve ()
    w.d.resultPromise.resolve (.unknown none 0)
  for w in ws do
    for t in ← w.tasks.get do await "cleanup" (IO.hasFinished t)

private def ownership : CommandElabM Unit := do
  numCoresCache.set (some 1)
  runManager
  let aOwner ← getVCManagerOwner
  let envA ← getEnv
  let getter : CoreM (VCManager VCMetadata SmtResult) := withEnv envA readVCManager
  let a ← worker aOwner (.unknown none 0)
  register a
  let aCalls ← IO.mkRef (#[] : Array (Array (Name × Option VCStatus)))
  runFilteredAsync (fun m => m.propertyName? == some `same) fun r =>
    aCalls.modify (·.push (r.vcs.map fun v => (v.name, v.status)))
  await "A started" (started a)
  runManager
  let bOwner ← getVCManagerOwner
  let envB ← getEnv
  let b ← worker bOwner (.disproven none 0)
  try
    check (!(← a.d.cancelTk.isSet)) "creating B canceled A"
    check ((← readOwner aOwner)._managerId != (← readOwner bOwner)._managerId) "owner IDs collided"
    register b
    -- An empty request retires immediately; the next valid request must still
    -- enlist and schedule this same owner.
    startFiltered (fun _ => false)
    let bCalls ← IO.mkRef (#[] : Array (Array (Name × Option VCStatus)))
    runFilteredAsync (fun m => m.propertyName? == some `same) fun r =>
      bCalls.modify (·.push (r.vcs.map fun v => (v.name, v.status)))
    barrier bOwner
    check (!(← started b)) "B bypassed global capacity"
    check ((← liftCoreM getter)._managerId == (← readOwner aOwner)._managerId) "captured CoreM getter switched owners"
    setEnv envA
    let bId := (← readOwner bOwner)._managerId
    reset bId
    check ((← readOwner bOwner)._managerId == bId) "A request reset foreign owner B"
    let id := (← readVCManager)._managerId
    check (id == (← readOwner aOwner)._managerId) "saved environment lost owner"
    withVCManager fun ref => do
      let (mgr, _) := (← ref.get).addVC (← data `onlyA) {}
      ref.set mgr
    check ((← readOwner bOwner).findVCByFilter (fun m => m.propertyName? == some `onlyA)).isNone "restored mutation leaked to B"
    a.publish.resolve ()
    await "A callback" do return !(← aCalls.get).isEmpty
    check ((← aCalls.get) == #[#[(`same, some .unknown)]]) "A callback read B results"
    barrier bOwner
    check (!(← started b)) "result publication released physical capacity"
    -- Reset A after its result has been consumed. B stays independent and
    -- cannot run until the old A physical task actually exits.
    reset id
    await "A reset" do return (← readOwner aOwner)._managerId != id
    check (← a.d.cancelTk.isSet) "explicit reset failed to cancel A"
    check (!(← b.d.cancelTk.isSet)) "reset A canceled B"
    a.finish.resolve ()
    await "A completion starts B" (started b)
    b.publish.resolve ()
    await "B callback" do return !(← bCalls.get).isEmpty
    check ((← bCalls.get) == #[#[(`same, some .disproven)]]) "B callback read A results"
    setEnv envB
    barrier bOwner
    let active ← dispatcher.atomically fun ref => return (← ref.get).owners.size
    check (active == 0) "completed owners retained by registry"
  finally
    cleanup #[a,b]
  IO.println "owner environments, callbacks, captured getter, reset, physical capacity and retirement: PASS"

private def canceledOwner : CommandElabM Unit := do
  numCoresCache.set (some 1)
  runManager
  let aOwner ← getVCManagerOwner
  let a ← worker aOwner (.unknown none 0)
  register a
  startAll
  await "blocking A starts" (started a)
  let markerIndex := (← get).snapshotTasks.size
  runManager
  let ownerMarker := (← get).snapshotTasks[markerIndex]!
  let bOwner ← getVCManagerOwner
  let b ← worker bOwner (.unknown none 0)
  register b
  let calls ← IO.mkRef 0
  let savedSnapshots := (← get).snapshotTasks
  let before := savedSnapshots.size
  runFilteredAsync (fun _ => true) (fun _ => calls.modify (· + 1))
  let observer := (← get).snapshotTasks[before]!
  modify fun st => { st with snapshotTasks := savedSnapshots }
  try
    barrier bOwner
    ownerMarker.cancelRec
    check (← bOwner.cancelTk.isSet) "origin snapshot did not cancel its owner"
    check (!(← aOwner.cancelTk.isSet)) "origin snapshot canceled another owner"
    barrier aOwner
    await "canceled owner observer exits" (IO.hasFinished observer.task)
    let errors := observer.task.get.element.diagnostics.msgLog.toArray.filter (·.severity == .error)
    check (errors.size == 1) "canceled owner observer lost interruption diagnostic"
    let message ← errors[0]!.data.toString
    check (message.contains "specification owner was canceled") "unexpected observer error"
    check ((← calls.get) == 0) "obsolete owner observer invoked callback"
    check (← b.d.cancelTk.isSet) "obsolete owner did not cancel its queued worker"
    a.publish.resolve (); a.finish.resolve ()
    await "A finishes" do return (← readOwner aOwner)._dischargerResults.contains (0,0)
    barrier aOwner
    check (!(← started b)) "obsolete owner admitted queued worker"
    let active ← dispatcher.atomically fun ref => return (← ref.get).owners.size
    check (active == 0) "obsolete owner retained by dispatcher"
  finally
    cleanup #[a,b]
    observer.cancelRec
  IO.println "obsolete owner stops queued admissions, terminates observer and retires: PASS"

run_cmd ownership
run_cmd canceledOwner
