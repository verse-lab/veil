module
public meta import Veil.Core.Tools.Verifier.Server

public meta section
namespace VeilTest.VerifierGeneration
open Lean Elab Command Veil Veil.Verifier

abbrev Mgr := VCManager VCMetadata SmtResult

def check (condition : Bool) (message : String) : CommandElabM Unit :=
  unless condition do throwError message

def await (label : String) (condition : BaseIO Bool) : IO Unit := do
  let deadline := (← IO.monoMsNow) + 10000
  while !(← condition) do
    if (← IO.monoMsNow) > deadline then
      throw <| IO.userError s!"timed out: {label}"
    IO.sleep 1

def manager : CommandElabM Mgr := readVCManager

def data (name : Name) : CommandElabM (VCData VCMetadata) := do
  return { name, params := #[], statement := ← `(True)
           metadata := .induction { (default : InductionVCMetadata) with property := name } }

def matching (name : Name) (metadata : VCMetadata) : Bool := metadata.propertyName? == some name

def fresh (names : Array Name) (completed : Bool := false) : CommandElabM Mgr := do
  reset (← manager)._managerId
  let mut mgr ← manager
  for name in names do
    let (mgr', id) := mgr.addVC (← data name) {}
    mgr := mgr'
    if completed then mgr := { mgr with _doneWith := mgr._doneWith.insert id .proven }
  withVCManager fun ref => ref.set mgr
  return mgr

def barrier : CommandElabM Unit := do
  let owner ← getVCManagerOwner
  let manager := owner.manager.atomically (m := BaseIO) fun ref => ref.get
  let (id, name) ← withVCManager fun ref => do
    let mgr ← ref.get
    let name := Name.mkSimple s!"barrier{mgr._nextVcId}"
    let (mgr, id) := mgr.addVC (← data name) {}
    ref.set mgr
    return (id, name)
  startFiltered (matching name)
  await "notification barrier" do return (← manager).enabledVCs.contains id

/-- Scoped requests carry their original generation even when applied after a
reset. Frontend starts now apply atomically, so there is no pre-driver queue. -/
def queuedStart (filtered : Bool) : CommandElabM Unit := do
  runManager
  let original ← fresh #[`target]
  let mgr ← fresh #[`target]
  let owner ← getVCManagerOwner
  let manager := owner.manager.atomically (m := BaseIO) fun ref => ref.get
  let starts ← IO.mkRef 0
  let resultPromise ← IO.Promise.new
  let startTimePromise ← IO.Promise.new
  let worker : Discharger SmtResult := {
    id := { managerId := mgr._managerId, vcId := 0, dischargerId := 0, name := `worker }
    cancelTk := ← IO.CancelToken.new, task := none, resultPromise, startTimePromise
    mkTask := do
      starts.modify (· + 1)
      startTimePromise.resolve 0
      publishDischargerResult resultPromise vcManagerCh
        { managerId := mgr._managerId, vcId := 0, dischargerId := 0, name := `worker }
        (.unknown none 0)
      return .pure default }
  try
    withVCManager fun ref => ref.set (mgr.addDischarger 0 worker)
    sendNotification (if filtered then .startFiltered original._managerId (matching `target)
      else .startAll original._managerId)
    barrier
    check (!(← manager).enabledVCs.contains 0) "stale scoped start enabled replacement VC"
    check ((← starts.get) == 0) "stale scoped start admitted replacement worker"
    if filtered then startFiltered (matching `target) else startAll
    barrier
    check ((← manager).enabledVCs.contains 0) "current start did not enable VC"
    check ((← starts.get) == 1) "current start did not admit exactly one worker"
    liftIO <| IO.println s!"scoped start (filtered={filtered}): PASS"
  finally
    resultPromise.resolve (.unknown none 0)
    startTimePromise.resolve 0

/-- Each stale test enters the production waiter and consumes a sentinel before
replacement. No timed ordering is used; the deadline only bounds failure. -/
def staleWait (asynchronous : Bool) (replacement : Nat) : CommandElabM Unit := do
  runManager
  let owner ← getVCManagerOwner
  let managerLoopErrors := owner.errors
  let saved ← manager
  let savedSnapshots := (← get).snapshotTasks
  let savedErrors ← managerLoopErrors.get
  let cleanup ← IO.mkRef (none : Option (Language.SnapshotTask Language.SnapshotTree))
  try
    let _ ← fresh #[`original]
    let calls ← IO.mkRef (#[] : Array (Array Name))
    managerLoopErrors.set #["generation observer polling sentinel"]
    modify fun st => { st with snapshotTasks := #[] }
    if asynchronous then
      runFilteredAsync (fun _ => true) fun results => calls.modify (·.push (results.vcs.map (·.name)))
    else
      let cancelTk ← IO.CancelToken.new
      let wrapped ← Command.wrapAsyncAsSnapshot (fun () => do
        try
          let results ← waitFilteredSync (fun _ => true)
          calls.modify (·.push (results.vcs.map (·.name)))
        catch _ => pure ()) cancelTk
      let task ← (wrapped ()).asTask (prio := .dedicated)
      Command.logSnapshotTask { stx? := none, cancelTk? := cancelTk, task }
    let some observer := (← get).snapshotTasks[0]? | throwError "missing observer task"
    cleanup.set (some observer)
    modify fun st => { st with snapshotTasks := savedSnapshots }
    await "actual waiter poll entry" do return (← managerLoopErrors.get).isEmpty
    let _ ← fresh (if replacement == 0 then #[] else #[`replacement]) (replacement == 1)
    await "stale observer termination" (IO.hasFinished observer.task)
    discard <| IO.wait observer.task
    check (← calls.get).isEmpty "stale waiter returned replacement results or invoked callback"
    liftIO <| IO.println s!"stale waiter (async={asynchronous}, replacement={replacement}): PASS"
  finally
    let _ ← fresh #[]
    if let some observer ← cleanup.get then
      observer.cancelRec
      await "observer cleanup" (IO.hasFinished observer.task)
      discard <| IO.wait observer.task
    withVCManager fun ref => ref.set saved
    managerLoopErrors.set savedErrors
    modify fun st => { st with snapshotTasks := savedSnapshots }

def currentWaits : CommandElabM Unit := do
  runManager
  let saved ← manager
  let savedSnapshots := (← get).snapshotTasks
  let cleanup ← IO.mkRef (none : Option (Language.SnapshotTask Language.SnapshotTree))
  try
    let _ ← fresh #[`original] true
    let results ← waitFilteredSync (fun _ => true)
    check (results.vcs.map (·.name) == #[`original]) "current synchronous waiter returned wrong results"
    let calls ← IO.mkRef (#[] : Array (Array Name))
    modify fun st => { st with snapshotTasks := #[] }
    runFilteredAsync (fun _ => true) fun results => calls.modify (·.push (results.vcs.map (·.name)))
    let some observer := (← get).snapshotTasks[0]? | throwError "missing current observer"
    cleanup.set (some observer)
    await "current observer" (IO.hasFinished observer.task)
    discard <| IO.wait observer.task
    check ((← calls.get) == #[#[`original]]) "current async callback missing, duplicated or incorrect"
    liftIO <| IO.println "current synchronous and asynchronous waits: PASS"
  finally
    if let some observer ← cleanup.get then
      observer.cancelRec
      await "current observer cleanup" (IO.hasFinished observer.task)
    withVCManager fun ref => ref.set saved
    modify fun st => { st with snapshotTasks := savedSnapshots }

end VeilTest.VerifierGeneration
