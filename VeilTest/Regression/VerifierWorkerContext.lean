module
meta import VeilTest.Regression.VerifierWorkerContextSupport
meta import Veil.Core.Tools.Verifier.TheoremDischarger

open Lean Elab Command Veil Veil.Verifier
meta section
private def await (label : String) (condition : BaseIO Bool) : IO Unit := do
  let deadline := (← IO.monoMsNow) + 10000
  while !(← condition) do
    if (← IO.monoMsNow) > deadline then throw <| IO.userError s!"timed out: {label}"
    IO.sleep 1

run_cmd do
  runManager
  withVCManager fun ref => do
    let (mgr, _) := (← ref.get).addVC {
      name := `workerCheckpoint, params := #[], statement := ← `(True), metadata := default } {}
    ref.set mgr

@[veil] public theorem workerCheckpoint : True := True.intro

run_cmd do
  unless !(interactiveRegistrationsExt.getState (← getEnv)).isEmpty do
    throwError "missing caller proof checkpoint fixture"
  let owner ← getVCManagerOwner
  let mgr ← readVCManager
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  workerContextGates.set (some (entered, release))
  let stmt : VCStatement := { name := `workerContext, params := #[], statement := ← `(True) }
  let term ← `(by worker_context_probe; exact workerAvailable)
  let id : DischargerIdentifier := { managerId := mgr._managerId, vcId := 1, dischargerId := 0, name := `workerContext }
  let callerMessages := (← get).messages
  let callerInfos := (← get).infoState
  let callerTrace := (← get).traceState
  logInfo "caller context diagnostic"
  modify fun st => { st with infoState := { st.infoState with enabled := false }, traceState := { st.traceState with tid := 31337 } }
  let before := ← get
  let d ← Discharger.fromTermWith term stmt id vcManagerCh fun _ outcome time => do
    unless (Veil.Verifier.vcManagerExt.getState (← getEnv)).isEmpty do
      throwError "mkResult captured manager handles"
    unless (Veil.Verifier.interactiveRegistrationsExt.getState (← getEnv)).isEmpty do
      throwError "mkResult captured checkpoint proof registrations"
    unless (← getEnv).contains ``workerAvailable do throwError "mkResult lost theorem environment"
    match outcome with
    | .inl witness => pure (.proven (some witness) none time)
    | .inr ex => pure (.error #[← safeExceptionEntry ex] time)
  let task ← IO.mkRef (none : Option SnapshotTreeTask)
  try
    let after := ← get
    unless after.messages.toArray.size == before.messages.toArray.size do throwError "capture lost caller diagnostics"
    unless after.infoState.enabled == false do throwError "capture lost caller info state"
    unless after.traceState.tid == 31337 do throwError "capture lost caller trace state"
    unless after.snapshotTasks.size == before.snapshotTasks.size do throwError "capture lost caller snapshot tasks"
    unless after.ngen.idx != before.ngen.idx || after.ngen.namePrefix != before.ngen.namePrefix do
      throwError "capture discarded fresh name-generator advances"
    unless (← readVCManager)._managerId == mgr._managerId do throwError "construction changed caller owner"
    unless !(interactiveRegistrationsExt.getState (← getEnv)).isEmpty do
      throwError "capture erased caller proof checkpoint"
    unless !(← d.startTimePromise.isResolved) do throwError "queued worker started during capture"
    withVCManager fun ref => do
      let (mgr, _) := (← ref.get).addVC { stmt with metadata := default } {} #[d]
      ref.set mgr
    startAll
    let running ← readVCManager
    task.set (running.nodes[1]?.bind fun vc => vc.dischargers[0]?.bind (·.task))
    await "worker sees detached environment" entered.isResolved
    unless (← readVCManager)._managerId == mgr._managerId do throwError "running worker changed caller owner"
    release.resolve ()
    await "result publication" d.resultPromise.isResolved
    let some result := d.resultPromise.result?.get | throwError "worker dropped result"
    unless result.isSuccessful do throwError "detached worker could not use ordinary theorem: {result.kindString}"
    await "accepted result" do
      owner.manager.atomically fun ref => return (← ref.get)._doneWith.contains 1
    if let some t ← task.get then
      await "worker snapshot diagnostics" (IO.hasFinished t)
      let diagnostics := t.get.element.diagnostics.msgLog.toArray
      unless diagnostics.size == 1 do throwError "worker inherited caller diagnostics or lost its own diagnostics"
      let rendered ← diagnostics[0]!.data.toString
      unless rendered == "worker context diagnostic" do throwError "wrong worker diagnostics: {rendered}"
    liftIO <| IO.println "queued/started worker excludes runtimes, retains theorem environment and diagnostics, restores caller state: PASS"
  finally
    release.resolve ()
    entered.resolve ()
    if let some t ← task.get then await "worker cleanup" (IO.hasFinished t)
    reset mgr._managerId
    workerContextGates.set none
    modify fun st => { st with messages := callerMessages, infoState := callerInfos, traceState := callerTrace }
