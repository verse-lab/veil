module

public meta import Veil.Core.Tools.Verifier.Server

public meta section
open Lean Elab Command Veil Veil.Verifier

private def awaitTask (task : Task α) : CommandElabM α := do
  let deadline ← (do IO.sleep 5000; pure (none : Option α)).asTask (prio := .dedicated)
  let some result ← IO.waitAny [task.map some, deadline] | throwError "capacity regression timed out"
  return result

private def launch (entered release : IO.Promise Unit) : CommandElabM Session := do
  runManager
  let session ← getSession
  withVCManager fun ref => do
    let data : VCData VCMetadata := {name := `capacity, params := #[], statement := ← `(term| True), metadata := default}
    let (mgr, id) := (← ref.get).addVC data {}
    ref.set (← mgr.mkAddDischarger id fun _ id ch => do
      let resultPromise ← IO.Promise.new
      let startTimePromise ← IO.Promise.new
      return {
        id, task := none, cancelTk := ← IO.CancelToken.new, resultPromise, startTimePromise
        mkTask := (do
          startTimePromise.resolve (← IO.monoMsNow)
          entered.resolve ()
          -- Publish before exiting to test the physical lifetime independently.
          publishDischargerResult resultPromise ch id (.proven (some (mkConst ``True.intro)) none 0)
          let _ ← IO.wait release.result?
          pure default).asTask (prio := .dedicated)})
  startAll
  return session

run_cmd do
  let cores ← numCoresCache.get
  numCoresCache.set (some 1)
  let releaseFirst ← IO.Promise.new
  let releaseSecond ← IO.Promise.new
  try
    let enteredFirst ← IO.Promise.new
    let first ← launch enteredFirst releaseFirst
    let _ ← awaitTask enteredFirst.result?
    let enteredSecond ← IO.Promise.new
    let second ← launch enteredSecond releaseSecond
    IO.sleep 100
    unless !(← IO.hasFinished enteredSecond.result?) do
      throwError "another session exceeded the process-wide capacity"
    unless (← (← first.snapshot).inFlightCount) == 1 && (← (← second.snapshot).inFlightCount) == 0 do
      throwError "physical slot was released before worker exit"
    releaseFirst.resolve ()
    let _ ← awaitTask enteredSecond.result?
    releaseSecond.resolve ()
    let _ ← waitFilteredSync (fun _ => true)
  finally
    releaseFirst.resolve ()
    releaseSecond.resolve ()
    numCoresCache.set cores
