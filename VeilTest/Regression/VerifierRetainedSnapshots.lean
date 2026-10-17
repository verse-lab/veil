import VeilTest.Regression.VerifierCancellationSupport

open Lean Elab Command Veil Veil.Verifier

private def awaitTask (task : Task α) : CommandElabM α := do
  let deadline ← (do IO.sleep 5000; pure (none : Option α)).asTask (prio := .dedicated)
  let some result ← IO.waitAny [task.map some, deadline] | throwError "retained snapshot regression timed out"
  return result

private def addTestVC (name : Name) (term : Term) : CommandElabM Unit :=
  withVCManager fun ref => do
    let data : VCData VCMetadata := {name, params := #[], statement := ← `(term| True), metadata := default}
    let (mgr, id) := (← ref.get).addVC data {}
    ref.set (← mgr.mkAddDischarger id fun statement id ch =>
      Discharger.fromTermWith term statement id ch fun _ outcome time =>
        match outcome with
        | .inl witness => pure (.proven witness none time)
        | .inr ex => pure (.error #[(ex, toJson "test discharger failed")] time))

run_cmd do
  for cancelRetained in [false, true] do
    runManager
    let entered ← IO.Promise.new
    let release ← IO.Promise.new
    gates.set (some (entered, release))
    try
      addTestVC `retained (← `(term| by await_cancellation; trivial))
      let old ← getSession
      let result ← IO.Promise.new
      runFilteredAsync (fun _ => true) fun results => result.resolve results.totalSolved
      let waiter := (← get).snapshotTasks.back!
      let _ ← awaitTask entered.result?
      let oldMgr ← old.snapshot
      let some d := oldMgr.nodes[0]!.dischargers[0]? | throwError "missing original attempt"
      withReader (fun ctx => {ctx with fileMap := FileMap.ofString (ctx.fileMap.source ++ "\n-- edit below retained command")}) do
        let fresh ← getSession
        unless (← fresh.snapshot)._managerId != oldMgr._managerId do throwError "generation was not forked"
        let _ ← old.snapshot
        unless !(← d.cancelTk.isSet) do throwError "fork cancelled a retained snapshot's work"
        if cancelRetained then
          if let some token := waiter.cancelTk? then token.set
          let _ ← awaitTask waiter.task
          unless ← d.cancelTk.isSet do throwError "retained request failed to release after cancellation"
          release.resolve ()
        else
          release.resolve ()
          let _ ← awaitTask waiter.task
          unless (← IO.hasFinished result.result?) && result.result?.get == some 1 do
            throwError "retained snapshot did not deliver its original result"
    finally
      release.resolve ()

run_cmd do
  -- Driver failure must revoke running attempts without poisoning queued ones.
  let cores ← numCoresCache.get
  numCoresCache.set (some 1)
  let release ← IO.Promise.new
  try
    runManager
    let entered ← IO.Promise.new
    gates.set (some (entered, release))
    addTestVC `one (← `(term| by await_cancellation; trivial))
    addTestVC `two (← `(term| by await_cancellation; trivial))
    startAll
    let session ← getSession
    let _ ← awaitTask entered.result?
    let before ← session.snapshot
    let some running := before.nodes.valuesArray.findSome? (fun vc => vc.dischargers.find? (·.task.isSome))
      | throwError "missing running attempt"
    try
      session.withManager fun ref => ref.modify fun mgr => {mgr with upstream := mgr.upstream.insert 0 {0}}
    catch _ => pure ()
    let stopped ← (do
      while !(← running.cancelTk.isSet) do IO.sleep 1).asTask (prio := .dedicated)
    let _ ← awaitTask stopped
    for vc in before.nodes.valuesArray do
      for d in vc.dischargers do
        if d.task.isNone then
          unless !(← d.cancelTk.isSet) do throwError "driver failure poisoned queued resources"
    session.withManager fun ref => ref.modify fun mgr => {mgr with upstream := mgr.upstream.insert 0 {}}
    release.resolve ()
    let result ← waitFilteredSync (fun _ => true)
    unless result.totalSolved == 2 do throwError "repaired driver did not restart revoked work"
  finally
    release.resolve ()
    numCoresCache.set cores
