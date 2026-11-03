module
meta import Veil.Core.Tools.Verifier.TheoremDischarger
meta import Veil.Core.UI.Verifier.VerificationResults
meta import VeilTest.Regression.VerifierObserverSupport

open Lean Elab Command Std Veil Veil.Verifier VeilTest.VerifierObserver
meta section

private def waitFor (label : String) (p : BaseIO Bool) : CommandElabM Unit := do
  let deadline := (← IO.monoMsNow) + 10000
  while !(← p) do
    if (← IO.monoMsNow) > deadline then throwError "timeout: {label}"
    IO.sleep 1

private def attached (mgr : Mgr) : CommandElabM (HashSet DischargerIdentifier) := do
  let saved := (← get).snapshotTasks
  modify fun st => { st with snapshotTasks := #[] }
  try logPendingDischargerTasks mgr (fun _ => true) {}
  finally modify fun st => { st with snapshotTasks := saved }

private def scenario (fallbackSucceeds : Bool) : CommandElabM Unit := do
  let failures ← IO.mkRef (#[] : Array String)
  let check := fun (b : Bool) (message : String) => unless b do failures.modify (·.push message)
  runManager
  let owner ← getVCManagerOwner
  let generation := (← readVCManager)._managerId
  let primaryGate ← IO.Promise.new
  let fallbackGate ← IO.Promise.new
  let primaryEntered ← IO.Promise.new
  let fallbackEntered ← IO.Promise.new
  let primaryCalls ← IO.mkRef 0
  let fallbackCalls ← IO.mkRef 0
  let tasks ← IO.mkRef (#[] : Array SnapshotTreeTask)
  let mkWorker := fun (vcId : Nat) (gate entered : IO.Promise Unit) (calls : IO.Ref Nat)
      (result : DischargerResult SmtResult) => do
    let resultPromise ← IO.Promise.new
    let startTimePromise ← IO.Promise.new
    let id : DischargerIdentifier := { managerId := generation, vcId, dischargerId := 0, name := `automatic }
    let mkTask := do
      let task ← BaseIO.asTask (prio := .dedicated) do
        calls.modify (· + 1)
        startTimePromise.resolve 0
        entered.resolve ()
        let _ ← IO.wait gate.result?
        publishDischargerResult resultPromise vcManagerCh id result
        tree "fallback diagnostic"
      tasks.modify (·.push task)
      return task
    let cancelTk ← IO.CancelToken.new
    return ({ id := id
              cancelTk := cancelTk
              task := none
              startTimePromise := startTimePromise
              resultPromise := resultPromise
              mkTask := mkTask } : Discharger SmtResult)
  let primary ← mkWorker 0 primaryGate primaryEntered primaryCalls (.unknown none 0)
  let result := if fallbackSucceeds then .proven (some (mkConst ``True.intro)) none 0 else .error #[] 0
  let fallback ← mkWorker 1 fallbackGate fallbackEntered fallbackCalls result
  let proofName := if fallbackSucceeds then `fallbackSuccessProof else `fallbackErrorProof
  withVCManager fun ref => do
    let (mgr, _) := (← ref.get).addVC (← data proofName) {} #[primary]
    let (mgr, _) := mgr.addAlternativeVC (← data `alternative) 0 #[fallback]
    ref.set mgr
  let oldEnv ← getEnv
  let oldGetter ← captureVCManager
  let savedMessages := (← get).messages
  try
    elabCommand (← `(command| @[veil] public theorem $(mkIdent proofName) : True := True.intro))
    let successGetter ← captureVCManager
    setEnv oldEnv
    elabCommand (← `(command| @[veil] public theorem $(mkIdent proofName) : True := by sorry))
    modify fun st => { st with messages := savedMessages }
    let errorEnv ← getEnv
    let errorGetter ← captureVCManager
    -- Both requests pass through the actual admission path. The proof-only
    -- checkpoint must not enable its hidden alternatives in the shared base.
    startAll
    startFiltered (fun _ => true)
    let base ← owner.manager.atomically fun ref => ref.get
    check (base.enabledVCs.isEmpty) "proof-only request enabled hidden automatic work"
    check ((← primaryCalls.get) == 0 && (← fallbackCalls.get) == 0) "proof-only request started work"
    setEnv oldEnv
    startFiltered (matching proofName)
    waitFor "primary start" primaryEntered.isResolved
    setEnv errorEnv
    let checkViews := fun (stage : String) => do
      for (getter, status, failed) in #[(successGetter, VCStatus.proven, false), (errorGetter, .error, true)] do
        let view ← getter
        check (view._doneWith[0]? == some status) s!"{stage}: interactive status lost"
        check (view.dormantVCs.contains 1) s!"{stage}: fallback visible"
        check (view.isDone && view.isDoneFiltered (fun _ => true)) s!"{stage}: proof checkpoint waits for fallback"
        check ((← view.inFlightCount) == 0) s!"{stage}: hidden work counted in flight"
        check (!(← attached view).contains fallback.id) s!"{stage}: hidden fallback diagnostics attached"
        let results ← liftCoreM <| view.toResults (fun _ => true)
        check (hasFailedVCs results == failed) s!"{stage}: fallback changed proof failure reporting"
      check (!(← primary.cancelTk.isSet) && !(← fallback.cancelTk.isSet)) s!"{stage}: shared work canceled"
    checkViews "before primary failure"
    check ((← (← oldGetter).inFlightCount) == 1) "old getter lost primary flight"
    primaryGate.resolve ()
    waitFor "fallback start" fallbackEntered.isResolved
    checkViews "gated fallback"
    let old ← oldGetter
    check (!old.isDone && !old.dormantVCs.contains 1 && old.enabledVCs.contains 1) "old getter lost fallback"
    check ((← old.inFlightCount) == 1) "old getter lost fallback flight"
    check ((← attached old).contains fallback.id) "old observer lost fallback diagnostic"
    setEnv oldEnv
    check (!(← readVCManager).dormantVCs.contains 1 && !(← readVCManager).isDone) "rollback lost running fallback"
    setEnv errorEnv
    fallbackGate.resolve ()
    waitFor "fallback acceptance" (owner.manager.atomically fun ref => return (← ref.get)._dischargerResults.contains (1, 0))
    checkViews "accepted fallback"
    let old ← oldGetter
    check (old.isDone && old._doneWith[1]? == some (if fallbackSucceeds then .proven else .error)) "old getter lost accepted fallback"
    let results ← liftCoreM <| old.toResults (fun _ => true)
    check (hasFailedVCs results == !fallbackSucceeds) "old UI lost fallback outcome"
    setEnv oldEnv
    check ((← readVCManager)._doneWith[1]? == old._doneWith[1]?) "rollback lost accepted fallback"
    check ((← primaryCalls.get) == 1 && (← fallbackCalls.get) == 1) "shared attempts restarted"
  finally
    primaryGate.resolve ()
    fallbackGate.resolve ()
    for task in ← tasks.get do
      let _ ← IO.wait task
    setEnv oldEnv
    modify fun st => { st with messages := savedMessages }
  unless (← failures.get).isEmpty do
    throwError "{String.intercalate "\n" (← failures.get).toList}"

run_cmd scenario true
run_cmd scenario false
