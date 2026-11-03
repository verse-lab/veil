module
meta import all Veil.Core.Tools.Verifier.TheoremDischarger
meta import Batteries.Tactic.OpenPrivate

open Lean Elab Command Veil Veil.Verifier
meta section

private def ensure (b : Bool) (message : String) : CommandElabM Unit :=
  unless b do throwError message

private def waitFor (label : String) (p : BaseIO Bool) : CommandElabM Unit := do
  let deadline := (← IO.monoMsNow) + 10000
  while !(← p) do
    if (← IO.monoMsNow) > deadline then throwError "timeout waiting for {label}"
    IO.sleep 1

private def expectStatus (expected : Option VCStatus) : CommandElabM Unit := do
  ensure ((← readVCManager)._doneWith[0]? == expected) s!"wrong checkpoint status, expected {expected.map toString}"

run_cmd do
  runManager
  let owner ← getVCManagerOwner
  let managerId := (← readVCManager)._managerId
  let started ← IO.Promise.new
  let publishGate ← IO.Promise.new
  let exitGate ← IO.Promise.new
  let exited ← IO.Promise.new
  let physicalTask ← IO.mkRef (none : Option SnapshotTreeTask)
  let observerTask ← IO.mkRef (none : Option SnapshotTreeTask)
  let callbackSeen ← IO.Promise.new
  let calls ← IO.mkRef 0
  let cancelTk ← IO.CancelToken.new
  let startTimePromise ← IO.Promise.new
  let resultPromise ← IO.Promise.new
  let id : DischargerIdentifier := { managerId, vcId := 0, dischargerId := 0, name := `auto }
  let automatic : Discharger SmtResult := {
    id, cancelTk, startTimePromise, resultPromise, task := none
    mkTask := do
      calls.modify (· + 1)
      BaseIO.asTask (prio := .dedicated) do
        startTimePromise.resolve (← IO.monoMsNow)
        started.resolve ()
        let _ ← IO.wait publishGate.result?
        publishDischargerResult resultPromise vcManagerCh id (.proven (some (mkConst ``True.intro)) none 0)
        let _ ← IO.wait exitGate.result?
        exited.resolve ()
        pure default }
  try
    withVCManager fun ref => do
      let (mgr, _) := (← ref.get).addVC {
        name := `goal, params := #[], statement := ← `(True), metadata := default } {} #[automatic]
      ref.set mgr
    let before ← getEnv
    let oldGetter ← captureVCManager
    let beforeSnapshots := (← get).snapshotTasks.size
    runFilteredAsync (fun _ => true) fun results => do
      ensure (results.vcs[0]?.bind (·.status) == some .proven) "captured callback saw future interactive result"
      ensure (!(← readVCManager).nodes[0]!.hasInteractiveDischarger) "callback adopted future checkpoint"
      callbackSeen.resolve ()
    let some observer := (← get).snapshotTasks[beforeSnapshots]? | throwError "missing async observer task"
    observerTask.set (some observer.task)
    waitFor "automatic entry" started.isResolved
    let running ← readVCManager
    let some workerTask := running.nodes[0]?.bind (fun vc => vc.dischargers[0]?.bind (·.task))
      | throwError "missing physical worker task"
    physicalTask.set (some workerTask)
    let savedMessages := (← get).messages
    elabCommand (← `(command| @[veil] public theorem $(mkIdent `goal) : True := True.intro))
    let success ← getEnv
    let successGetter ← captureVCManager
    expectStatus (some .proven)
    let proofView ← readVCManager
    ensure ((← proofView.inFlightCount) == 0) "proof view counted hidden automatic work"
    ensure ((← (← oldGetter).inFlightCount) == 1) "old checkpoint lost pending automatic work"
    ensure (!(← oldGetter)._doneWith.contains 0) "captured getter saw a future registration"
    ensure (!(← callbackSeen.isResolved)) "future proof completed old pending callback"
    ensure (!(← cancelTk.isSet)) "future proof canceled an earlier automatic attempt"
    -- A branch from the same old checkpoint must not overwrite success.
    setEnv before
    elabCommand (← `(command| @[veil] public theorem $(mkIdent `goal) : True := by sorry))
    let error ← getEnv
    let errorGetter ← captureVCManager
    expectStatus (some .error)
    ensure ((← successGetter)._doneWith[0]? == some .proven) "error branch overwrote proof branch"
    ensure ((← errorGetter)._doneWith[0]? == some .error) "error getter lost interactive precedence"
    setEnv success
    expectStatus (some .proven)
    setEnv before
    expectStatus none
    ensure (!(← readVCManager).nodes[0]!.hasInteractiveDischarger) "rollback retained interactive discharger"
    -- Shared automatic publication is accepted while the error branch exists.
    setEnv error
    publishGate.resolve ()
    waitFor "automatic acceptance" (owner.manager.atomically fun ref => return (← ref.get)._dischargerResults.contains (0, 0))
    waitFor "old checkpoint callback" callbackSeen.isResolved
    expectStatus (some .error)
    ensure ((← oldGetter)._doneWith[0]? == some .proven) "old getter did not observe shared automatic result"
    ensure ((← successGetter)._doneWith[0]? == some .proven) "automatic result changed valid proof view"
    ensure ((← errorGetter)._doneWith[0]? == some .error) "automatic success hid interactive error"
    setEnv before
    elabCommand (← `(command| @[veil] public theorem $(mkIdent `goal) : True := by sorry))
    expectStatus (some .error)
    -- Completion and theorem lookup use the same effective checkpoint view.
    let results ← waitFilteredSync (fun _ => true)
    ensure (results.vcs[0]?.bind (·.status) == some .error) "wait used another checkpoint"
    setEnv before
    let results ← waitFilteredSync (fun _ => true)
    ensure (results.vcs[0]?.bind (·.status) == some .proven) "rollback did not reuse automatic result"
    ensure ((← calls.get) == 1) "rollback reran one-shot automatic task"
    addProvenTheoremsInDependencyOrder (fun _ => true)
    ensure ((← getEnv).contains `goal) "automatic theorem missing after rollback"
    -- A failed command's environment is discarded by its command checkpoint.
    setEnv before
    try
      elabCommand (← `(command| @[veil] public theorem $(mkIdent `goal) : True := True.intro))
      throwError "discard this command"
    catch _ => setEnv before
    ensure (!(← readVCManager).nodes[0]!.hasInteractiveDischarger) "failed command left registration"
    -- Reset invalidates old environment-backed records even if names/VC IDs recur.
    setEnv error
    reset managerId
    withVCManager fun ref => do
      let (mgr, _) := (← ref.get).addVC {
        name := `goal, params := #[], statement := ← `(True), metadata := default } {}
      ref.set mgr
    ensure (!(← readVCManager).nodes[0]!.hasInteractiveDischarger) "reset revived old-generation proof"
    ensure ((← readVCManager)._doneWith.isEmpty) "reset inherited old proof status"
    modify fun st => { st with messages := savedMessages }
    liftIO <| IO.println "interactive rollback, branches, captured getter, automatic reuse, reset: PASS"
  finally
    publishGate.resolve ()
    exitGate.resolve ()
    waitFor "physical worker exit" exited.isResolved
    if let some task ← physicalTask.get then
      waitFor "physical task completion" (IO.hasFinished task)
    if let some task ← observerTask.get then
      waitFor "observer task exit" (IO.hasFinished task)
    -- Keep every promise owner alive until the real task has left its gates.
    discard <| pure (started, publishGate, exitGate, exited, startTimePromise, resultPromise, callbackSeen)


-- A stored interactive checkpoint must survive an automatic array growing
-- after capture, and repeat registration must replace its own entry.
run_cmd do
  runManager
  withVCManager fun ref => do
    let (mgr, _) := (← ref.get).addVC {
      name := `late, params := #[], statement := ← `(True), metadata := default } {}
    ref.set mgr
  elabCommand (← `(command| @[veil] public theorem $(mkIdent `late) : True := True.intro))
  let getter ← captureVCManager
  let cancelTk ← IO.CancelToken.new
  let startTimePromise ← IO.Promise.new
  let resultPromise ← IO.Promise.new
  let calls ← IO.mkRef 0
  let generation := (← readVCManager)._managerId
  let id : DischargerIdentifier := { managerId := generation, vcId := 0, dischargerId := 0, name := `lateAuto }
  let d : Discharger SmtResult := {
    id, cancelTk, startTimePromise, resultPromise, task := none
    mkTask := do
      calls.modify (· + 1)
      BaseIO.asTask (pure default) }
  withVCManager fun ref => ref.modify (·.addDischarger 0 d)
  ensure ((← getter)._doneWith[0]? == some .proven) "late automatic addition collided with stored interactive ID"
  ensure ((← getter).nodes[0]!.successful == some 1) "view did not rebase interactive ID"
  elabCommand (← `(command| attribute [veil] $(mkIdent `late)))
  ensure ((← readVCManager).nodes[0]!.dischargers.size == 2) "repeat registration duplicated checkpoint proof"
  startAll
  ensure ((← calls.get) == 0) "interactive checkpoint started unrequested automatic work"
  ensure (!(← cancelTk.isSet)) "view canceled dormant automatic work"
  liftIO <| IO.println "late automatic append, repeat registration, request-local scheduling: PASS"


open private Veil.Verifier.registerFinishedTheoremDischarger from Veil.Core.Tools.Verifier.TheoremDischarger

run_cmd do
  runManager
  let owner ← getVCManagerOwner
  let generation := (← readVCManager)._managerId
  withVCManager fun ref => do
    let (mgr, _) := (← ref.get).addVC {
      name := `bad, params := #[], statement := ← `(True), metadata := default } {}
    ref.set { mgr with
      nodes := mgr.nodes.modify 0 (fun vc => { vc with successful := some 0 })
      _doneWith := mgr._doneWith.insert 0 .proven
      _dischargerResults := mgr._dischargerResults.insert (0, 0)
        (.proven (some (mkConst ``True.intro)) none 0) }
  let before ← getEnv
  elabCommand (← `(command| @[veil] public theorem $(mkIdent `bad) : True ∧ True := ⟨True.intro, True.intro⟩))
  expectStatus (some .error)
  setEnv before
  expectStatus (some .proven)
  reset generation
  let result ← liftCoreM <| registerFinishedTheoremDischarger owner generation `bad
    (.proven (some (mkConst ``True.intro)) none 0)
  ensure (match result with | .error _ => true | _ => false) "stale validated registration crossed reset"
  ensure ((← readVCManager).nodes.isEmpty) "stale registration mutated reset manager"
  liftIO <| IO.println "invalid witness rollback and generation validation: PASS"
