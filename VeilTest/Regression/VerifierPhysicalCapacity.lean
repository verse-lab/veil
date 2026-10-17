module

meta import Veil.Core.Tools.Verifier.Server

/- Real server admissions with gated SnapshotTree tasks. Timing is used only
as a bounded failure guard; assertions follow processed notification barriers.
Run in an isolated Lean process because this forces the process core count. -/

open Lean Elab Command Veil Veil.Verifier
meta section

private def check (condition : Bool) (message : String) : CommandElabM Unit :=
  unless condition do throwError message

private def await (label : String) (condition : BaseIO Bool) : IO Unit := do
  let deadline := (← IO.monoMsNow) + 10000
  while !(← condition) do
    if (← IO.monoMsNow) > deadline then
      throw <| IO.userError s!"timed out: {label}"
    IO.sleep 1

private def manager : BaseIO (VCManager VCMetadata SmtResult) :=
  vcManager.atomically fun ref => ref.get

private def data (name : Name) : CommandElabM (VCData VCMetadata) := do
  return { name, params := #[], statement := ← `(True)
           metadata := .induction { (default : InductionVCMetadata) with property := name } }

/-- An empty VC enabled by a unique startFiltered notification is a FIFO
barrier: seeing it enabled under the manager mutex means prior handlers and
the barrier handler's own admission pass have finished. -/
private def barrier : CommandElabM Unit := do
  let id ← withVCManager fun ref => do
    let mgr ← ref.get
    let name := Name.mkSimple s!"barrier{mgr._nextVcId}"
    let (mgr, id) := mgr.addVC (← data name) {}
    ref.set mgr
    return (id, name)
  startFiltered (fun metadata => metadata.propertyName? == some id.2)
  await "notification barrier" do return (← manager).enabledVCs.contains id.1

private structure Worker where
  discharger : Discharger SmtResult
  publish : IO.Promise Unit
  published : IO.Promise Unit
  finish : IO.Promise Unit
  tasks : IO.Ref (Array SnapshotTreeTask)

private def worker (mgrId vcId dischargerId : Nat) : BaseIO Worker := do
  let publish ← IO.Promise.new
  let published ← IO.Promise.new
  let finish ← IO.Promise.new
  let tasks ← IO.mkRef #[]
  let resultPromise ← IO.Promise.new
  let startTimePromise ← IO.Promise.new
  let id : DischargerIdentifier := { managerId := mgrId, vcId, dischargerId, name := `gated }
  let mkTask := do
    let task ← BaseIO.asTask (prio := .dedicated) do
      startTimePromise.resolve 0
      let _ ← IO.wait publish.result?
      publishDischargerResult resultPromise vcManagerCh id (.unknown none 0)
      published.resolve ()
      let _ ← IO.wait finish.result?
      return (default : Language.SnapshotTree)
    tasks.modify (·.push task)
    return task
  return { publish, published, finish, tasks, discharger := {
    id, resultPromise, startTimePromise, cancelTk := ← IO.CancelToken.new,
    task := none, mkTask } }

private def cleanup (workers : Array Worker) : IO Unit := do
  -- Keep all promise owners alive until every admitted task has finished.
  for w in workers do
    w.publish.resolve ()
    w.finish.resolve ()
    w.discharger.resultPromise.resolve (.unknown none 0)
  for w in workers do
    for task in ← w.tasks.get do
      await "cleanup task" (IO.hasFinished task)

private def started (w : Worker) : BaseIO Bool :=
  IO.hasFinished w.discharger.startTimePromise.result?

private def assertPending (w : Worker) (label : String) : CommandElabM Unit := do
  check ((← w.tasks.get).isEmpty) s!"{label}: admitted while old physical worker unfinished"
  check (!(← started w)) s!"{label}: task body started early"

private def register (workers : Array Worker) : CommandElabM Unit :=
  withVCManager fun ref => do
    let mgr ← ref.get
    let (mgr, _) := mgr.addVC (← data `testVC) {} (workers.map (·.discharger))
    ref.set mgr

private def fresh : CommandElabM Unit := do
  numCoresCache.set (some 1)
  runManager
  barrier

private def earlyPublication : CommandElabM Unit := do
  fresh
  let mgr ← manager
  let a ← worker mgr._managerId mgr._nextVcId 0
  let b ← worker mgr._managerId mgr._nextVcId 1
  try
    register #[a, b]
    startAll
    await "A starts" (started a)
    a.publish.resolve ()
    await "A result accepted" do
      return (← manager)._dischargerResults.contains (a.discharger.id.vcId, 0)
    barrier
    check (((← manager).nodes[a.discharger.id.vcId]!.dischargers[1]?.bind (·.task)).isNone)
      "early publication released a physical slot"
    assertPending b "early publication"
    -- No further result or frontend notifications: original task completion
    -- alone must trigger the next admission.
    a.finish.resolve ()
    await "completion refills B" (started b)
    check (← IO.hasFinished (← a.tasks.get)[0]!) "B ran before A's task finished"
  finally
    cleanup #[a, b]
  barrier
  liftIO <| IO.println "physical capacity: early publication and completion-only refill PASS"

private def resets (publishBeforeReset : Bool) : CommandElabM Unit := do
  fresh
  let mgr ← manager
  let a ← worker mgr._managerId mgr._nextVcId 0
  let retained ← IO.mkRef #[a]
  try
    register #[a]
    startAll
    await "old A starts" (started a)
    if publishBeforeReset then
      a.publish.resolve ()
      await "old A accepted" do
        return (← manager)._dischargerResults.contains (a.discharger.id.vcId, 0)
    let mut previous := a
    for iteration in [:3] do
      let oldId := (← manager)._managerId
      if iteration == 1 then
        -- Also exercise the synchronous frontend reset path.
        runManager
      else
        reset oldId
      await "reset processed" do return (← manager)._managerId != oldId
      check (← previous.discharger.cancelTk.isSet) "reset missed abandoned cancellation token"
      let mgr ← manager
      let replacement ← worker mgr._managerId mgr._nextVcId 0
      retained.modify (·.push replacement)
      register #[replacement]
      startAll
      sendNotification .fill
      sendNotification .fill
      barrier
      assertPending replacement s!"reset {iteration}"
      check (!(← replacement.discharger.cancelTk.isSet)) "reset canceled replacement work"
      previous := replacement
    if !publishBeforeReset then
      a.publish.resolve ()
      await "stale A notification sent" (IO.hasFinished a.published.result?)
      barrier
      check ((← manager)._dischargerResults.isEmpty) "stale result was accepted"
      assertPending previous "stale result"
    a.finish.resolve ()
    await "old completion refills current manager" (started previous)
    check (← IO.hasFinished (← a.tasks.get)[0]!) "replacement ran before old task finished"
    check (!(← previous.discharger.cancelTk.isSet)) "old completion canceled replacement"
    let workers ← retained.get
    for abandoned in workers[1:3] do
      assertPending abandoned "abandoned queued worker"
  finally
    cleanup (← retained.get)
  barrier
  liftIO <| IO.println s!"physical capacity: repeated resets, cancellation, prior/stale result ({publishBeforeReset}) PASS"

private def twoSlots : CommandElabM Unit := do
  fresh
  numCoresCache.set (some 2)
  let mgr ← manager
  let a ← worker mgr._managerId mgr._nextVcId 0
  let b ← worker mgr._managerId (mgr._nextVcId + 1) 0
  let c ← worker mgr._managerId (mgr._nextVcId + 2) 0
  try
    register #[a]
    register #[b]
    startAll
    await "first of two slots" (started a)
    await "second of two slots" (started b)
    register #[c]
    startAll
    barrier
    assertPending c "two full slots"
    a.publish.resolve ()
    await "first result accepted" do
      return (← manager)._dischargerResults.contains (a.discharger.id.vcId, 0)
    barrier
    assertPending c "published result with two full slots"
    a.finish.resolve ()
    await "one physical slot refilled" (started c)
    check (← IO.hasFinished (← a.tasks.get)[0]!) "third worker ran before first finished"
    check (!(← IO.hasFinished (← b.tasks.get)[0]!)) "second gate did not retain its worker"
  finally
    cleanup #[a, b, c]
  barrier
  liftIO <| IO.println "physical capacity: two slots and one-at-a-time refill PASS"

run_cmd earlyPublication
run_cmd resets true
run_cmd resets false
run_cmd twoSlots
