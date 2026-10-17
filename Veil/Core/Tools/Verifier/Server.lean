module

public meta import Veil.Core.Tools.Verifier.Environment
public meta import Veil.Core.Tools.Verifier.Manager
public meta import Veil.Core.Tools.Verifier.Results
public meta import Std.Sync.Mutex
public meta import Veil.Util.Multiprocessing
public meta import Veil.Util.Meta

public meta section

namespace Veil.Verifier

open Lean Elab Command Std

private structure SessionState where
  manager : VCManager VCMetadata SmtResult
  driving : Bool := false
  driver : Option (Task Unit) := none
  cancelled : Bool := false
  superseded : Bool := false
  failure? : Option String := none
  cancelTk? : Option IO.CancelToken := none
  nextRequest : Nat := 0
  requests : HashMap Nat (VCMetadata → Bool) := {}
  /-- Explicit starts own their work independently of result waiters. -/
  standalone : HashSet VCId := {}

/-- One module in one document generation. No process-global current manager:
commands, result callbacks and widgets retain their own session handle. -/
structure Session where
  private state : Mutex SessionState
  source : String
  /-- Immutable registrations visible at the command snapshot holding this
  handle. Later commands may mutate the live manager, but cannot extend a
  cached earlier snapshot's registration set. -/
  private registrations : VCManager VCMetadata SmtResult

-- The binding follows command environments across section/namespace endings.
-- Local async access avoids blocking attribute handlers on their own theorem.
initialize sessionEnv : EnvExtension (Option Session) ←
  registerEnvExtension (pure none) (asyncMode := .local)
initialize nextSessionId : IO.Ref Nat ← IO.mkRef 0

private def newManager : BaseIO (VCManager VCMetadata SmtResult) := do
  let id ← nextSessionId.modifyGet fun id => (id, id + 1)
  VCManager.new (← Std.Channel.new) id

/-- Snapshot only this session. A cancelled request must never become an empty
successful result by observing a replacement module's manager. -/
def Session.snapshot (session : Session) : IO (VCManager VCMetadata SmtResult) :=
  session.state.atomically fun ref => do
    let state ← ref.get
    if let some failure := state.failure? then throw (IO.userError failure)
    if state.cancelled || (← state.cancelTk?.mapM (fun tk => (tk.isSet : IO Bool))).getD false then
      throw (IO.userError "Verification session was cancelled")
    return state.manager

private def SessionState.demand (state : SessionState) : HashSet VCId :=
  let roots := state.requests.valuesArray.foldl (fun ids filter =>
    (state.manager.matchingIds filter).fold (·.insert ·) ids) state.standalone
  state.manager.requestScope roots

/-- Fork cached command state after an edit below an unchanged #gen_spec.
Factory replay allocates fresh tasks, tokens and promises. Interactive results
survive only if their exact theorem declaration remains in this environment. -/
private def Session.fork (session : Session) (source : String) (env : Environment) :
    EIO Exception Session := do
  let old := session.registrations
  let fresh ← newManager
  let some ch := fresh.ch | throw (Exception.error Syntax.missing "Missing session result channel")
  let mut mgr := {old with
    _managerId := fresh._managerId, ch := fresh.ch, _doneWith := {}
    _dischargerResults := {}, _totalDischarged := 0, _totalSolved := 0, _countedDischargers := {}
    enabledVCs := {}, cancelledVCs := {}, factories := {}, dependencyErrors := {}, retiredDischargers := #[]
    inDegree := old.upstream.map (fun _ deps => deps.size)
    dormantVCs := old.registeredDormantVCs }
  for vcId in List.range old._nextVcId do
    let some vc := old.nodes[vcId]? | continue
    let mut ds := #[]
    for d in vc.dischargers do
      let id := {d.id with managerId := mgr._managerId, dischargerId := ds.size}
      if let some factory := old.factories[(vcId, d.id.dischargerId)]? then
        let fresh ← match ← (factory id ch).toBaseIO with
          | .ok fresh => pure fresh
          | .error ex => d.invalidated id ex
        ds := ds.push fresh
        mgr := {mgr with factories := mgr.factories.insert (vcId, id.dischargerId) factory}
      else if d.isInteractive then
        if let some (name, value) := d.theoremValue? then
          if let some (.thmInfo info) := (env.setExporting false).find? name then
            if info.value == value then
              if let .finished result ← d.status then
                let resultPromise ← IO.Promise.new
                resultPromise.resolve result
                let startTimePromise ← IO.Promise.new
                startTimePromise.resolve (← IO.monoMsNow)
                ds := ds.push {d with
                  id, cancelTk := ← IO.CancelToken.new
                  task := some (Task.pure default), resultPromise, startTimePromise
                  mkTask := pure (Task.pure default)}
      else
        ds := ds.push (← d.invalidated id (Exception.error Syntax.missing
          m!"Cannot restart VC {vc.name}: its discharger has no factory"))
    mgr := {mgr with nodes := mgr.nodes.insert vcId {vc with dischargers := ds, successful := none}}
  -- All nodes must belong to the new generation before replaying results.
  -- Replay in dependency order rather than hash-map iteration order.
  for vcId in List.range mgr._nextVcId do
    let some vc := mgr.nodes[vcId]? | continue
    for d in vc.dischargers do
      if d.isInteractive then
        if let .finished result ← d.status then mgr ← mgr.recordDischargerResult d.id result
  let fresh : Session := {state := ← Mutex.new {manager := mgr}, source, registrations := mgr}
  -- Reused command snapshots still own their original requests. Superseding
  -- the binding must not cancel those waiters; discarded snapshots release
  -- their own ownership. Standalone starts have no retained snapshot owner.
  session.state.atomically fun ref => do
    let state ← ref.get
    let state := {state with
      superseded := true, standalone := {}
      manager := ← state.manager.reconcileFinished}
    let wanted := state.demand
    let manager ← state.manager.cancelUnneeded wanted
    ref.set {state with manager := manager.enableIds wanted}
  return fresh

/-- The environment binding is immutable even when a cached #gen_spec handle
contains completed work. Async callbacks capture this handle before spawning;
an old callback never resolves against a newer document's session. -/
def getSession [Monad m] [MonadEnv m] [MonadFileMap m] [MonadError m] [MonadResolveName m]
    [MonadLiftT IO m] [MonadLiftT (EIO Exception) m] : m Session := do
  let some session := sessionEnv.getState (← getEnv) | throwError "VC manager has not been initialized; use #gen_spec first"
  let source := (← getFileMap).source
  let superseded ← (session.state.atomically fun ref => return (← ref.get).superseded : IO Bool)
  if source == session.source && !superseded then return session
  let fresh ← session.fork source (← getEnv)
  modifyEnv (sessionEnv.setState · (some fresh))
  return fresh

def isDoesNotThrow (m : VCMetadata) : Bool := m.propertyName? == some `doesNotThrow

/-- Process-wide physical worker budget, shared by every module and document
generation. Lock order is session, then pool; workers never acquire the pool.
Keep superseded tasks here until they actually exit, even after publication. -/
initialize solverTasks : Mutex (Array SnapshotTreeTask) ← Mutex.new #[]

private def fillAvailableSlotsLocked (mgr : VCManager VCMetadata SmtResult)
    : BaseIO (VCManager VCMetadata SmtResult) := solverTasks.atomically fun ref => do
  let mut tasks ← (← ref.get).filterM fun task => return !(← IO.hasFinished task)
  let mut mgr := mgr
  let ready := (← mgr.readyTasks).take ((← getNumCores) - tasks.size)
  for (vc, discharger) in ready do
    let discharger ← discharger.run
    if let some task := discharger.task then tasks := tasks.push task
    let vc := {vc with dischargers := vc.dischargers.set! discharger.id.dischargerId discharger}
    mgr := {mgr with nodes := mgr.nodes.insert vc.uid vc}
  ref.set tasks
  return mgr

/-- Execution and cancellation use the same ownership closure. This is also
refreshed after registration, so late matching VCs cannot leave waiters stuck. -/
private def SessionState.refreshDemand (state : SessionState) : BaseIO SessionState := do
  let wanted := state.demand
  let manager ← state.manager.cancelUnneeded wanted
  let manager ← (manager.enableIds wanted).restartCancelled
  return {state with manager}

/-- One bounded-lifetime driver per active session. It exits when enabled work
finishes and is restarted by a later start request. All transitions and task
spawns are BaseIO under the session mutex, so interruption cannot tear them. -/
private partial def Session.drive (session : Session) : BaseIO Unit := do
  let continueDriving ← session.state.atomically fun ref => do
    let mut state ← ref.get
    let mut mgr := state.manager
    if let .error message := mgr.validateRegistrations then
      mgr ← mgr.cancelUnneeded {}
      ref.set {state with manager := mgr, failure? := some message, driving := false, driver := none}
      return false
    if state.cancelled || (← state.cancelTk?.mapM IO.CancelToken.isSet).getD false then
      mgr.cancelAllDischargers
      ref.set {state with cancelled := true, driving := false, driver := none}
      return false
    let some ch := mgr.ch | do
      mgr ← mgr.cancelUnneeded {}
      ref.set {state with
        manager := mgr, failure? := some "Missing session result channel"
        driving := false, driver := none}
      return false
    while true do
      let some notification ← ch.tryRecv | break
      match notification with
      | .dischargerResult id result => mgr ← mgr.recordDischargerResult id result
      | .startAll => state := {state with standalone := mgr.nodes.fold (fun ids id _ => ids.insert id) state.standalone}
      | .startFiltered filter => state := {state with standalone := (mgr.matchingIds filter).fold (·.insert ·) state.standalone}
      | .fill => pure ()
      | .reset id =>
        if id == mgr._managerId then state := {state with cancelled := true}
    if state.cancelled then
      mgr.cancelAllDischargers
      ref.set {state with manager := mgr, driving := false, driver := none}
      return false
    mgr ← mgr.reconcileFinished
    state ← {state with manager := mgr}.refreshDemand
    mgr := state.manager
    if let .error message := mgr.validateEnabled then
      mgr ← mgr.cancelUnneeded {}
      ref.set {state with manager := mgr, failure? := some message, driving := false, driver := none}
      return false
    mgr ← fillAvailableSlotsLocked mgr
    let pending := mgr.nodes.toArray.any fun (id, _) =>
      mgr.enabledVCs.contains id && !mgr._doneWith.contains id && !mgr.dormantVCs.contains id
    let active := pending || (← mgr.inFlightCount) > 0
    ref.set {state with manager := mgr, driving := active, driver := if active then state.driver else none}
    return active
  if continueDriving then
    IO.sleep 10
    session.drive

private def Session.start (session : Session) (standalone? : Option (VCMetadata → Bool) := none) : IO Unit :=
  session.state.atomically fun ref => do
    let mut state ← ref.get
    if state.cancelled then return
    if let .error message := state.manager.validateRegistrations then throw (IO.userError message)
    if let some filter := standalone? then
      state := {state with standalone := (state.manager.matchingIds filter).fold (·.insert ·) state.standalone}
    -- Validate before touching shared one-shot resources. A rejected start
    -- must not poison registrations which were never enabled.
    let candidate := {state.manager with enabledVCs := {}}.enableIds state.demand
    if let .error message := candidate.validateEnabled then throw (IO.userError message)
    state ← state.refreshDemand
    state := {state with failure? := none}
    let pending := state.manager.nodes.toArray.any fun (id, _) =>
      state.manager.enabledVCs.contains id && !state.manager._doneWith.contains id && !state.manager.dormantVCs.contains id
    unless state.driving || !pending do
      let task ← session.drive.asTask (prio := .dedicated)
      state := {state with driving := true, driver := some task}
    ref.set state

def Session.withManager [Monad m] [MonadEnv m] [MonadResolveName m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadLiftT (ST IO.RealWorld) m] [MonadFinally m] [MonadError m]
    (session : Session) (f : IO.Ref (VCManager VCMetadata SmtResult) → m α) : m α := do
  let (result, registrations) ← session.state.atomically fun ref => do
    let state ← ref.get
    if state.cancelled then throwError "Verification session was cancelled"
    let managerRef ← IO.mkRef state.manager
    let result ← f managerRef
    let manager ← managerRef.get
    ref.set {state with manager}
    return (result, manager)
  -- Updating an explicitly captured older module must not rebind the current
  -- module. Old command environments still receive their own checkpoint.
  if let some current := sessionEnv.getState (← getEnv) then
    if current.registrations._managerId == session.registrations._managerId then
      modifyEnv (sessionEnv.setState · (some {session with registrations}))
  session.start
  return result

def withVCManager (f : IO.Ref (VCManager VCMetadata SmtResult) → CommandElabM α) : CommandElabM α := do
  (← getSession).withManager f

def sendNotification (notification : ManagerNotification VCMetadata SmtResult) : CommandElabM Unit := do
  let session ← getSession
  session.state.atomically fun ref => do
    let state ← ref.get
    let some ch := state.manager.ch | throwError "Missing session result channel"
    let _ ← ch.send notification
    unless state.driving || state.cancelled do
      let task ← session.drive.asTask (prio := .dedicated)
      ref.set {state with driving := true, driver := some task}

def reset (managerId : ManagerId) : CommandElabM Unit := sendNotification (.reset managerId)
def startAll : CommandElabM Unit := do (← getSession).start (some (fun _ => true))
def startFiltered (filter : VCMetadata → Bool) : CommandElabM Unit := do (← getSession).start (some filter)

/-- Create a new module session without abandoning other modules' requests. -/
def runManager (cancelTk? : Option IO.CancelToken := none) : CommandElabM Unit := do
  let manager ← newManager
  let session : Session := {
    state := ← Mutex.new {manager, cancelTk?}
    source := (← getFileMap).source, registrations := manager}
  modifyEnv (sessionEnv.setState · (some session))

private def Session.acquire (session : Session) (filter : VCMetadata → Bool) : IO Nat :=
  session.state.atomically fun ref => do
    let state ← ref.get
    if state.cancelled then throw (IO.userError "Verification session was cancelled")
    if let .error message := state.manager.validateRegistrations then throw (IO.userError message)
    let candidate := {state with
      nextRequest := state.nextRequest + 1
      requests := state.requests.insert state.nextRequest filter}
    -- Publish only valid demand. An already-running driver must never see a
    -- request which startup will reject and cancel other requests' work.
    let manager := {state.manager with enabledVCs := {}}.enableIds candidate.demand
    if let .error message := manager.validateEnabled then throw (IO.userError message)
    ref.set candidate
    return state.nextRequest

/-- Cancelling one request cancels only work no other live request needs.
Snapshot leaf tasks carry no cancellation token: duplicate registrations by
concurrent waiters therefore cannot cancel one another's solver work. -/
private def Session.release (session : Session) (request : Nat) : BaseIO Unit :=
  session.state.atomically fun ref => do
    let state ← ref.get
    unless state.requests.contains request do return
    let requests := state.requests.erase request
    -- Preserve completed results before withdrawing ownership. Release never
    -- rebuilds revoked attempts just to cancel them again.
    let state := {state with requests, manager := ← state.manager.reconcileFinished}
    let wanted := state.demand
    let manager ← state.manager.cancelUnneeded wanted
    ref.set {state with manager := manager.enableIds wanted}

private def awaitFilteredWithLogging (session : Session) (filter : VCMetadata → Bool)
    : CommandElabM (VerificationResults VCMetadata SmtResult) := do
  let mut registered : HashSet DischargerIdentifier := {}
  while true do
    Core.checkInterrupted |> liftCoreM
    let mgr ← session.snapshot
    for (_, vc) in mgr.nodes do
      if filter vc.metadata then
        for d in vc.dischargers do
          if let some task := d.task then
            unless registered.contains d.id do
              Command.logSnapshotTask {stx? := none, cancelTk? := none, task}
              registered := registered.insert d.id
    if mgr.isDoneFiltered filter then return ← liftCoreM (mgr.toResults filter)
    IO.sleep 10
  panic! "unreachable"

def runFilteredAsync (filter : VCMetadata → Bool)
    (callback : VerificationResults VCMetadata SmtResult → CommandElabM Unit) : CommandElabM Unit := do
  let session ← getSession
  let request ← session.acquire filter
  let handedOff ← IO.mkRef false
  try
    session.start
    let cancelTk ← IO.CancelToken.new
    let wrapped ← Command.wrapAsyncAsSnapshot (fun () => do
      let result ← awaitFilteredWithLogging session filter
      callback result) cancelTk
    let task ← (do
      let snapshot ← wrapped ()
      session.release request
      return snapshot).asTask (prio := .dedicated)
    -- The BaseIO task now owns release, even if snapshot logging is interrupted.
    handedOff.set true
    Command.logSnapshotTask {stx? := none, cancelTk? := cancelTk, task}
  finally
    unless ← handedOff.get do session.release request

def waitFilteredSync (filter : VCMetadata → Bool) : CommandElabM (VerificationResults VCMetadata SmtResult) := do
  let session ← getSession
  let request ← session.acquire filter
  try
    session.start
    let results ← awaitFilteredWithLogging session filter
    return results
  finally
    session.release request

private def ensureExistingTheoremMatches (fullName : Name) (statement : Expr) : TermElabM Unit := do
  let some info := (← getEnv).find? fullName
    | return
  unless ← Meta.isDefEq info.type statement do
    throwError "cannot generate VC theorem `{fullName}` because a declaration with that name already exists with a different type"

private def addProvenVCTheorem (vc : VerificationCondition VCMetadata SmtResult)
    (witness : Witness) : CommandElabM Unit := do
  liftTermElabM do
    let fullName := (← getCurrNamespace).append vc.name
    let statement ← vc.toVCStatement.type
    if (← getEnv).contains fullName then
      ensureExistingTheoremMatches fullName statement
      return
    let witness ← instantiateMVars witness
    let _ ← addVeilTheorem vc.name statement witness
    return ()

/-- Add theorem declarations for all already-proven VCs matching `filter`.

This must run on the command elaboration thread, not in the manager task: it
mutates the current Lean environment by adding theorem constants whose proofs
are the witnesses returned by successful dischargers. Declarations are added in
the manager DAG's dependency order so downstream proof terms can refer to
upstream VC theorem constants. -/
def addProvenTheoremsInDependencyOrder (filter : VCMetadata → Bool) : CommandElabM Unit := do
  let mgr ← (← getSession).snapshot
  for vcId in mgr.vcIdsInDependencyOrder filter do
    if let some (vc, witness) := mgr.provenWitness? vcId then
      addProvenVCTheorem vc witness

end Veil.Verifier
