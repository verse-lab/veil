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

/-- The handle follows saved environments, asynchronous commands and CoreM getters.
It is deliberately not persistent across imports. -/
initialize vcManagerExt : EnvExtension (HashMap Name VCManagerEnvironment) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/-- Completed interactive results belong to an immutable Lean checkpoint, keyed
by globally unique runtime generation. They never enter the shared runtime. -/
abbrev InteractiveRegistrations := Array (Discharger SmtResult × DischargerResult SmtResult)
initialize interactiveRegistrationsExt : EnvExtension (HashMap ManagerId InteractiveRegistrations) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/-- Remove direct runtime access from detached workers. Historical realization
contexts can still retain owners; source-snapshot cleanup releases abandoned
worker captures without changing Lean declaration realization. -/
def clearVerifierRuntime (env : Environment) : Environment :=
  interactiveRegistrationsExt.setState (vcManagerExt.setState env {}) {}

def getVCManagerOwner [Monad m] [MonadEnv m] [MonadError m] : m VCManagerEnvironment := do
  let key := ((← localEnv.get).currentModule.map (·.name)).getD .anonymous
  let some owner := (vcManagerExt.getState (← getEnv))[key]?
    | throwError "verification manager has not been prepared"
  return owner

def withVCManager (f : IO.Ref (VCManager VCMetadata SmtResult) → CommandElabM α) : CommandElabM α := do
  let owner ← getVCManagerOwner
  owner.manager.atomically fun ref => do
    if ← owner.cancelTk.isSet then
      throwError "verification interrupted: specification owner was canceled"
    f ref

/-- Capture the caller's proof checkpoint once, while allowing shared automatic
results to advance. Safe for CoreM/widget refreshes in a different context. -/
def captureVCManager [Monad m] [MonadEnv m] [MonadError m] [MonadLiftT BaseIO m] :
    m (BaseIO (VCManager VCMetadata SmtResult)) := do
  let owner ← getVCManagerOwner
  let id ← liftM <| owner.manager.atomically (m := BaseIO) fun ref => return (← ref.get)._managerId
  let registrations := (interactiveRegistrationsExt.getState (← getEnv))[id]?.getD #[]
  return do
    let mgr ← owner.manager.atomically (m := BaseIO) fun ref => ref.get
    mgr.withInteractiveResults registrations

def readVCManager [Monad m] [MonadEnv m] [MonadError m] [MonadLiftT BaseIO m] :
    m (VCManager VCMetadata SmtResult) := do
  liftM (← captureVCManager)

/-- One lock protects the physical pool and active-owner registry. Its lock is
always taken before an owner's manager mutex. Frontend mutations only take the
owner mutex, and enqueue afterwards. No idle owner is retained here. -/
structure DispatcherState where
  nextId : Nat := 0
  owners : HashMap ManagerId VCManagerEnvironment := {}
  tasks : Array SnapshotTreeTask := #[]
deriving Inhabited

initialize dispatcher : Std.Mutex DispatcherState ← Std.Mutex.new {}

private def newManagerLocked (ref : IO.Ref DispatcherState) : BaseIO (VCManager VCMetadata SmtResult) := do
  let st ← ref.get
  ref.set { st with nextId := st.nextId + 1 }
  VCManager.new vcManagerCh (currentManagerId := st.nextId)

/-- Explicit reset owns worker cancellation; observers do not. -/
def cancelAbandonedWork (mgr : VCManager VCMetadata SmtResult) : BaseIO Unit :=
  mgr.cancelAllDischargers

private def fillOwnerLocked (pool : IO.Ref DispatcherState) (owner : VCManagerEnvironment)
    : BaseIO Bool := owner.manager.atomically fun ref => do
  let mut mgr ← ref.get
  if ← owner.cancelTk.isSet then
    cancelAbandonedWork mgr
    return false
  let numCores ← getNumCores
  let ready := (← mgr.readyTasks).take (numCores - (← pool.get).tasks.size)
  for (vc, discharger) in ready do
    let discharger' ← discharger.run
    if let some task := discharger'.task then
      pool.modify fun st => { st with tasks := st.tasks.push task }
      BaseIO.chainTask task (fun _ => discard <| vcManagerCh.send .fill)
    let vc' := { vc with dischargers := vc.dischargers.set! discharger.id.dischargerId discharger' }
    mgr := { mgr with nodes := mgr.nodes.insert vc.uid vc' }
  ref.set mgr
  -- Results can precede physical completion. Keep the owner until both its
  -- ready work and outstanding publications have drained; the physical pool
  -- separately retains unfinished tasks even after this owner retires.
  if !(← mgr.readyTasks).isEmpty then return true
  for (_, vc) in mgr.nodes do
    for d in vc.effectiveDischargers do
      if d.task.isSome && !mgr._dischargerResults.contains (vc.uid, d.id.dischargerId) then
        return true
  return false

private def handleNotificationLocked (pool : IO.Ref DispatcherState)
  (notification : ManagerNotification VCMetadata SmtResult)
    (registrations : InteractiveRegistrations := #[]) : BaseIO Unit := do
  let st ← pool.get
  let tasks ← st.tasks.filterM fun task => return !(← IO.hasFinished task)
  pool.set { st with tasks }
  let id? := match notification with
    | .dischargerResult id _ => some id.managerId
    | .reset id | .startAll id | .startFiltered id _ => some id
    | .fill => none
  if let some id := id? then
    if let some owner := (← pool.get).owners[id]? then
      owner.manager.atomically fun ref => do
        let mgr ← ref.get
        if mgr._managerId != id then return
        match notification with
        | .dischargerResult id res => ref.set (← mgr.recordDischargerResult id res)
        | .startAll _ =>
          ref.set (mgr.enableMatchingFromView (← mgr.withInteractiveResults registrations) (fun _ => true))
        | .startFiltered _ filter =>
          ref.set (mgr.enableMatchingFromView (← mgr.withInteractiveResults registrations) filter)
        | .reset _ =>
          cancelAbandonedWork mgr
          ref.set (← newManagerLocked pool)
        | .fill => pure ()
  let owners := (← pool.get).owners
  for (id, owner) in owners do
    let currentId ← owner.manager.atomically fun ref => return (← ref.get)._managerId
    if currentId != id || !(← fillOwnerLocked pool owner) then
      pool.modify fun st => { st with owners := st.owners.erase id }


private def handleNotification (notification : ManagerNotification VCMetadata SmtResult) : BaseIO Unit := do
  dispatcher.atomically fun pool => handleNotificationLocked pool notification
  frontendNotification.notifyAll

private def startDispatcher : BaseIO Unit :=
  vcServerStarted.atomically fun ref => do
    unless ← ref.get do
      -- One shared asynchronous receiver, no dedicated thread per owner.
      discard <| vcManagerCh.forAsync handleNotification
      ref.set true

/-- Apply frontend requests synchronously under the pool lock. Registration and
handling are one transaction: retiring an idle owner cannot discard a queued
start. Worker publications still use the shared asynchronous channel. -/
def enqueue (owner : VCManagerEnvironment)
    (notification : ManagerNotification VCMetadata SmtResult)
    (registrations : InteractiveRegistrations := #[]) : BaseIO Unit := do
  dispatcher.atomically fun pool => do
    let id ← owner.manager.atomically fun ref => return (← ref.get)._managerId
    let requestedId := match notification with
      | .reset requested | .startAll requested | .startFiltered requested _ => requested
      | .dischargerResult requested _ => requested.managerId
      | .fill => id
    if requestedId != id then return
    pool.modify fun st => { st with owners := st.owners.insert id owner }
    handleNotificationLocked pool notification registrations
  frontendNotification.notifyAll

def sendNotification (notification : ManagerNotification VCMetadata SmtResult) : CommandElabM Unit := do
  let owner ← getVCManagerOwner
  let id ← owner.manager.atomically fun ref => return (← ref.get)._managerId
  let registrations := (interactiveRegistrationsExt.getState (← getEnv))[id]?.getD #[]
  enqueue owner notification registrations

def reset (managerId : ManagerId) : CommandElabM Unit := do
  let currentId ← (← getVCManagerOwner).manager.atomically fun ref => return (← ref.get)._managerId
  sendNotification (.reset managerId)
  if currentId == managerId then
    modifyEnv fun env => interactiveRegistrationsExt.modifyState env (·.erase managerId)

def startAll : CommandElabM Unit := do
  let managerId := (← readVCManager)._managerId
  sendNotification (.startAll managerId)

private def requestFiltered (filter : VCMetadata → Bool) : CommandElabM ManagerId := do
  let managerId := (← readVCManager)._managerId
  sendNotification (.startFiltered managerId filter)
  return managerId

def startFiltered (filter : VCMetadata → Bool) : CommandElabM Unit := do
  discard <| requestFiltered filter

def isDoesNotThrow (m : VCMetadata) : Bool := m.propertyName? == some `doesNotThrow

/-- Prepare an independent owner. Completed snapshot registration gives the
creating command cancellation ownership without an infinite snapshot task.
Cancellation is checked before each admission, including completion refills. -/
def runManager (cancelTk? : Option IO.CancelToken := none) : CommandElabM Unit := do
  -- Keep the execution token separate even when callers supply the frontend's
  -- origin token; retaining that token in `owner` would recreate the cycle.
  let cancelTk ← IO.CancelToken.new
  if let some supplied := cancelTk? then supplied.onSet cancelTk.set
  let mgr ← liftM <| dispatcher.atomically newManagerLocked
  let owner := { manager := ← Std.Mutex.new mgr, errors := ← IO.mkRef #[], cancelTk : VCManagerEnvironment }
  let key := ((← localEnv.get).currentModule.map (·.name)).getD .anonymous
  if let some previous := (vcManagerExt.getState (← getEnv))[key]? then
    let previousId ← previous.manager.atomically fun ref => return (← ref.get)._managerId
    modifyEnv fun env => interactiveRegistrationsExt.modifyState env (·.erase previousId)
  modifyEnv fun env => vcManagerExt.modifyState env (·.insert key owner)
  -- The frontend's command token owns this runtime's lifetime. It survives
  -- wrappers such as #guard_msgs that consume child snapshot tasks, and must
  -- never be retained by the owner or detached workers. Releasing/canceling the
  -- originating command invalidates saved bare environments as well, breaking
  -- cycles through declaration realization contexts without changing them.
  let originLifetime ← match (← read).cancelTk? with
    | some token => pure token
    | none => IO.CancelToken.new
  originLifetime.onSet do
    owner.cancelTk.set
    discard <| BaseIO.asTask do
      dispatcher.atomically fun pool => do
        owner.manager.atomically fun ref => do
          let mgr ← ref.get
          cancelAbandonedWork mgr
          ref.set (← newManagerLocked pool)
          pool.modify fun st => { st with owners := st.owners.erase mgr._managerId }
        handleNotificationLocked pool .fill
      frontendNotification.notifyAll
  -- A child marker grants cancellation of only this owner. Without a frontend
  -- token, the marker also supplies the origin lifetime for tool callers.
  let markerToken := if (← read).cancelTk?.isSome then cancelTk else originLifetime
  Command.logSnapshotTask { stx? := none, cancelTk? := some markerToken, task := .pure default }
  startDispatcher

/-- Preserve diagnostics, traces, and asynchronous children without granting an
observer cancellation ownership. `SnapshotTask.cancelRec` traverses children
when their tasks finish even if the parent token is `none`, so stripping only
the root token is insufficient. Mapping is lazy in pending child tasks. -/
private partial def observerSnapshotTree (tree : Language.SnapshotTree) : Language.SnapshotTree :=
  { tree with children := tree.children.map fun child =>
      { child with
        cancelTk? := none
        task := child.task.map observerSnapshotTree (sync := true) } }

/-- Register newly started tasks matching this observer, using its own seen set.
Reading manager state instead of consuming a channel lets overlapping observers
see the same tasks, including work started before they began waiting. -/
def logPendingDischargerTasks (mgr : VCManager VCMetadata SmtResult)
    (filter : VCMetadata → Bool) (registered : HashSet DischargerIdentifier)
    : CommandElabM (HashSet DischargerIdentifier) := do
  let mut registered := registered
  for (_, vc) in mgr.nodes do
    if !filter vc.metadata then continue
    for discharger in vc.effectiveDischargers do
      if registered.contains discharger.id then continue
      if let some task := discharger.task then
        Command.logSnapshotTask {
          stx? := none
          cancelTk? := none
          task := task.map observerSnapshotTree (sync := true) }
        registered := registered.insert discharger.id
  return registered

/-- Poll for discharger tasks from the manager and register them with `logSnapshotTask`.
    Waits until all VCs matching the filter are done, then returns the results.
    Fails if the captured manager generation has been replaced.
    This enables profiler trace propagation by registering tasks on the calling thread. -/
private def awaitFilteredWithLogging (managerId : ManagerId) (filter : VCMetadata → Bool)
    : CommandElabM (VerificationResults VCMetadata SmtResult) := do
  let owner ← getVCManagerOwner
  let mut registered := HashSet.emptyWithCapacity
  while true do
    liftCoreM Core.checkInterrupted
    if ← owner.cancelTk.isSet then
      enqueue owner .fill
      throwError "verification interrupted: specification owner was canceled"
    -- Surface manager-loop errors where the user is looking; the loop itself
    -- cannot log to the editor (it is not registered with `logSnapshotTask`).
    for err in ← (← getVCManagerOwner).errors.modifyGet fun errs => (errs, #[]) do
      logWarning m!"VC manager loop error: {err}"
    -- Snapshot under the lock, render outside it (`toResults` pretty-prints).
    let mgr ← readVCManager
    if mgr._managerId != managerId then
      throwError "verification interrupted: VC manager generation {managerId} was replaced by {mgr._managerId}"
    registered ← logPendingDischargerTasks mgr filter registered
    if mgr.isDoneFiltered filter then
      let results ← liftCoreM (mgr.toResults filter)
      liftCoreM Core.checkInterrupted
      return results
    IO.sleep 10
  panic! "unreachable"

/-- Start VCs matching the filter and run the callback asynchronously when done.
Uses `wrapAsyncAsSnapshot` so that errors from the callback are reported to the user.
This task also polls for discharger tasks from the manager and registers them with
`logSnapshotTask`, enabling profiler trace propagation.
Note: Widget display does not work in the callback since it runs in an async context. -/
def runFilteredAsync (filter : VCMetadata → Bool)
    (callback : VerificationResults VCMetadata SmtResult → CommandElabM Unit) : CommandElabM Unit := do
  let managerId ← requestFiltered filter
  let cancelTk ← IO.CancelToken.new
  let wrappedTask ← Command.wrapAsyncAsSnapshot (fun () => do
    let results ← awaitFilteredWithLogging managerId filter
    liftCoreM Core.checkInterrupted
    callback results) cancelTk
  let task ← (wrappedTask ()).asTask (prio := .dedicated)
  Command.logSnapshotTask { stx? := none, cancelTk? := cancelTk, task := task }

/-- Start VCs matching the filter and wait synchronously for completion.
Returns the results on the main thread, allowing widget display.
This also polls for discharger tasks from the manager and registers them with
`logSnapshotTask`, enabling profiler trace propagation.
Warning: This blocks the elaborator until all matching VCs complete. -/
def waitFilteredSync (filter : VCMetadata → Bool) : CommandElabM (VerificationResults VCMetadata SmtResult) := do
  let managerId ← requestFiltered filter
  awaitFilteredWithLogging managerId filter

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
  let mgr ← readVCManager
  for vcId in mgr.vcIdsInDependencyOrder filter do
    if let some (vc, witness) := mgr.provenWitness? vcId then
      addProvenVCTheorem vc witness

end Veil.Verifier
