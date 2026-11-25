module

public meta import Veil.Core.Tools.Verifier.Environment
public meta import Veil.Core.Tools.Verifier.Manager
public meta import Veil.Core.Tools.Verifier.Results
public meta import Std.Sync.Mutex
public meta import Veil.Util.Multiprocessing
public meta import Veil.Util.Meta

/- Each source owns a manager; the dispatcher shares physical capacity across
owners. A worker publishes its result promise, the manager later accepts its
channel notification, and its task can finish later still. Only task exit frees
physical capacity. Interactive proofs are projected from the caller's checkpoint. -/

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

private def managerKey [Monad m] [MonadEnv m] : m Name := do
  return ((← localEnv.get).currentModule.map (·.name)).getD .anonymous

private def getVCManagerEntry [Monad m] [MonadEnv m] [MonadError m] : m (Name × VCManagerEnvironment) := do
  let key ← managerKey
  let some owner := (vcManagerExt.getState (← getEnv))[key]?
    | throwError "verification manager has not been prepared"
  return (key, owner)

def getVCManagerOwner [Monad m] [MonadEnv m] [MonadError m] : m VCManagerEnvironment :=
  Prod.snd <$> getVCManagerEntry

/-- An owner closes when the command that prepared it is re-elaborated, or when
both of its lifetime holders (child snapshot and info-tree leaf) are dropped. -/
def ownerCanceledMessage : String :=
  "verification interrupted: specification owner was canceled (its preparing command was re-elaborated, or its snapshot and info tree were dropped)"

def withVCManager (f : IO.Ref (VCManager VCMetadata SmtResult) → CommandElabM α) : CommandElabM α := do
  let owner ← getVCManagerOwner
  owner.manager.atomically fun ref => do
    if ← owner.cancelTk.isSet then
      throwError ownerCanceledMessage
    f ref

private def captureOwner [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (owner : VCManagerEnvironment) :
    m (BaseIO (VCManager VCMetadata SmtResult)) := do
  let id ← liftM <| owner.manager.atomically (m := BaseIO) fun ref => return (← ref.get)._managerId
  let registrations := (interactiveRegistrationsExt.getState (← getEnv))[id]?.getD #[]
  return do
    let mgr ← owner.manager.atomically (m := BaseIO) fun ref => ref.get
    mgr.withInteractiveResults registrations

/-- Capture the caller's proof checkpoint once, while allowing shared automatic
results to advance. Safe for CoreM/widget refreshes in a different context. -/
def captureVCManager [Monad m] [MonadEnv m] [MonadError m] [MonadLiftT BaseIO m] :
    m (BaseIO (VCManager VCMetadata SmtResult)) := do
  captureOwner (← getVCManagerOwner)

def readVCManager [Monad m] [MonadEnv m] [MonadError m] [MonadLiftT BaseIO m] :
    m (VCManager VCMetadata SmtResult) := do
  liftM (← captureVCManager)

/-- The caller's current generation, without projecting interactive proofs. -/
private def currentManagerId (owner : VCManagerEnvironment) : CommandElabM ManagerId :=
  owner.manager.atomically fun ref => return (← ref.get)._managerId

/-- One lock protects the physical pool and active-owner registry. Its lock is
always taken before an owner's manager mutex. Frontend mutations only take the
owner mutex, then apply their request. No idle owner is retained here. -/
structure DispatcherState where
  nextId : Nat := 0
  owners : HashMap ManagerId VCManagerEnvironment := {}
  physicalTasks : Array SnapshotTreeTask := #[]
deriving Inhabited

initialize dispatcher : Std.Mutex DispatcherState ← Std.Mutex.new {}

private def newManagerLocked (ref : IO.Ref DispatcherState) : BaseIO (VCManager VCMetadata SmtResult) := do
  let st ← ref.get
  ref.set { st with nextId := st.nextId + 1 }
  VCManager.new vcManagerCh (currentManagerId := st.nextId)

/-- Start available work. Return whether this owner still needs notification
routing for ready work or unaccepted results; its physical tasks are retained
separately even when the owner retires. -/
private def fillOwnerLocked (pool : IO.Ref DispatcherState) (owner : VCManagerEnvironment)
    : BaseIO Bool := owner.manager.atomically fun ref => do
  let mut mgr ← ref.get
  if ← owner.cancelTk.isSet then
    mgr.cancelAllDischargers
    return false
  let numCores ← getNumCores
  let ready := mgr.readyTasks.take (numCores - (← pool.get).physicalTasks.size)
  for (vc, discharger) in ready do
    let discharger' ← discharger.run
    if let some task := discharger'.task then
      pool.modify fun st => { st with physicalTasks := st.physicalTasks.push task }
      BaseIO.chainTask task (fun _ => discard <| vcManagerCh.send .fill)
    let vc' := { vc with dischargers := vc.dischargers.set! discharger.id.dischargerId discharger' }
    mgr := { mgr with nodes := mgr.nodes.insert vc.uid vc' }
  ref.set mgr
  -- Results can precede physical completion. Keep the owner until both its
  -- ready work and outstanding publications have drained; the physical pool
  -- separately retains unfinished tasks even after this owner retires.
  if !mgr.readyTasks.isEmpty then return true
  for (_, vc) in mgr.nodes do
    for d in vc.effectiveDischargers do
      if d.task.isSome && !mgr._dischargerResults.contains (vc.uid, d.id.dischargerId) then
        return true
  return false

private def handleNotificationLocked (pool : IO.Ref DispatcherState)
  (notification : ManagerNotification VCMetadata SmtResult)
    (registrations : InteractiveRegistrations := #[]) : BaseIO Unit := do
  let st ← pool.get
  let physicalTasks ← st.physicalTasks.filterM fun task => return !(← IO.hasFinished task)
  pool.set { st with physicalTasks }
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
          mgr.cancelAllDischargers
          ref.set (← newManagerLocked pool)
        | .fill => pure ()
  let owners := (← pool.get).owners
  for (id, owner) in owners do
    let currentId ← owner.manager.atomically fun ref => return (← ref.get)._managerId
    if currentId != id || !(← fillOwnerLocked pool owner) then
      pool.modify fun st => { st with owners := st.owners.erase id }


private def handleNotification (notification : ManagerNotification VCMetadata SmtResult) : BaseIO Unit := do
  dispatcher.atomically fun pool => handleNotificationLocked pool notification

private def startDispatcher : BaseIO Unit :=
  vcServerStarted.atomically fun ref => do
    unless ← ref.get do
      -- One shared asynchronous receiver, no dedicated thread per owner.
      discard <| vcManagerCh.forAsync handleNotification
      ref.set true

/-- Apply frontend requests synchronously under the pool lock. Registration and
handling are one transaction: retiring an idle owner cannot discard a queued
start. Worker publications still use the shared asynchronous channel. -/
def applyFrontendRequest (owner : VCManagerEnvironment)
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

private def applyOwnerRequest (owner : VCManagerEnvironment) (generation : ManagerId)
    (notification : ManagerNotification VCMetadata SmtResult) : CommandElabM Unit := do
  let registrations := (interactiveRegistrationsExt.getState (← getEnv))[generation]?.getD #[]
  applyFrontendRequest owner notification registrations

def applyCurrentRequest (notification : ManagerNotification VCMetadata SmtResult) : CommandElabM Unit := do
  let owner ← getVCManagerOwner
  applyOwnerRequest owner (← currentManagerId owner) notification

def reset (managerId : ManagerId) : CommandElabM Unit := do
  let (key, owner) ← getVCManagerEntry
  let currentId ← currentManagerId owner
  applyOwnerRequest owner currentId (.reset managerId)
  if currentId == managerId then
    modifyEnv fun env => vcManagerExt.modifyState (interactiveRegistrationsExt.modifyState env (·.erase managerId))
      (·.modify key ({ · with publication? := none }))

def startAll : CommandElabM Unit := do
  let owner ← getVCManagerOwner
  let managerId ← currentManagerId owner
  applyOwnerRequest owner managerId (.startAll managerId)

private def requestFiltered (filter : VCMetadata → Bool) (publish := false) : CommandElabM ManagerId := do
  let (key, owner) ← getVCManagerEntry
  let managerId ← owner.manager.atomically fun ref => do
    let mgr ← ref.get
    if publish then
      let previous := owner.publication?.filter (·.1 == mgr._managerId)
      let ids := mgr.nodes.fold (init := previous.map Prod.snd |>.getD {}) fun ids id vc =>
        if filter vc.metadata then ids.insert id else ids
      modifyEnv fun env => vcManagerExt.modifyState env
        (·.insert key { owner with publication? := some (mgr._managerId, ids) })
    return mgr._managerId
  applyOwnerRequest owner managerId (.startFiltered managerId filter)
  return managerId

def startFiltered (filter : VCMetadata → Bool) : CommandElabM Unit := do
  discard <| requestFiltered filter

def isDoesNotThrow (m : VCMetadata) : Bool := m.propertyName? == some `doesNotThrow

/-- Keeps the lifetime marker in the creating command's info tree even when a
wrapper such as `#guard_msgs` consumes its child snapshot tasks. It must not be
stored in the environment or runtime: deferred workers can retain historical
environments through Lean's declaration realization contexts. -/
private structure ManagerLifetimeInfo where
  token : IO.CancelToken
  deriving TypeName

/-- Prepare an independent owner tied to the creating command's snapshots.
The frontend's `Context.cancelTk?` also cancels parsing of later commands, so it
does not own the lifetime of this command's reusable environment. -/
def runManager (cancelTk? : Option IO.CancelToken := none) : CommandElabM Unit := do
  let cancelTk ← IO.CancelToken.new
  let mgr ← liftM <| dispatcher.atomically newManagerLocked
  let owner := { manager := ← Std.Mutex.new mgr, errors := ← IO.mkRef #[], cancelTk : VCManagerEnvironment }
  let key ← managerKey
  if let some previous := (vcManagerExt.getState (← getEnv))[key]? then
    let previousId ← previous.manager.atomically fun ref => return (← ref.get)._managerId
    modifyEnv fun env => interactiveRegistrationsExt.modifyState env (·.erase previousId)
  modifyEnv fun env => vcManagerExt.modifyState env (·.insert key owner)
  let lifetime ← IO.CancelToken.new
  let cleanupOnce ← IO.CancelToken.new
  cleanupOnce.onSet do
    -- Finalizers and explicitly supplied tokens can fire under the owner lock.
    -- Publish cancellation synchronously, then release captures under the
    -- dispatcher's normal lock order in a separate task.
    discard <| BaseIO.asTask do
      dispatcher.atomically fun pool => do
        owner.manager.atomically fun ref => do
          let mgr ← ref.get
          mgr.cancelAllDischargers
          ref.set (← newManagerLocked pool)
          pool.modify fun st => { st with owners := st.owners.erase mgr._managerId }
        handleNotificationLocked pool .fill
  -- CancelToken callbacks run before its isSet flag is published. Finish
  -- setting cancellation before scheduling cleanup, so a late mutation cannot
  -- observe an uncanceled owner after cleanup has already cleared it.
  let close : BaseIO Unit := do
    cancelTk.set
    cleanupOnce.set
  lifetime.onSet close
  -- An explicitly supplied token is cancellation authority; the implicit
  -- frontend token is not. Neither is retained by the runtime.
  if let some supplied := cancelTk? then supplied.onSet close
  Command.logSnapshotTask { stx? := none, cancelTk? := some lifetime, task := .pure default }
  -- Insert directly even when UI info is disabled: this leaf owns a resource,
  -- not UI metadata. #guard_msgs preserves info trees while consuming tasks.
  -- Detached workers must clear both infoState and snapshotTasks before capture.
  let info := Info.ofCustomInfo { stx := .missing, value := .mk { token := lifetime : ManagerLifetimeInfo } }
  modifyInfoState fun st => { st with trees := st.trees.push (.node info {}) }
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
    (filter : VCId → VCMetadata → Bool) (registered : HashSet DischargerIdentifier)
    : CommandElabM (HashSet DischargerIdentifier) := do
  let mut registered := registered
  for (vcId, vc) in mgr.nodes do
    if mgr.dormantVCs.contains vcId || !filter vcId vc.metadata then continue
    for discharger in vc.effectiveDischargers do
      if registered.contains discharger.id then continue
      if let some task := discharger.task then
        Command.logSnapshotTask {
          stx? := none
          cancelTk? := none
          task := task.map observerSnapshotTree (sync := true) }
        registered := registered.insert discharger.id
  return registered

/-- Observe an existing request in its original generation and proof checkpoint. -/
private def awaitFilteredManager (owner : VCManagerEnvironment) (managerId : ManagerId)
    (filter : VCId → VCMetadata → Bool) (logTasks := false) :
    CommandElabM (VCManager VCMetadata SmtResult) := do
  let getManager ← captureOwner owner
  let mut registered := HashSet.emptyWithCapacity
  while true do
    liftCoreM Core.checkInterrupted
    if ← owner.cancelTk.isSet then
      applyFrontendRequest owner .fill
      throwError ownerCanceledMessage
    -- Surface manager-loop errors where the user is looking; the loop itself
    -- cannot log to the editor (it is not registered with `logSnapshotTask`).
    for err in ← owner.errors.modifyGet fun errs => (errs, #[]) do
      logWarning m!"VC manager loop error: {err}"
    -- Snapshot under the lock, render outside it (`toResults` pretty-prints).
    let mgr ← getManager
    if mgr._managerId != managerId then
      -- Owner cleanup replaces the generation. Cancellation may have raced
      -- the check above while we were acquiring the manager snapshot.
      if ← owner.cancelTk.isSet then
        throwError ownerCanceledMessage
      throwError "verification interrupted: VC manager generation {managerId} was replaced by {mgr._managerId}"
    if logTasks then registered ← logPendingDischargerTasks mgr filter registered
    if mgr.isDoneFiltered filter then return mgr
    IO.sleep 10
  panic! "unreachable"

/-- Wait for the assertion checks started by spec preparation. Their warnings are
reported by the original request, independently of theorem publication. -/
def awaitAssertionChecks : CommandElabM Unit := do
  let owner ← getVCManagerOwner
  discard <| awaitFilteredManager owner (← currentManagerId owner) (fun _ => isDoesNotThrow)

private def awaitFilteredWithLogging (managerId : ManagerId) (filter : VCMetadata → Bool) :
    CommandElabM (VerificationResults VCMetadata SmtResult) := do
  let mgr ← awaitFilteredManager (← getVCManagerOwner) managerId (fun _ => filter) (logTasks := true)
  let results ← liftCoreM (mgr.toResults filter)
  liftCoreM Core.checkInterrupted
  return results

/-- Start VCs matching the filter and run the callback asynchronously when done.
Uses `wrapAsyncAsSnapshot` so that errors from the callback are reported to the user.
This task also polls for discharger tasks from the manager and registers them with
`logSnapshotTask`, enabling profiler trace propagation.
Returns the requested generation so widget consumers use the same generation as
the observer, even if the manager is reset before widget construction.
Note: Widget display does not work in the callback since it runs in an async context. -/
def runFilteredAsyncWithManagerId (filter : VCMetadata → Bool)
    (callback : VerificationResults VCMetadata SmtResult → CommandElabM Unit) (publish := true) : CommandElabM ManagerId := do
  let managerId ← requestFiltered filter publish
  let cancelTk ← IO.CancelToken.new
  let wrappedTask ← Command.wrapAsyncAsSnapshot (fun () => do
    let results ← awaitFilteredWithLogging managerId filter
    liftCoreM Core.checkInterrupted
    callback results) cancelTk
  let task ← (wrappedTask ()).asTask (prio := .dedicated)
  Command.logSnapshotTask { stx? := none, cancelTk? := cancelTk, task := task }
  return managerId

/-- Start asynchronous verification without retaining its requested generation. -/
def runFilteredAsync (filter : VCMetadata → Bool)
    (callback : VerificationResults VCMetadata SmtResult → CommandElabM Unit) (publish := true) : CommandElabM Unit := do
  discard <| runFilteredAsyncWithManagerId filter callback publish

/-- Start VCs matching the filter and wait synchronously for completion.
Returns the results on the main thread, allowing widget display.
This also polls for discharger tasks from the manager and registers them with
`logSnapshotTask`, enabling profiler trace propagation.
Warning: This blocks the elaborator until all matching VCs complete. -/
def waitFilteredSync (filter : VCMetadata → Bool) : CommandElabM (VerificationResults VCMetadata SmtResult) := do
  let managerId ← requestFiltered filter
  awaitFilteredWithLogging managerId filter

/-- Return a closed proof at the canonical VC type and the name of any new declaration. -/
private def publishVC (vc : VCStatement) (witness : Expr)
    (convert : Expr → Expr → TermElabM Expr := fun proof _ => pure proof) :
    TermElabM (Expr × Option Name) := do
  let fullName := (← getCurrNamespace) ++ vc.name
  let statement ← vc.type
  if (← getEnv).contains fullName then
    -- An interactive witness may already carry the exact universe specialization.
    let existing ← if witness.isConstOf fullName then pure witness else Meta.mkConstWithFreshMVarLevels fullName
    if ← Meta.isDefEq (← Meta.inferType existing) statement then
      let existing ← instantiateMVars existing
      -- A phantom universe can remain unconstrained. Check the concrete instance
      -- before passing it to a companion in a separate term elaboration.
      let closed := if existing.hasLevelMVar then
          existing.replaceLevel fun l => if l.isMVar then some .zero else none
        else existing
      if ← Meta.isDefEq (← Meta.inferType closed) statement then
        -- Conversion inspects the canonical VC even if the user stated a defeq form.
        return (Meta.mkExpectedPropHint closed statement, none)
    throwError "cannot generate VC theorem `{fullName}` because a declaration with that name already exists with a different type"
  let proof ← instantiateMVars (← convert witness statement)
  let name ← withOptions (warn.sorry.set · false) <| addVeilTheorem vc.name statement proof
  return (mkConst name, some name)

/-- Publish direct witnesses first, so a variant uses an independent proof when
one is available. A derived theorem refers to its source theorem by name. -/
private def publishWitnesses (mgr : VCManager VCMetadata SmtResult) (ordered : Array VCId) :
    CommandElabM Unit := do
  let mut published := #[]
  let mut variants := #[]
  for id in ordered do
    let some (vc, witness) := mgr.provenWitness? id | continue
    try
      let (source, added?) ← liftTermElabM <| publishVC vc.toVCStatement witness
      if let some name := added? then published := published.push name
      if let some variant := vc.variant? then
        variants := variants.push (variant, source)
    catch ex =>
      if ex.isInterrupt then throw ex
      logException ex
  for (variant, source) in variants do
    try
      let (_, added?) ← liftTermElabM <| publishVC variant.toVCStatement source variant.ofProof
      if let some name := added? then published := published.push name
    catch ex =>
      if ex.isInterrupt then throw ex
      logException ex
  unless warn.sorry.get (← getOptions) do return
  let affected ← published.filterM fun name => return (← collectAxioms name).contains ``sorryAx
  unless affected.isEmpty do
    let lines := (affected.qsort Name.lt).toList.map (MessageData.ofConstName · (fullNames := true))
    logWarning <| .tagged `hasSorry m!"Published VC theorems using `sorryAx`{indentD (MessageData.joinSep lines Format.line)}"

def addProvenTheoremsInDependencyOrder (filter : VCMetadata → Bool) : CommandElabM Unit := do
  let mgr ← readVCManager
  publishWitnesses mgr (mgr.vcIdsInDependencyOrder (fun _ => filter))

/-- Publish only the requests captured in this module's checkpoint. The commands
that requested them already enabled and observed the work. -/
def publishRequestedTheorems (moduleName : Name) : CommandElabM Unit := do
  let some owner := (vcManagerExt.getState (← getEnv))[moduleName]? | return
  let some (generation, ids) := owner.publication? | return
  modifyEnv fun env => vcManagerExt.modifyState env (·.insert moduleName { owner with publication? := none })
  let requested := fun (id : VCId) (_ : VCMetadata) => ids.contains id
  let mgr ← awaitFilteredManager owner generation requested
  liftCoreM Core.checkInterrupted
  publishWitnesses mgr (mgr.vcIdsInDependencyOrder requested)

end Veil.Verifier
