import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Core.Tools.Verifier.Manager
import Veil.Core.Tools.Verifier.Results
import Std.Sync.Mutex
import Veil.Util.Multiprocessing
import Veil.Util.Meta

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

/-- One module in one document generation. No process-global current manager:
commands, result callbacks and widgets retain their own session handle. -/
structure Session where
  private state : Mutex SessionState
  source : String

initialize sessionEnv : SimpleScopedEnvExtension (Option Session) (Option Session) ←
  registerSimpleScopedEnvExtension { initial := none, addEntry := fun _ s => s }
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
    if state.cancelled then throw (IO.userError "Verification session was cancelled")
    return state.manager

/-- Fork cached command state after an edit below an unchanged #gen_spec.
Factory replay allocates fresh tasks, tokens and promises. Interactive results
survive only if their exact theorem declaration remains in this environment. -/
private def Session.fork (session : Session) (source : String) (env : Environment) :
    EIO Exception Session := do
  let old ← session.state.atomically fun ref => do
    let state ← ref.get
    state.manager.cancelAllDischargers
    ref.set {state with cancelled := true, superseded := true}
    return state.manager
  let fresh ← newManager
  let some ch := fresh.ch | throw (Exception.error Syntax.missing "Missing session result channel")
  let mut mgr := {old with
    _managerId := fresh._managerId, ch := fresh.ch, _doneWith := {}
    _dischargerResults := {}, _totalDischarged := 0, _totalSolved := 0
    enabledVCs := {}, factories := {}, dependencyErrors := {}, retiredDischargers := #[]
    inDegree := old.upstream.map (fun _ deps => deps.size)
    dormantVCs := old.alternativeVCs.valuesArray.foldl (fun ids alts => alts.foldl (·.insert ·) ids) {} }
  for (vcId, vc) in old.nodes do
    let mut ds := #[]
    for d in vc.dischargers do
      let id := {d.id with managerId := mgr._managerId, dischargerId := ds.size}
      if let some factory := old.factories[(vcId, d.id.dischargerId)]? then
        ds := ds.push (← factory id ch)
        mgr := {mgr with factories := mgr.factories.insert (vcId, id.dischargerId) factory}
      else if d.isInteractive then
        if let some (name, value) := d.theoremValue? then
          if let some (.thmInfo info) := env.find? name then
            if info.value == value then ds := ds.push {d with id}
      else
        throw (Exception.error Syntax.missing m!"Cannot restart VC {vc.name}: its discharger has no factory")
    mgr := {mgr with nodes := mgr.nodes.insert vcId {vc with dischargers := ds, successful := none}}
    for d in ds do
      if d.isInteractive then
        if let .finished result ← d.status then mgr ← mgr.recordDischargerResult d.id result
  return {state := ← Mutex.new {manager := mgr}, source}

/-- The environment binding is immutable even when a cached #gen_spec handle
contains completed work. Async callbacks capture this handle before spawning;
an old callback never resolves against a newer document's session. -/
def getSession [Monad m] [MonadEnv m] [MonadFileMap m] [MonadError m] [MonadResolveName m]
    [MonadLiftT IO m] [MonadLiftT (EIO Exception) m] : m Session := do
  let some session ← sessionEnv.get | throwError "VC manager has not been initialized; use #gen_spec first"
  let source := (← getFileMap).source
  let superseded ← (session.state.atomically fun ref => return (← ref.get).superseded : IO Bool)
  if source == session.source && !superseded then return session
  let fresh ← session.fork source (← getEnv)
  sessionEnv.add (some fresh) .local
  return fresh

def isDoesNotThrow (m : VCMetadata) : Bool := m.propertyName? == some `doesNotThrow

private def fillAvailableSlotsLocked (mgr : VCManager VCMetadata SmtResult)
    : BaseIO (VCManager VCMetadata SmtResult) := do
  let mut mgr := mgr
  let ready := (← mgr.readyTasks).take ((← getNumCores) - (← mgr.inFlightCount))
  for (vc, discharger) in ready do
    let discharger ← discharger.run
    let vc := {vc with dischargers := vc.dischargers.set! discharger.id.dischargerId discharger}
    mgr := {mgr with nodes := mgr.nodes.insert vc.uid vc}
  return mgr

/-- One bounded-lifetime driver per active session. It exits when enabled work
finishes and is restarted by a later start request. All transitions and task
spawns are BaseIO under the session mutex, so interruption cannot tear them. -/
private partial def Session.drive (session : Session) : BaseIO Unit := do
  let continueDriving ← session.state.atomically fun ref => do
    let mut state ← ref.get
    let mut mgr := state.manager
    if let .error message := mgr.validateRegistrations then
      mgr.cancelAllDischargers
      ref.set {state with failure? := some message, driving := false, driver := none}
      return false
    if state.cancelled || (← state.cancelTk?.mapM IO.CancelToken.isSet).getD false then
      mgr.cancelAllDischargers
      ref.set {state with cancelled := true, driving := false, driver := none}
      return false
    let some ch := mgr.ch | return false
    while true do
      let some notification ← ch.tryRecv | break
      match notification with
      | .dischargerResult id result => mgr ← mgr.recordDischargerResult id result
      | .startAll => mgr := mgr.enableAll
      | .startFiltered filter => mgr := mgr.enableMatching filter
      | .fill => pure ()
      | .reset id =>
        if id == mgr._managerId then state := {state with cancelled := true}
    if state.cancelled then
      mgr.cancelAllDischargers
      ref.set {state with manager := mgr, driving := false, driver := none}
      return false
    mgr ← mgr.reconcileFinished
    mgr ← fillAvailableSlotsLocked mgr
    let pending := mgr.nodes.toArray.any fun (id, _) =>
      mgr.enabledVCs.contains id && !mgr._doneWith.contains id && !mgr.dormantVCs.contains id
    let active := pending || (← mgr.inFlightCount) > 0
    ref.set {state with manager := mgr, driving := active, driver := if active then state.driver else none}
    return active
  if continueDriving then
    IO.sleep 10
    session.drive

private def Session.start (session : Session) (filter : VCMetadata → Bool) : IO Unit :=
  session.state.atomically fun ref => do
    let state ← ref.get
    if state.cancelled then return
    if let .error message := state.manager.validateRegistrations then throw (IO.userError message)
    let mut state := {state with manager := state.manager.enableMatching filter}
    let pending := state.manager.nodes.toArray.any fun (id, _) =>
      state.manager.enabledVCs.contains id && !state.manager._doneWith.contains id && !state.manager.dormantVCs.contains id
    unless state.driving || !pending do
      let task ← session.drive.asTask (prio := .dedicated)
      state := {state with driving := true, driver := some task}
    ref.set state

def Session.withManager [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadLiftT (ST IO.RealWorld) m] [MonadFinally m] [MonadError m]
    (session : Session) (f : IO.Ref (VCManager VCMetadata SmtResult) → m α) : m α := do
  let result ← session.state.atomically fun ref => do
    let state ← ref.get
    if state.cancelled then throwError "Verification session was cancelled"
    let managerRef ← IO.mkRef state.manager
    let result ← f managerRef
    ref.set {state with manager := ← managerRef.get}
    return result
  session.start (fun _ => false)
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
def startAll : CommandElabM Unit := do (← getSession).start (fun _ => true)
def startFiltered (filter : VCMetadata → Bool) : CommandElabM Unit := do (← getSession).start filter

/-- Create a new module session without abandoning other modules' requests. -/
def runManager (cancelTk? : Option IO.CancelToken := none) : CommandElabM Unit := do
  let session : Session := {state := ← Mutex.new {manager := ← newManager, cancelTk?}, source := (← getFileMap).source}
  sessionEnv.add (some session) .local

private def Session.acquire (session : Session) (filter : VCMetadata → Bool) : BaseIO Nat :=
  session.state.atomically fun ref => do
    let state ← ref.get
    ref.set {state with
      nextRequest := state.nextRequest + 1
      requests := state.requests.insert state.nextRequest filter}
    return state.nextRequest

/-- Cancelling one request cancels only work no other live request needs.
Snapshot leaf tasks carry no cancellation token: duplicate registrations by
concurrent waiters therefore cannot cancel one another's solver work. -/
private def Session.release (session : Session) (request : Nat) (cancel : Bool) : BaseIO Unit :=
  session.state.atomically fun ref => do
    let state ← ref.get
    let some filter := state.requests[request]? | return
    let requests := state.requests.erase request
    if cancel then
      for (_, vc) in state.manager.nodes do
        if filter vc.metadata && !(requests.valuesArray.any (· vc.metadata)) then
          for d in vc.dischargers do d.cancelTk.set
    ref.set {state with requests}

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
  session.start filter
  let cancelTk ← IO.CancelToken.new
  let completed ← IO.mkRef false
  let wrapped ← Command.wrapAsyncAsSnapshot (fun () => do
    let result ← awaitFilteredWithLogging session filter
    completed.set true
    callback result) cancelTk
  let task ← (do
    let snapshot ← wrapped ()
    session.release request (!(← completed.get))
    return snapshot).asTask (prio := .dedicated)
  Command.logSnapshotTask {stx? := none, cancelTk? := cancelTk, task}

def waitFilteredSync (filter : VCMetadata → Bool) : CommandElabM (VerificationResults VCMetadata SmtResult) := do
  let session ← getSession
  let request ← session.acquire filter
  session.start filter
  try
    let results ← awaitFilteredWithLogging session filter
    session.release request false
    return results
  finally
    session.release request true

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
