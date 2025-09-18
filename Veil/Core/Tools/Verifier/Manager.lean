import Lean
import Std.Sync.Channel
open Lean Std

namespace Veil

section DataStructures

abbrev VCId := Nat
abbrev DischargerId := Nat

structure VCIdentifier where
  /-- A unique ID for this VC. -/
  uid : VCId
deriving Inhabited, BEq, Hashable

instance : ToString VCIdentifier where
  toString id := s!"{id.uid}"

structure DischargerIdentifier where
  /-- The ID of the VC that this discharger is discharging. -/
  vcId : VCId
  /-- This is the index of within the `vcId`'s `dischargers` array. -/
  dischargerId : DischargerId
  /-- The name of the discharger. -/
  name : Name
deriving Inhabited, BEq, Hashable

instance : ToString DischargerIdentifier where
  toString id := s!"{id.name} ({id.vcId}.{id.dischargerId})"

structure VCStatement where
  /-- Name of this VC. If the VC gets proven, this will be the name of
  the `theorem` in the Lean environment. -/
  name : Name
  /-- Binders needed for the `statement` of the VC to make sense. -/
  params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
  /-- The syntax of the statement (i.e. Lean type) of this VC. For
  convenience in generating `theorem` statements, we keep the binders
  separately, in the `params` field. -/
  statement : Term
deriving Inhabited, BEq

/-- A discharger, if successful, produces a witness for the VC's statement. -/
abbrev Witness := Expr
/-- Dischargers also produce a front-end specific data, which can be produced
either when the discharger is successful or when it fails (or both). We use
this, for example, to return a counter-example from the SMT solver. -/
abbrev DischargerData (ResultT : Type) := ResultT

inductive DischargerResult (ResultT : Type) where
  /-- The discharger finished successfully, i.e. produced a witness & data. -/
  | success (witness : Witness) (data : DischargerData ResultT) (time : Nat)
  /-- The discharger failed, i.e. did not produce a witness, but did produce
  data, e.g. a counter-example. -/
  | failure (data : DischargerData ResultT) (time : Nat)
  /-- The discharger threw an error. -/
  | error (ex : Exception)
deriving Inhabited

def DischargerResult.time (res : DischargerResult ResultT) : Option Nat :=
  match res with
  | .success _ _ time | .failure _ time => some time
  | .error _ => none

def DischargerResult.kindString (res : DischargerResult ResultT) : String :=
  match res with
  | .success _ _ _ => "success"
  | .failure _ _ => "failure"
  | .error _ => "error"

instance [ToString ResultT] : ToString (DischargerResult ResultT) where
  toString res :=
    match res with
    | .success expr data time => s!"success {expr} {data} ({time}ms)"
    | .failure data time => s!"failure {data} ({time}ms)"
    | .error _ex => s!"exception thrown"

instance [ToMessageData ResultT] : ToMessageData (DischargerResult ResultT) where
  toMessageData res :=
    match res with
    | .success expr data time => m!"success {expr} {data} ({time}ms)"
    | .failure data time => m!"failure {data} ({time}ms)"
    | .error ex => m!"error {ex.toMessageData}"

inductive DischargeStatus (ResultT : Type) where
  /-- The discharger task has not been started yet. -/
  | notStarted
  /-- The discharger is running, i.e. started but hasn't finished yet. -/
  | running
  /-- The discharger finished -/
  | finished (res : DischargerResult ResultT)
deriving Inhabited

/-- A notification from a discharger to the VCManager. -/
abbrev DischargerNotification (ResultT : Type) := (DischargerIdentifier × DischargerResult ResultT)
abbrev DischargerTask (ResultT : Type) := Task (Except Exception (DischargerResult ResultT))

/-- A way of discharging / proving a VC.-/
structure Discharger (ResultT : Type) where
  id : DischargerIdentifier
  /-- Optionally, a VC discharger can provide term (e.g. a proof script) that
  can be shown to the user, e.g. when a VC's corresponding `theorem` is
  pretty-printed. -/
  term : Option Term := none
  /-- A cancellation token for the discharger. -/
  cancelTk : IO.CancelToken
  /-- The discharger.  -/
  task : Option (DischargerTask ResultT)
  /-- Creates a task that discharges the VC. It's the task responsibility to
  return to the VCManager a `VCDischargeStatus`. This is done via the `ch`
  field of the `VCManager`. Running the resulting `BaseIO` action causes the
  task to be started eagerly. The task should be stored in the `task` field for
  later access. -/
  private mkTask : BaseIO (DischargerTask ResultT)

structure VCData (VCMetaT : Type) extends VCStatement where
  /-- Metadata associated with this VC, provided by the frontend. -/
  metadata : VCMetaT
deriving Inhabited

structure VerificationCondition (VCMetaT ResultT : Type) extends VCIdentifier, VCData VCMetaT where
  /-- Dischargers for this VC. More can be added after the VC is created, and
  the system will pick up new dischargers and re-attempt to discharge the VC.-/
  dischargers : Array (Discharger ResultT)
  /-- The ID of the (first) discharger that successfully discharged the VC. -/
  successful : Option DischargerId := none
deriving Inhabited

instance : BEq (VerificationCondition VCMetaT ResultT) where
  beq a b :=
    a.uid == b.uid &&
    a.statement == b.statement

instance : Hashable (VerificationCondition VCMetaT ResultT) where
  hash x := hash x.uid

def VerificationCondition.theoremStx [Monad m] [MonadQuotation m] [MonadError m] (vc : VerificationCondition VCMetaT ResultT) : m Command := do
  let defaultDischargedBy ← `(term|by sorry)
  let dischargedBy : Term ← match vc.successful with
  | some dischargerId => do
    let .some discharger := vc.dischargers[dischargerId]?
      | throwError "VerificationCondition.theoremStx: successful discharger {dischargerId} not found for VC {vc.uid}"
    pure $ discharger.term.getD defaultDischargedBy
  | none => pure defaultDischargedBy
  `(command| theorem $(mkIdent vc.name) $(vc.params)* : $(vc.statement) := $dischargedBy)

end DataStructures

section VCManager

inductive ManagerNotification (ResultT : Type) where
  | fromDischarger (dischargerId : DischargerIdentifier) (res : DischargerResult ResultT)
  | fromFrontend
deriving Inhabited

instance [ToString ResultT] : ToString (ManagerNotification ResultT) where
  toString res :=
    match res with
    | .fromDischarger dischargerId res => s!"fromDischarger {dischargerId} {res}"
    | .fromFrontend => s!"fromFrontend"

-- Based on [RustDagcuter](https://github.com/busyster996/RustDagcuter)
structure VCManager (VCMetaT ResultT: Type) where
  /-- All VCs, indexed by their ID. -/
  nodes : HashMap VCId (VerificationCondition VCMetaT ResultT)

  /-- Dependencies of each VC, i.e. VCs that must be proven before this
  VC can be proven. -/
  upstream : HashMap VCId (HashSet VCId)

  /-- In-degree count for each VC (number of upstream dependencies).
  Used for topological sorting: unfinished tasks with 0 in-degree
  should be executed next. -/
  inDegree : HashMap VCId Nat

  /-- Dependents of each VC, i.e. VCs that depend on _this_ VC. Used to
  update in-degrees when a task completes. -/
  downstream : HashMap VCId (HashSet VCId)

  protected _nextId : VCId := 0

  /-- Notifications from dischargers to the VCManager that a discharger has
  finished. NOTE: Do not change after the VCManager is created! -/
  protected fromDischargers : Option (Std.Channel (ManagerNotification ResultT)) := none
  /-- Notifications from the frontend to the VCManager that a VC or discharger
  has been added. NOTE: Do not change after the VCManager is created! -/
  protected fromFrontend : Option (Std.Channel (ManagerNotification ResultT)) := none
deriving Inhabited

/-- Create a new VCManager. This should be preferred instead of `default`, as
this initializes the channel for communicating the discharge status of VCs. -/
def VCManager.new : BaseIO (VCManager VCMetaT ResultT) := do
  return {
    nodes := HashMap.emptyWithCapacity,
    upstream := HashMap.emptyWithCapacity,
    inDegree := HashMap.emptyWithCapacity,
    downstream := HashMap.emptyWithCapacity,
    _nextId := 0,
    fromDischargers := some (← Std.Channel.new),
    fromFrontend := some (← Std.Channel.new),
  }

/-- Adds a new verification condition (VC) to the VCManager, along with its
upstream dependencies. Returns the updated VCManager and the new VC. -/
def VCManager.addVC (mgr : VCManager VCMetaT ResultT) (vc : VCData VCMetaT) (dependsOn : HashSet VCId) (initialDischargers : Array (Discharger ResultT) := #[]) : (VCManager VCMetaT ResultT × VCId) := Id.run do
  let uid := mgr._nextId
  let vc := {vc with uid := uid, dischargers := initialDischargers, successful := none}
  -- Add ourselves downstream of all our dependencies
  let mut downstream := mgr.downstream
  for parent in dependsOn do
    downstream := downstream.insert parent ((downstream[parent]? |>.getD {}).insert uid)
  let mgr' := { mgr with
    nodes := (mgr.nodes.insert uid vc),
    upstream := (mgr.upstream.insert uid dependsOn),
    inDegree := (mgr.inDegree.insert uid dependsOn.size),
    downstream := downstream,
    _nextId := mgr._nextId + 1
  }
  (mgr', uid)

open Lean.Elab.Command in
def VCManager.mkAddDischarger (mgr : VCManager VCMetaT ResultT) (vcId : VCId) (mk : VCStatement → DischargerIdentifier → Std.Channel (ManagerNotification ResultT) → CommandElabM (Discharger ResultT)) : CommandElabM (VCManager VCMetaT ResultT) := do
  let .some ch := mgr.fromDischargers | throwError "VCManager.mkAddDischarger called without a channel"
  match mgr.nodes[vcId]? with
  | some vc => do
    let dischargerId := vc.dischargers.size
    let id : DischargerIdentifier := {vcId, dischargerId, name := Name.mkSimple s!"{vc.name}_{dischargerId}" }
    pure { mgr with nodes := mgr.nodes.insert vcId { vc with dischargers := vc.dischargers.push (← mk vc.toVCStatement id ch) } }
  | none => pure mgr

def VCManager.theorems [Monad m] [MonadQuotation m] [MonadError m] (mgr : VCManager VCMetaT ResultT) : m (Array Command) :=
  mgr.nodes.valuesArray.mapM (·.theoremStx)

def Discharger.run (discharger : Discharger ResultT) : BaseIO (Discharger ResultT) := do
  match discharger.task with
  | some _ => return discharger
  -- This will start the task eagerly
  | none =>
    let task ← discharger.mkTask
    return { discharger with task := some task }

def Discharger.status (discharger : Discharger ResultT) : BaseIO (DischargeStatus ResultT) := do
  match discharger.task with
  | none => return .notStarted
  | some task =>
    match ← IO.hasFinished task with
    | false => return .running
    | true => do
      match task.get with
      | .ok res => return .finished res
      | .error ex => return .finished (.error ex)

def Discharger.isSuccessful (discharger : Discharger ResultT) : BaseIO Bool := do
  match (← discharger.status) with
  | .finished (.success _ _ _) => return true
  | _ => return false

/-- Find the next discharger to try. Once this function returns `none`, it will
not return `some` again unless new dischargers are added. -/
def VerificationCondition.nextDischarger? (vc : VerificationCondition VCMetaT ResultT) : BaseIO (Option (Discharger ResultT)) := do
  match vc.successful with
  | some _ => return .none
  | none =>
    for discharger in vc.dischargers do
      match ← discharger.status with
      | .notStarted => return some discharger
      | .finished (.success _ _ _) | .running => return none -- we wait for the discharger to finish
      | .finished (.failure _ _) | .finished (.error _) => continue
    return none

def VCManager.readyTasks (mgr : VCManager VCMetaT ResultT) : CoreM (List (VerificationCondition VCMetaT ResultT × Discharger ResultT)) := do
  let ready ← mgr.inDegree.toList.filterMapM (fun (vcId, inDegree) => do
    let .some vc := mgr.nodes[vcId]? | throwError "VCManager.executeOne: VC {vcId} not found"
    if inDegree != 0 then pure none else
      match ← vc.nextDischarger? with
      | some discharger => pure (some (vc, discharger))
      | none => pure none)
  return ready

def VCManager.startTask (mgr : VCManager VCMetaT ResultT) (vc : VerificationCondition VCMetaT ResultT) (discharger : Discharger ResultT) : CoreM (VCManager VCMetaT ResultT) := do
  let discharger' ← discharger.run
  return { mgr with nodes := mgr.nodes.insert vc.uid { vc with dischargers := vc.dischargers.set! discharger.id.dischargerId discharger' }}

def VCManager.executeOne (mgr : VCManager VCMetaT ResultT) : CoreM (VCManager VCMetaT ResultT) := do
  let ready ← mgr.readyTasks
  match ready with
  | [] => return mgr
  | (vc, discharger) :: _ => mgr.startTask vc discharger

def VCManager.startAll (mgr : VCManager VCMetaT ResultT) : CoreM (VCManager VCMetaT ResultT) := do
  let mut mgr' := mgr
  let ready ← mgr'.readyTasks
  for (vc, discharger) in ready do
     mgr' ← mgr'.startTask vc discharger
  dbg_trace "({← IO.monoMsNow})[VCManager.startAll] finished starting all tasks"
  return mgr'

instance [ToMessageData VCMetaT] : ToMessageData (VCManager VCMetaT ResultT) where
  toMessageData mgr :=
    let nodes := mgr.nodes.toList.map (fun (uid, vc) => m!"[{uid}] {vc.name} depends on {mgr.upstream[uid]!.toList.map (fun dep => m!"{dep}")} (in-degree: {mgr.inDegree[uid]!}) {vc.metadata}")
    MessageData.joinSep nodes "\n"

end VCManager

end Veil
