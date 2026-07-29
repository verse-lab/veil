import Lean
import Std.Sync.Channel
import Veil.Backend.SMT.Result
import Veil.Util.TopologicalSort
open Lean Std

namespace Veil

section DataStructures

abbrev VCId := Nat
abbrev ManagerId := Nat
abbrev DischargerId := Nat

structure VCIdentifier where
  /-- A unique ID for this VC. -/
  uid : VCId
deriving Inhabited, BEq, Hashable

instance : ToString VCIdentifier where
  toString id := s!"{id.uid}"

structure DischargerIdentifier where
  /-- The ID of the VCManager that this discharger is associated with. Used to
  ignore dischargers from other managers (e.g. after a `reset`). -/
  managerId : ManagerId
  /-- The ID of the VC that this discharger is discharging. -/
  vcId : VCId
  /-- This is the index of within the `vcId`'s `dischargers` array. -/
  dischargerId : DischargerId
  /-- The name of the discharger. -/
  name : Name
deriving Inhabited, BEq, Hashable

instance : ToString DischargerIdentifier where
  toString id := s!"{id.name} (VC #{id.vcId} ∈ mgr {id.managerId})"

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

open Elab Term in
/-- The type of the VC's statement as an `Expr`. -/
def VCStatement.type (vc : VCStatement) : TermElabM Expr := do
  Term.elabBinders vc.params fun vs => do
  let body ← withSynthesize (postpone := .no) $
    withoutErrToSorry $ elabTerm vc.statement (Expr.sort levelZero)
  let typ ← Meta.mkForallFVars vs body >>= instantiateMVars
  if typ.hasMVar || typ.hasFVar || typ.hasSorry then
    throwError "VCStatement.type: {vc.name}'s type is not fully determined"
  return typ

/-- A discharger, if successful, produces a witness for the VC's statement. -/
abbrev Witness := Expr
/-- Dischargers also produce a front-end specific data, which can be produced
either when the discharger is successful or when it fails (or both). We use
this, for example, to return a counter-example from the SMT solver. -/
abbrev DischargerData (ResultT : Type) := Option ResultT

inductive DischargerResult (ResultT : Type) where
  /-- The discharger finished successfully, i.e. produced a witness & data.
      The witness is optional for trace queries where there's no proof term. -/
  | proven (witness : Option Witness) (data : DischargerData ResultT) (time : Nat)
  /-- The discharger disproved the VC, i.e. produced a counter-example. -/
  | disproven (data : DischargerData ResultT) (time : Nat)
  /-- The discharger did not prove or disprove the VC, i.e. the result is
  inconclusive -/
  | unknown (data : DischargerData ResultT) (time : Nat)
  /-- The discharger threw an error. -/
  | error (ex : Array (Exception × Json)) (time : Nat)

instance : Inhabited (DischargerResult ResultT) where
  default := .error #[] default

def DischargerResult.isSuccessful (res : DischargerResult ResultT) : Bool :=
  match res with
  | .proven _ _ _ => true
  | .disproven _ _ | .unknown _ _ | .error _ _ => false

def DischargerResult.time (res : DischargerResult ResultT) : Nat :=
  match res with
  | .proven _ _ time | .disproven _ time | .unknown _ time | .error _ time => time

def DischargerResult.kindString (res : DischargerResult ResultT) : String :=
  match res with
  | .proven _ _ _ => "proven"
  | .disproven _ _ => "disproven"
  | .unknown _ _ => "unknown"
  | .error _ _ => "error"

instance [ToString ResultT] : ToString (DischargerResult ResultT) where
  toString res :=
    match res with
    | .proven (some expr) data time => s!"proven {expr} {data} ({time}ms)"
    | .proven none data time => s!"proven (no witness) {data} ({time}ms)"
    | .disproven data time => s!"disproven {data} ({time}ms)"
    | .unknown data time => s!"unknown {data} ({time}ms)"
    | .error exs time => s!"exception thrown {exs.map (·.2)} ({time}ms)"

instance [ToMessageData ResultT] : ToMessageData (DischargerResult ResultT) where
  toMessageData res :=
    match res with
    | .proven (some expr) data time => m!"proven {expr} {data} ({time}ms)"
    | .proven none data time => m!"proven (no witness) {data} ({time}ms)"
    | .disproven data time => m!"disproven {data} ({time}ms)"
    | .unknown data time => m!"unknown {data} ({time}ms)"
    | .error exs time => m!"error {exs.map (·.1.toMessageData)} ({time}ms)"

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
/-- A task that produces a SnapshotTree for integration with the language server. -/
abbrev SnapshotTreeTask := Task Language.SnapshotTree

/-- A way of discharging / proving a VC.-/
structure Discharger (ResultT : Type) where
  id : DischargerIdentifier
  /-- Whether this discharger comes from an explicitly tagged interactive proof
  theorem rather than automatic tooling. -/
  isInteractive : Bool := false
  /-- Optionally, a VC discharger can provide term (e.g. a proof script) that
  can be shown to the user, e.g. when a VC's corresponding `theorem` is
  pretty-printed. -/
  term : Option Term := none
  /-- A cancellation token for the discharger. Cancellation is *cooperative*:
  Lean elaboration observes the token at heartbeat checkpoints, but an
  in-flight in-process cvc5 `checkSat` (FFI) cannot be interrupted from Lean.
  Setting the token therefore takes effect at the next heartbeat, or once the
  current solver call returns or hits `veil.smt.timeout`. -/
  cancelTk : IO.CancelToken
  /-- The snapshot tree task for integration with the language server's error
  reporting. This is produced by `wrapAsyncAsSnapshot`. -/
  task : Option SnapshotTreeTask
  /-- Promise that resolves to the monotonic timestamp (ms) when the discharger
  actually starts executing. This is set by the discharger itself, not when
  the task is scheduled. -/
  startTimePromise : IO.Promise Nat
  /-- Promise that resolves to the discharger result. This is how results are
  communicated since `wrapAsyncAsSnapshot` returns Unit. -/
  resultPromise : IO.Promise (DischargerResult ResultT)
  /-- Creates a task that discharges the VC. Running the resulting `BaseIO`
  action causes the task to be started eagerly. The task should be stored in
  the `task` field for later access. -/
  private mkTask : BaseIO SnapshotTreeTask

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
  let veilHuman : TSyntax `tactic := ⟨mkIdent `unveil⟩
  let defaultDischargedBy ← `(term|by
    $veilHuman:tactic
    sorry)
  let dischargedBy : Term ← match vc.successful with
  | some dischargerId => do
    let .some discharger := vc.dischargers[dischargerId]?
      | throwError "VerificationCondition.theoremStx: successful discharger {dischargerId} not found for VC {vc.uid}"
    pure $ discharger.term.getD defaultDischargedBy
  | none => pure defaultDischargedBy
  `(command| theorem $(mkIdent vc.name) $(vc.params)* : $(vc.statement) := $dischargedBy)

open Lean.Meta.Tactic.TryThis in
def VerificationCondition.suggestion [Monad m] [MonadQuotation m] [MonadError m] (vc : VerificationCondition VCMetaT ResultT) : m Suggestion :=
  vc.theoremStx

end DataStructures

section VCManager

inductive ManagerNotification (VCMetaT ResultT : Type) where
  | dischargerResult (id : DischargerIdentifier) (res : DischargerResult ResultT)
  /-- Issued by the frontend to reset the VCManager. -/
  | reset (managerId : ManagerId)
  /-- Issued by the frontend to start all ready tasks. -/
  | startAll
  /-- Start VCs matching the filter. -/
  | startFiltered (filter : VCMetaT → Bool)
deriving Inhabited

instance [ToString ResultT] : ToString (ManagerNotification VCMetaT ResultT) where
  toString res :=
    match res with
    | .dischargerResult dischargerId res => s!"dischargerResult {dischargerId} {res}"
    | .reset managerId => s!"reset {managerId}"
    | .startAll => s!"startAll"
    | .startFiltered _ => s!"startFiltered"

inductive VCStatus where
  /-- The VC has been proven (shown to be true). -/
  | proven
  /-- The VC has been disproven (shown to be false). -/
  | disproven
  /-- The VC is still unknown (not proven or disproven). -/
  | unknown
  /-- All dischargers returned an error/threw an exception. -/
  | error
  /-- All dischargers timed out. -/
  | timeout
deriving Inhabited, BEq, Hashable

instance : ToString VCStatus where
  toString status :=
    match status with
    | .proven => "✅"
    | .disproven => "❌"
    | .unknown => "❓"
    | .error => "💥"
    | .timeout => "⏱️"

def VCStatus.emoji (status : VCStatus) : String := toString status

def VCStatus.kindString (status : VCStatus) : String :=
  match status with
  | .proven => "proven"
  | .disproven => "disproven"
  | .unknown => "unknown"
  | .error => "error"
  | .timeout => "timeout"

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

  /-- Maps primary VC IDs to their alternative VCs (e.g., TR-style).
  Alternative VCs are triggered when the primary VC's dischargers all fail. -/
  alternativeVCs : HashMap VCId (Array VCId) := HashMap.emptyWithCapacity

  /-- VCs that should NOT be started automatically (waiting for trigger).
  Used for alternative VCs that only run when their primary VC fails. -/
  dormantVCs : HashSet VCId := HashSet.emptyWithCapacity

  protected _nextVcId : VCId := 0
  /-- Number of dischargers that have finished executing. -/
  protected _totalDischarged : Nat := 0
  /-- Number of dischargers that have finished successfully. This is equal to
  the number of VCs that have been proven. -/
  protected _totalSolved : Nat := 0

  protected _doneWith : HashMap VCId VCStatus := HashMap.emptyWithCapacity

  /-- Store discharger results for each VC, indexed by (VCId, DischargerId). -/
  protected _dischargerResults : HashMap (VCId × DischargerId) (DischargerResult ResultT) := HashMap.emptyWithCapacity

  protected _managerId : ManagerId := 0

  /-- Channel for communicating with the VCManager. -/
  protected ch : Option (Std.Channel (ManagerNotification VCMetaT ResultT)) := none
deriving Inhabited

/-- Create a new VCManager. This should be preferred instead of `default`, as
this initializes the channel for communicating the discharge status of VCs. -/
def VCManager.new (ch : Std.Channel (ManagerNotification VCMetaT ResultT)) (currentManagerId : ManagerId := 0) : BaseIO (VCManager VCMetaT ResultT) := do
  return {
    nodes := HashMap.emptyWithCapacity,
    upstream := HashMap.emptyWithCapacity,
    inDegree := HashMap.emptyWithCapacity,
    downstream := HashMap.emptyWithCapacity,
    alternativeVCs := HashMap.emptyWithCapacity,
    dormantVCs := HashSet.emptyWithCapacity,
    _doneWith := HashMap.emptyWithCapacity,
    _dischargerResults := HashMap.emptyWithCapacity,
    _nextVcId := 0,
    _managerId := currentManagerId + 1,
    ch := ch,
  }

/-- Adds a new verification condition (VC) to the VCManager, along with its
upstream dependencies. Returns the updated VCManager and the new VC.
If `isDormant` is true, the VC will not be started automatically by `readyTasks`. -/
def VCManager.addVC (mgr : VCManager VCMetaT ResultT) (vc : VCData VCMetaT) (dependsOn : HashSet VCId) (initialDischargers : Array (Discharger ResultT) := #[]) (isDormant : Bool := false) : (VCManager VCMetaT ResultT × VCId) := Id.run do
  let uid := mgr._nextVcId
  let vc := {vc with uid := uid, dischargers := initialDischargers, successful := none}
  -- Add ourselves downstream of all our dependencies
  let mut downstream := mgr.downstream
  for parent in dependsOn do
    downstream := downstream.insert parent ((downstream[parent]? |>.getD {}).insert uid)
  let mut mgr' := { mgr with
    nodes := (mgr.nodes.insert uid vc),
    upstream := (mgr.upstream.insert uid dependsOn),
    inDegree := (mgr.inDegree.insert uid dependsOn.size),
    downstream := downstream,
    _nextVcId := mgr._nextVcId + 1
  }
  -- Mark as dormant if requested (e.g., for alternative VCs)
  if isDormant then
    mgr' := { mgr' with dormantVCs := mgr'.dormantVCs.insert uid }
  (mgr', uid)

/-- Add an alternative VC associated with a primary VC. The alternative
starts dormant and will only be triggered when the primary VC fails
(i.e., all of its dischargers fail). -/
def VCManager.addAlternativeVC (mgr : VCManager VCMetaT ResultT)
    (vc : VCData VCMetaT)
    (primaryVCId : VCId)
    (initialDischargers : Array (Discharger ResultT) := #[])
    : (VCManager VCMetaT ResultT × VCId) := Id.run do
  -- Use the same dependencies as the primary VC
  let primaryDeps := mgr.upstream[primaryVCId]?.getD {}
  let (mgr', altId) := mgr.addVC vc primaryDeps initialDischargers (isDormant := true)
  -- Register the association: primary -> alternative
  let alts := mgr'.alternativeVCs[primaryVCId]?.getD #[]
  let mgr'' := { mgr' with
    alternativeVCs := mgr'.alternativeVCs.insert primaryVCId (alts.push altId)
  }
  (mgr'', altId)

private def VCManager.mkDischargerIdentifier (mgr : VCManager VCMetaT ResultT)
    (vc : VerificationCondition VCMetaT ResultT) : DischargerIdentifier :=
  { vcId := vc.uid
    dischargerId := vc.dischargers.size
    name := Name.mkSimple s!"{vc.name}_{vc.dischargers.size}"
    managerId := mgr._managerId }

/-- Add a discharger to an existing VC. If the VC had previously exhausted its
dischargers without success, re-open it so the new discharger can affect the
reported status. -/
def VCManager.addDischarger (mgr : VCManager VCMetaT ResultT) (vcId : VCId)
    (discharger : Discharger ResultT) : VCManager VCMetaT ResultT := Id.run do
  let some vc := mgr.nodes[vcId]? | return mgr
  let mut mgr := mgr
  let vc := { vc with dischargers := vc.dischargers.push discharger }
  mgr := { mgr with nodes := mgr.nodes.insert vcId vc }
  if vc.successful.isNone then
    mgr := { mgr with _doneWith := mgr._doneWith.erase vcId }
  return mgr

open Lean.Elab.Command in
def VCManager.mkAddDischarger (mgr : VCManager VCMetaT ResultT) (vcId : VCId) (mk : VCStatement → DischargerIdentifier → Std.Channel (ManagerNotification VCMetaT ResultT) → CommandElabM (Discharger ResultT)) : CommandElabM (VCManager VCMetaT ResultT) := do
  let .some ch := mgr.ch | throwError "VCManager.mkAddDischarger called without a channel"
  match mgr.nodes[vcId]? with
  | some vc => do
    let id := mgr.mkDischargerIdentifier vc
    pure <| mgr.addDischarger vcId (← mk vc.toVCStatement id ch)
  | none => pure mgr

def VCManager.theorems [Monad m] [MonadQuotation m] [MonadError m] (mgr : VCManager VCMetaT ResultT) : m (Array Command) :=
  mgr.nodes.valuesArray.mapM (·.theoremStx)

def VCManager.undischargedTheorems [Monad m] [MonadQuotation m] [MonadError m] (mgr : VCManager VCMetaT ResultT) : m (Array Command) :=
  mgr.nodes.valuesArray.filterMapM (fun vc => do
    match vc.successful with
    | some _ => return none
    | none => return some (← vc.theoremStx))

open Lean.Meta.Tactic.TryThis in
def VCManager.suggestions [Monad m] [MonadQuotation m] [MonadError m] (mgr : VCManager VCMetaT ResultT) : m (Array Suggestion) :=
  mgr.nodes.valuesArray.mapM (·.suggestion)

/-- VC ids matching `filter`, ordered so upstream dependencies appear before
their downstream dependents. Ties are broken by VC id for deterministic theorem
declaration order. -/
def VCManager.vcIdsInDependencyOrder (mgr : VCManager VCMetaT ResultT)
    (filter : VCMetaT → Bool := fun _ => true) : Array VCId := Id.run do
  let selectedIds := (List.range mgr._nextVcId).filter fun vcId =>
    match mgr.nodes[vcId]? with
    | some vc => filter vc.metadata
    | none => false
  topologicalSort selectedIds fun vcId =>
    (mgr.upstream[vcId]?.getD {}).toList

/-- The witness produced by the successful discharger for `vcId`, if there is
one. Trace VCs can be `.proven` without a proof witness and therefore return
`none`. -/
def VCManager.provenWitness? (mgr : VCManager VCMetaT ResultT)
    (vcId : VCId) : Option (VerificationCondition VCMetaT ResultT × Witness) := do
  let vc ← mgr.nodes[vcId]?
  let dischargerId ← vc.successful
  match mgr._dischargerResults[(vcId, dischargerId)]? with
  | some (.proven (some witness) _ _) => some (vc, witness)
  | _ => none

def Discharger.run (discharger : Discharger ResultT) : BaseIO (Discharger ResultT) := do
  match discharger.task with
  | some _ => return discharger
  -- This will start the task eagerly
  | none =>
    let task ← discharger.mkTask
    return { discharger with task := some task }

def Discharger.status (discharger : Discharger ResultT) : BaseIO (DischargeStatus ResultT) := do
  let resultTask := discharger.resultPromise.result?
  match ← IO.hasFinished resultTask with
  | true =>
    match resultTask.get with
    | some res => return .finished res
    | none => panic! "Discharger.status: result promise resolved to none"
  | false =>
    match discharger.task with
    | none => return .notStarted
    | some _ => return .running

def Discharger.isSuccessful (discharger : Discharger ResultT) : BaseIO Bool := do
  match (← discharger.status) with
  | .finished (.proven _ _ _) => return true
  | _ => return false

/-- Interactive theorem dischargers take precedence over automatic dischargers:
when a VC has at least one explicit `@[veil]` theorem, only those interactive
dischargers should contribute to scheduling and aggregate status reporting. -/
def VerificationCondition.effectiveDischargers
    (vc : VerificationCondition VCMetaT ResultT) : Array (Discharger ResultT) :=
  let interactiveDischargers := vc.dischargers.filter (·.isInteractive)
  if interactiveDischargers.isEmpty then vc.dischargers else interactiveDischargers

def VerificationCondition.hasInteractiveDischarger
    (vc : VerificationCondition VCMetaT ResultT) : Bool :=
  vc.dischargers.any (·.isInteractive)

def VerificationCondition.cancelNonInteractiveDischargers
    (vc : VerificationCondition VCMetaT ResultT) : BaseIO Unit := do
  for discharger in vc.dischargers do
    unless discharger.isInteractive do
      discharger.cancelTk.set

/-- Get the start time if the promise has been resolved (i.e., the discharger has started). -/
def Discharger.startTime (discharger : Discharger ResultT) : BaseIO (Option Nat) := do
  let task := discharger.startTimePromise.result?
  if ← IO.hasFinished task then
    return task.get
  else
    return none

/-- Find the next discharger to try. Once this function returns `none`, it will
not return `some` again unless new dischargers are added. -/
def VerificationCondition.nextDischarger? (vc : VerificationCondition VCMetaT ResultT) : BaseIO (Option (Discharger ResultT)) := do
  match vc.successful with
  | some _ => return .none
  | none =>
    if vc.hasInteractiveDischarger then
      return none
    for discharger in vc.dischargers do
      match ← discharger.status with
      | .notStarted => return some discharger
      -- if the discharger is still running, wait for it to finish
      | .running => return none
      -- if the discharger is finished the VC is proven or disproven, we're done
      | .finished (.proven _ _ _)  | .finished (.disproven _ _) => return none
      | .finished (.unknown _ _) => continue
      | .finished (.error _ _) => continue
    return none

def VCManager.readyTasks (mgr : VCManager VCMetaT ResultT)
    (filter : VCMetaT → Bool := fun _ => true) : BaseIO (List (VerificationCondition VCMetaT ResultT × Discharger ResultT)) := do
  let ready ← mgr.inDegree.toList.filterMapM (fun (vcId, inDegree) => do
    let .some vc := mgr.nodes[vcId]? | panic! "VCManager.readyTasks: VC {vcId} not found"
    -- Skip dormant VCs (e.g., alternative VCs waiting for their primary to fail)
    if mgr.dormantVCs.contains vcId then pure none
    -- Skip VCs that don't match the filter
    else if !filter vc.metadata then pure none
    else if inDegree != 0 then pure none else
      match ← vc.nextDischarger? with
      | some discharger => pure (some (vc, discharger))
      | none => pure none)
  return ready

/-- Set the cancellation token of every discharger in the manager. Used on
reset, so abandoned dischargers stop (cooperatively, see `Discharger.cancelTk`)
instead of running to timeout for a manager generation whose results will be
ignored. Setting the token of a finished or interactive discharger is a no-op. -/
def VCManager.cancelAllDischargers (mgr : VCManager VCMetaT ResultT) : BaseIO Unit := do
  for (_, vc) in mgr.nodes do
    for discharger in vc.dischargers do
      discharger.cancelTk.set

private def dischargerErrorIsTimeout (res : DischargerResult ResultT) : Bool :=
  match res with
  | .error exs _ =>
    exs.any fun (_, json) =>
      match json with
      | .str s => unknownExplanation? s == some .timeout
      | _ => false
  | _ => false

/-- Compute the final status for a VC whose dischargers have been exhausted.
Concrete outcomes take priority, and among failures a non-timeout `error`
outranks `unknown`; we only report `timeout` when every recorded error was a
timeout. -/
private def VCManager.exhaustedVCStatus (mgr : VCManager VCMetaT ResultT)
    (vc : VerificationCondition VCMetaT ResultT) : VCStatus :=
  if vc.successful.isSome then
    .proven
  else
    let results := vc.effectiveDischargers.filterMap fun discharger =>
      mgr._dischargerResults[(vc.uid, discharger.id.dischargerId)]?
    let (hasDisproven, hasUnknown, hasError, allErrorsAreTimeout) :=
      results.foldl
        (init := (false, false, false, true))
        fun (hasDisproven, hasUnknown, hasError, allErrorsAreTimeout) result =>
          match result with
          | .disproven _ _ => (true, hasUnknown, hasError, allErrorsAreTimeout)
          | .unknown _ _ => (hasDisproven, true, hasError, allErrorsAreTimeout)
          | .error _ _ =>
            (hasDisproven, hasUnknown, true, allErrorsAreTimeout && dischargerErrorIsTimeout result)
          | .proven _ _ _ => (hasDisproven, hasUnknown, hasError, allErrorsAreTimeout)
    if hasDisproven then
      .disproven
    else if hasError then
      if allErrorsAreTimeout then .timeout else .error
    else if hasUnknown then
      .unknown
    else
      .unknown

def VCManager.markDischarger (mgr : VCManager VCMetaT ResultT) (id : DischargerIdentifier) (res : DischargerResult ResultT): BaseIO (VCManager VCMetaT ResultT) := do
  let mut mgr := mgr
  let vcId := id.vcId
  let mut .some vc := mgr.nodes[vcId]? | dbg_trace "VCManager.markDischarger: VC {vcId} not found"; return mgr
  let incomingIsInteractive := match vc.dischargers[id.dischargerId]? with
    | some discharger => discharger.isInteractive
    | none => false
  if vc.hasInteractiveDischarger && !incomingIsInteractive then
    return mgr
  let wasAlreadySuccessful := vc.successful.isSome
  if incomingIsInteractive then
    vc.cancelNonInteractiveDischargers
    if wasAlreadySuccessful then
      vc := { vc with successful := none }
      mgr := { mgr with
        nodes := mgr.nodes.insert vcId vc
        _doneWith := mgr._doneWith.erase vcId }
  let mut vcStatus := .unknown
  -- Store the discharger result for JSON serialization
  mgr := { mgr with _dischargerResults := mgr._dischargerResults.insert (vcId, id.dischargerId) res }
  -- A late failure from another discharger must not undo a proof we already recorded.
  if vc.successful.isSome && !res.isSuccessful && !incomingIsInteractive then
    return { mgr with _doneWith := mgr._doneWith.insert vcId .proven }
  -- Update downstream in-degrees
  match res with
  | .proven _ _ _ => do
    vcStatus := .proven
    if vc.successful.isNone then
      vc := { vc with successful := some id.dischargerId }
      mgr := { mgr with nodes := mgr.nodes.insert vcId vc }
      unless wasAlreadySuccessful do
        let downstream := match mgr.downstream[vcId]? with
        | some downstream => downstream
        | none => HashSet.emptyWithCapacity 0
        for downstreamVc in downstream do
          let .some downstreamInDegree := mgr.inDegree[downstreamVc]? | dbg_trace "VCManager.markDischarger: VC {downstreamVc} not found in the in-degree map"; return mgr
          mgr := { mgr with inDegree := mgr.inDegree.insert downstreamVc (downstreamInDegree - 1) }
  | .disproven _ _ => vcStatus := .disproven
  | .unknown _ _ => vcStatus := .unknown
  | .error _ _ => vcStatus := .error
  let .some vc' := mgr.nodes[vcId]? | dbg_trace "VCManager.markDischarger: VC {vcId} disappeared"; return mgr
  -- Mark that we're done with this VC (if we've been successful or there are no more dischargers to try)
  if vc'.successful.isSome || (← vc'.nextDischarger?).isNone then
    vcStatus := mgr.exhaustedVCStatus vc'
    mgr := { mgr with _doneWith := mgr._doneWith.insert vcId vcStatus }
    -- Trigger alternative VCs if this VC failed (not proven)
    if vcStatus != .proven && !vc'.hasInteractiveDischarger then
      if let .some altIds := mgr.alternativeVCs[vcId]? then
        for altId in altIds do
          -- Wake up the alternative VC by removing from dormant set
          mgr := { mgr with dormantVCs := mgr.dormantVCs.erase altId }
  return mgr

/-- Record a finished discharger result, updating aggregate counters and VC
status bookkeeping together. -/
def VCManager.recordDischargerResult (mgr : VCManager VCMetaT ResultT)
    (id : DischargerIdentifier) (res : DischargerResult ResultT) :
    BaseIO (VCManager VCMetaT ResultT) := do
  let alreadySolved := match mgr.nodes[id.vcId]? with
    | some vc => vc.successful.isSome
    | none => false
  let mut mgr := { mgr with _totalDischarged := mgr._totalDischarged + 1 }
  if res.isSuccessful && !alreadySolved then
    mgr := { mgr with _totalSolved := mgr._totalSolved + 1 }
  mgr.markDischarger id res

def VCManager.statusEmoji (mgr : VCManager VCMetaT ResultT) (vcId : VCId) : String := Id.run do
  match mgr._doneWith[vcId]? with
  | some vcStatus => vcStatus.emoji
  | none => "❓❓❓"

/-- Find a VC matching the given filter, returning its ID if found.
Used to avoid creating duplicate VCs for the same trace query. -/
def VCManager.findVCByFilter (mgr : VCManager VCMetaT ResultT) (filter : VCMetaT → Bool)
    : Option VCId :=
  mgr.nodes.toArray.findSome? fun (vcId, vc) =>
    if filter vc.metadata then some vcId else none

/-- Check if all VCs are done. A VC is considered "done" if it's either:
- In `_doneWith` (has been processed), or
- In `dormantVCs` (is dormant and won't be processed because its primary succeeded)
This correctly handles alternative VCs that remain dormant when their primary succeeds. -/
def VCManager.isDone (mgr : VCManager VCMetaT ResultT) : Bool :=
  mgr._doneWith.size + mgr.dormantVCs.size == mgr.nodes.size

/-- Check if all VCs matching the filter are done. -/
def VCManager.isDoneFiltered (mgr : VCManager VCMetaT ResultT) (filter : VCMetaT → Bool) : Bool :=
  mgr.nodes.toArray.all fun (vcId, vc) =>
    !filter vc.metadata || mgr._doneWith.contains vcId || mgr.dormantVCs.contains vcId

instance (priority := low) printDependencies [ToMessageData VCMetaT] : ToMessageData (VCManager VCMetaT ResultT) where
  toMessageData mgr :=
    let nodes := mgr.nodes.toList.map (fun (uid, vc) => m!"[{uid}] {vc.name} depends on {mgr.upstream[uid]!.toList.map (fun dep => m!"{dep}")} (in-degree: {mgr.inDegree[uid]!}) {vc.metadata}")
    MessageData.joinSep nodes "\n"

instance printResults [ToMessageData VCMetaT] : ToMessageData (VCManager VCMetaT ResultT) where
    toMessageData mgr :=
    let nodes := mgr.nodes.toList.map (fun (uid, vc) => m!"[{uid}] {vc.name} {mgr.statusEmoji vc.uid}")
    MessageData.joinSep nodes "\n"

end VCManager

end Veil
