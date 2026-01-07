import Veil.Core.Tools.Verifier.Manager
import Veil.Frontend.DSL.Infra.Metadata

namespace Veil
open Lean

instance : Lean.ToJson VCStatus where
  toJson status := Lean.Json.str status.kindString

instance [ToJson ResultT] : ToJson (DischargerResult ResultT) where
  toJson res :=
    match res with
    | .proven _ data time | .disproven data time | .unknown data time => Json.mkObj [
      ("status", Json.str res.kindString),
      ("data", toJson data),
      ("time", toJson time)
    ]
    | .error exs time => Json.mkObj [
      ("status", Json.str "error"),
      ("exceptions", Json.arr (exs.map (·.2))),
      ("time", toJson time)
    ]

instance [Server.RpcEncodable ResultT] : Server.RpcEncodable (DischargerResult ResultT) where
  rpcEncode res := do
    match res with
    | .proven _ data time | .disproven data time | .unknown data time =>
      return .mkObj [("status", Json.str res.kindString), ("data", ← Server.rpcEncode data), ("time", toJson time)]
    | .error exs time => do
      return .mkObj [("status", Json.str "error"), ("exceptions", Json.arr (exs.map (·.2))), ("time", toJson time)]
  rpcDecode _ := do return default

/-- Represents the result data for a single discharger. -/
structure DischargerResultData (ResultT : Type) where
  /-- The ID of the discharger. -/
  id : DischargerId
  /-- The name of the discharger. -/
  name : Name
  /-- The status of the discharger. -/
  status : DischargeStatus ResultT
  /-- The time taken by the discharger (in milliseconds), if available. -/
  time : Option Nat
  /-- Monotonic timestamp (ms) when the discharger started, for elapsed time display. -/
  startTime : Option Nat := none
  /-- The full result of the discharger, if available. -/
  result : Option (DischargerResult ResultT)
deriving Inhabited

instance [ToJson ResultT] : ToJson (DischargerResultData ResultT) where
  toJson data :=
    let (statusStr, time, result) := match data.status with
      | .notStarted => ("notStarted", none, none)
      | .running => ("running", none, none)
      | .finished res => (res.kindString, some res.time, some res)
    Json.mkObj [
      ("id", toJson data.id),
      ("name", toJson data.name.toString),
      ("status", Json.str statusStr),
      ("time", match time.orElse (fun _ => data.time) with | some t => toJson t | none => Json.null),
      ("startTime", match data.startTime with | some t => toJson t | none => Json.null),
      ("result", match result.orElse (fun _ => data.result) with | some r => toJson r | none => Json.null)
    ]

/-- Represents timing information for a verification condition. -/
structure TimingData (ResultT : Type) where
  /-- Total time spent on all dischargers for this VC. -/
  totalTime : Option Nat
  /-- The ID of the successful discharger, if the VC was proven. -/
  successfulDischargerId : Option DischargerId
  /-- The time taken by the successful discharger. -/
  successfulDischargerTime : Option Nat
  /-- Details of all dischargers that were run for this VC. -/
  dischargers : Array (DischargerResultData ResultT)
deriving Inhabited

instance [ToJson ResultT] : ToJson (TimingData ResultT) where
  toJson timing :=
    Json.mkObj [
      ("totalTime", match timing.totalTime with | some t => toJson t | none => Json.null),
      ("successfulDischargerId", match timing.successfulDischargerId with | some id => toJson id | none => Json.null),
      ("successfulDischargerTime", match timing.successfulDischargerTime with | some t => toJson t | none => Json.null),
      ("dischargers", Json.arr (timing.dischargers.map toJson))
    ]

/-- Represents the result of a single verification condition. -/
structure VCResult (VCMetaT ResultT : Type) where
  /-- The unique ID of the VC. -/
  id : VCId
  /-- The name of the VC. -/
  name : Name
  /-- The status of the VC: "proven", "disproven", "unknown", or "error", if determined. -/
  status : Option VCStatus
  /-- Metadata associated with this VC. -/
  metadata : VCMetaT
  /-- Timing information for this VC. -/
  timing : TimingData ResultT
  /-- If this VC is an alternative (e.g., TR-style), the ID of the primary VC it's associated with. -/
  alternativeFor : Option VCId := none
  /-- Whether this VC is currently dormant (waiting for its primary to fail). -/
  isDormant : Bool := false
  /-- The theorem statement text for inserting into the editor.
      Format: `theorem <name> <params> : <statement> := by sorry` -/
  theoremText : Option String := none
deriving Inhabited

instance [ToJson VCMetaT] [ToJson ResultT] : ToJson (VCResult VCMetaT ResultT) where
  toJson vcResult :=
    Json.mkObj [
      ("id", toJson vcResult.id),
      ("name", toJson vcResult.name.toString),
      ("status", match vcResult.status with | some s => toJson s | none => Json.null),
      ("metadata", toJson vcResult.metadata),
      ("timing", toJson vcResult.timing),
      ("alternativeFor", match vcResult.alternativeFor with | some id => toJson id | none => Json.null),
      ("isDormant", toJson vcResult.isDormant),
      ("theoremText", match vcResult.theoremText with | some t => toJson t | none => Json.null)
    ]

/-- Represents the complete verification results, mirroring the JSON structure
generated by the `ToJson` instance of `VCManager`. -/
structure VerificationResults (VCMetaT ResultT : Type) where
  /-- Array of all verification condition results. -/
  vcs : Array (VCResult VCMetaT ResultT)
  /-- Total number of VCs. -/
  totalVCs : Nat
  /-- Total number of dischargers that have finished executing. -/
  totalDischarged : Nat
  /-- Total number of VCs that have been successfully proven. -/
  totalSolved : Nat
  /-- Total time spent across all VCs (in milliseconds). -/
  totalTime : Nat
  /-- Current server monotonic time (ms), for computing elapsed time of running dischargers. -/
  serverTime : Nat
deriving Inhabited

deriving instance Server.RpcEncodable for DischargeStatus
deriving instance Server.RpcEncodable for DischargerResultData
deriving instance Server.RpcEncodable for TimingData
deriving instance Server.RpcEncodable for VCStatus
deriving instance Server.RpcEncodable for VCResult
deriving instance Server.RpcEncodable for VerificationResults

instance [ToJson VCMetaT] [ToJson ResultT] : ToJson (VerificationResults VCMetaT ResultT) where
  toJson results :=
    Json.mkObj [
      ("vcs", Json.arr (results.vcs.map toJson)),
      ("totalVCs", toJson results.totalVCs),
      ("totalDischarged", toJson results.totalDischarged),
      ("totalSolved", toJson results.totalSolved),
      ("totalTime", toJson results.totalTime),
      ("serverTime", toJson results.serverTime)
    ]

/-- Build `DischargerResultData` for a specific discharger of a VC. -/
def mkDischargerResultData [Monad m] [MonadError m] [MonadLiftT BaseIO m] (mgr : VCManager VCMetaT ResultT) (vc : VerificationCondition VCMetaT ResultT) (dischargerId : DischargerId) : m (DischargerResultData ResultT) := do
  let .some discharger := vc.dischargers[dischargerId]?
    | throwError s!"mkDischargerResultData: discharger {dischargerId} not found in VC {vc.uid}"
  let status ← discharger.status
  let result := mgr._dischargerResults[(vc.uid, dischargerId)]?
  let time := result.map (·.time)
  let startTime ← discharger.startTime
  return {
    id := dischargerId
    name := discharger.id.name
    status := status
    time := time
    startTime := startTime
    result := result
  }

/-- Calculate total time for a VC by summing all completed dischargers; returns none if none finished -/
def VCManager.vcTotalTime (mgr : VCManager VCMetaT ResultT) (vcId : VCId) : Option Nat := do
  let vc ← mgr.nodes[vcId]?
  let times := (List.range vc.dischargers.size).filterMap fun i =>
    mgr._dischargerResults[(vcId, i)]?.map (·.time)
  if times.isEmpty then none else some (times.foldl (· + ·) 0)

/-- Get time for successful discharger (if VC is proven) -/
def VCManager.vcSuccessfulTime (mgr : VCManager VCMetaT ResultT) (vcId : VCId) : Option Nat := Id.run do
  let .some vc := mgr.nodes[vcId]? | return none
  match vc.successful with
  | none => return none
  | some dischargerId =>
    match mgr._dischargerResults[(vcId, dischargerId)]? with
    | some res => return some res.time
    | none => return none

/-- Build `TimingData` for a specific VC. -/
def mkTimingData [Monad m] [MonadError m] [MonadLiftT BaseIO m] (mgr : VCManager VCMetaT ResultT) (vc : VerificationCondition VCMetaT ResultT) : m (TimingData ResultT) := do
  let dischargerDetails ← (List.range vc.dischargers.size).toArray.mapM fun i =>
    mkDischargerResultData mgr vc i
  return {
    totalTime := mgr.vcTotalTime vc.uid
    successfulDischargerId := vc.successful
    successfulDischargerTime := mgr.vcSuccessfulTime vc.uid
    dischargers := dischargerDetails
  }

/-- Find the primary VC ID for an alternative VC, if this VC is an alternative. -/
def VCManager.findPrimaryVC (mgr : VCManager VCMetaT ResultT) (vcId : VCId) : Option VCId := Id.run do
  for (primaryId, alts) in mgr.alternativeVCs.toArray do
    if alts.contains vcId then
      return some primaryId
  return none

/-- Generate theorem text from a VC using proper pretty-printing.
    Format: `theorem <name> <params> : <statement> := by sorry` -/
def mkTheoremText (vc : VerificationCondition VCMetaT ResultT) : CoreM String := do
  let cmd ← vc.theoremStx
  let fmt ← Lean.PrettyPrinter.ppCommand cmd
  return fmt.pretty

/-- Build `VCResult` for a specific VC. -/
def mkVCResult [Monad m] [MonadError m] [MonadLiftT BaseIO m] [MonadLiftT CoreM m] (mgr : VCManager VCMetaT ResultT) (vcId : VCId) : m (VCResult VCMetaT ResultT) := do
  let .some vc := mgr.nodes[vcId]? | throwError s!"mkVCResult: VC {vcId} not found in manager"
  let timing ← mkTimingData mgr vc
  -- Generate theorem text for all VCs (for click-to-insert functionality)
  let theoremText ← some <$> liftM (mkTheoremText vc)
  return {
    id := vcId
    name := vc.name
    status := mgr._doneWith[vcId]?
    metadata := vc.metadata
    timing := timing
    alternativeFor := mgr.findPrimaryVC vcId
    isDormant := mgr.dormantVCs.contains vcId
    theoremText := theoremText
  }

/-- Convert a `VCManager` to `VerificationResults`, filtering VCs by the given predicate. -/
def VCManager.toResults [Monad m] [MonadError m] [MonadLiftT BaseIO m] [MonadLiftT CoreM m]
    (mgr : VCManager VCMetadata ResultT) (filter : VCMetadata → Bool)
    : m (VerificationResults VCMetadata ResultT) := do
  let filteredNodes := mgr.nodes.toArray.filter fun (_, vc) => filter vc.metadata
  let vcResults ← filteredNodes.mapM fun (vcId, _) => mkVCResult mgr vcId

  let totalTime := filteredNodes.foldl (init := 0) fun acc (uid, _) =>
    acc + ((mgr.vcTotalTime uid).getD 0)

  let totalSolved := vcResults.filter (fun r => r.status == some .proven) |>.size
  let totalDischarged := vcResults.foldl (init := 0) fun acc r =>
    let finishedCount := r.timing.dischargers.filter (fun (d : DischargerResultData ResultT) =>
      match d.status with | .finished _ => true | _ => false) |>.size
    acc + finishedCount

  let serverTime ← IO.monoMsNow

  return {
    vcs := vcResults
    totalVCs := filteredNodes.size
    totalDischarged := totalDischarged
    totalSolved := totalSolved
    totalTime := totalTime
    serverTime := serverTime
  }

/-- Convert a `VCManager` to `VerificationResults`, filtering to only include induction VCs.
    This is used by the `#check_invariants` widget which doesn't support trace VCs. -/
def VCManager.toVerificationResults [Monad m] [MonadError m] [MonadLiftT BaseIO m] [MonadLiftT CoreM m]
    (mgr : VCManager VCMetadata ResultT) : m (VerificationResults VCMetadata ResultT) :=
  mgr.toResults (·.isInduction)

end Veil
