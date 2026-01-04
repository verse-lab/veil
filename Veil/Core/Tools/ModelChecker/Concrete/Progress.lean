/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Pîrlea
-/
import Lean.Data.Json
import Std.Data.HashMap

namespace Veil.ModelChecker.Concrete
open Lean

/-- Status of background compilation. -/
inductive CompilationStatus where
  | none                          -- No background compilation
  | inProgress (elapsedMs : Nat)  -- Compilation is running
  | succeeded                     -- Compilation finished successfully
  | failed (error : String)       -- Compilation failed with error message
  deriving Inhabited, Repr

instance : ToJson CompilationStatus where
  toJson
    | .none => Json.mkObj [("status", "none")]
    | .inProgress ms => Json.mkObj [("status", "inProgress"), ("elapsedMs", ms)]
    | .succeeded => Json.mkObj [("status", "succeeded")]
    | .failed err => Json.mkObj [("status", "failed"), ("error", err)]

instance : FromJson CompilationStatus where
  fromJson? j := do
    let status ← j.getObjValAs? String "status"
    match status with
    | "none" => return .none
    | "inProgress" => return .inProgress (← j.getObjValAs? Nat "elapsedMs")
    | "succeeded" => return .succeeded
    | "failed" => return .failed (← j.getObjValAs? String "error")
    | _ => throw s!"Unknown compilation status: {status}"

/-- Progress information for model checking. -/
structure Progress where
  status : String := "Initializing..."
  uniqueStates : Nat := 0
  statesProcessed : Nat := 0
  queueLength : Nat := 0
  currentDepth : Nat := 0
  completedDepth : Nat := 0
  isRunning : Bool := true
  isCancelled : Bool := false
  startTimeMs : Nat := 0
  elapsedMs : Nat := 0
  /-- Status of background compilation (for handoff mode). -/
  compilationStatus : CompilationStatus := .none
  deriving ToJson, FromJson, Inhabited, Repr

/-- Refs for tracking progress of a single model checker instance. -/
structure ProgressRefs where
  progressRef : IO.Ref Progress
  resultRef : IO.Ref (Option Lean.Json)
  /-- Cancellation token for this instance. -/
  cancelToken : IO.CancelToken
  /-- Set by compilation task to signal interpreted mode to stop for handoff. -/
  handoffRequested : IO.Ref Bool
  /-- Set by interpreted mode when a violation is found (prevents handoff). -/
  violationFound : IO.Ref Bool

/-- Global registry mapping instance IDs to their progress refs.
    This allows passing quotable IDs through syntax while maintaining per-instance state. -/
initialize progressRegistry : IO.Ref (Std.HashMap Nat ProgressRefs) ← IO.mkRef {}
initialize nextInstanceId : IO.Ref Nat ← IO.mkRef 0

/-! ## Compiled Mode Progress Reporting

In compiled mode, the model checker runs as a separate process. Progress is communicated
via stderr (JSON lines), while the final result goes to stdout. -/

/-- Global flag indicating compiled mode (progress goes to stderr). -/
initialize compiledModeEnabled : IO.Ref Bool ← IO.mkRef false

/-- Start time for compiled mode progress tracking. -/
initialize compiledModeStartTime : IO.Ref Nat ← IO.mkRef 0

/-- Enable compiled mode progress reporting. Call this at the start of the compiled executable. -/
def enableCompiledModeProgress : IO Unit := do
  compiledModeEnabled.set true
  compiledModeStartTime.set (← IO.monoMsNow)

/-- Allocate a new progress instance and return its ID along with the cancel token. -/
def allocProgressInstance : IO (Nat × IO.CancelToken) := do
  let id ← nextInstanceId.modifyGet fun n => (n, n + 1)
  let cancelTk ← IO.CancelToken.new
  let refs : ProgressRefs := {
    progressRef := ← IO.mkRef { startTimeMs := ← IO.monoMsNow, status := "Running...", isRunning := true }
    resultRef := ← IO.mkRef none
    cancelToken := cancelTk
    handoffRequested := ← IO.mkRef false
    violationFound := ← IO.mkRef false
  }
  progressRegistry.modify fun m => m.insert id refs
  return (id, cancelTk)

/-- Get the progress refs for an instance ID. -/
def getProgressRefs (instanceId : Nat) : IO (Option ProgressRefs) := do
  return (← progressRegistry.get)[instanceId]?

/-- Run action with refs if they exist, otherwise do nothing. -/
private def withRefs (instanceId : Nat) (f : ProgressRefs → IO Unit) : IO Unit := do
  if let some refs ← getProgressRefs instanceId then f refs

/-- Update progress for a given instance ID.
    In compiled mode, also outputs progress to stderr as JSON. -/
def updateProgress (instanceId : Nat) (uniqueStates statesProcessed queueLength currentDepth completedDepth : Nat) : IO Unit := do
  let now ← IO.monoMsNow
  -- Update refs if they exist (interpreted mode)
  if let some refs ← getProgressRefs instanceId then
    refs.progressRef.modify fun p => { p with
      uniqueStates, statesProcessed, queueLength, currentDepth, completedDepth
      elapsedMs := now - p.startTimeMs }
  -- Output to stderr if in compiled mode
  if ← compiledModeEnabled.get then
    let startTime ← compiledModeStartTime.get
    let p : Progress := {
      status := "Running..."
      uniqueStates, statesProcessed, queueLength, currentDepth, completedDepth
      isRunning := true
      startTimeMs := startTime
      elapsedMs := now - startTime
    }
    IO.eprintln (toJson p).compress

/-- Update just the status and elapsed time for a given instance ID. -/
def updateStatus (instanceId : Nat) (status : String) : IO Unit := withRefs instanceId fun refs => do
  let now ← IO.monoMsNow
  refs.progressRef.modify fun p => { p with status, elapsedMs := now - p.startTimeMs }

/-- Mark progress as complete for a given instance ID. -/
def finishProgress (instanceId : Nat) (resultJson : Lean.Json) : IO Unit := withRefs instanceId fun refs => do
  let now ← IO.monoMsNow
  refs.progressRef.modify fun p => { p with status := "Complete", isRunning := false, elapsedMs := now - p.startTimeMs }
  refs.resultRef.set (some resultJson)

/-- Get current progress for an instance ID. -/
def getProgress (instanceId : Nat) : IO Progress := do
  match ← getProgressRefs instanceId with
  | some refs => refs.progressRef.get
  | none => return {}

/-- Get result JSON for an instance ID. -/
def getResultJson (instanceId : Nat) : IO (Option Lean.Json) := do
  match ← getProgressRefs instanceId with
  | some refs => refs.resultRef.get
  | none => return none

/-- Check if cancellation has been requested for an instance. -/
def isCancelled (instanceId : Nat) : IO Bool := do
  match ← getProgressRefs instanceId with
  | some refs => refs.cancelToken.isSet
  | none => return false

/-- Request cancellation for an instance. -/
def requestCancellation (instanceId : Nat) : IO Unit := withRefs instanceId (·.cancelToken.set)

/-- Mark progress as cancelled for a given instance ID. -/
def cancelProgress (instanceId : Nat) : IO Unit := withRefs instanceId fun refs => do
  let now ← IO.monoMsNow
  refs.progressRef.modify fun p => { p with
    status := "Cancelled", isRunning := false, isCancelled := true, elapsedMs := now - p.startTimeMs }
  refs.resultRef.set (some (Json.mkObj [("result", "cancelled")]))

/-! ## Handoff Coordination -/

def updateCompilationStatus (instanceId : Nat) (status : CompilationStatus) : IO Unit :=
  withRefs instanceId fun refs => refs.progressRef.modify fun p => { p with compilationStatus := status }

def requestHandoff (instanceId : Nat) : IO Unit := withRefs instanceId (·.handoffRequested.set true)

def checkHandoffRequested (instanceId : Nat) : IO Bool := do
  match ← getProgressRefs instanceId with
  | some refs => refs.handoffRequested.get
  | none => return false

/-- Check if execution should stop (cancelled or handoff requested). -/
def shouldStop (cancelToken : IO.CancelToken) (instanceId : Nat) : IO Bool :=
  return (← cancelToken.isSet) || (← checkHandoffRequested instanceId)

def setViolationFound (instanceId : Nat) : IO Unit := withRefs instanceId (·.violationFound.set true)

def isViolationFound (instanceId : Nat) : IO Bool := do
  match ← getProgressRefs instanceId with
  | some refs => refs.violationFound.get
  | none => return false

/-- Reset progress for handoff to compiled mode. Returns new cancel token. -/
def resetProgressForHandoff (instanceId : Nat) : IO (Option IO.CancelToken) := do
  let some refs ← getProgressRefs instanceId | return none
  refs.handoffRequested.set false
  let newCancelToken ← IO.CancelToken.new
  progressRegistry.modify fun m => m.insert instanceId { refs with cancelToken := newCancelToken }
  let now ← IO.monoMsNow
  refs.progressRef.set {
    status := "Restarting with compiled binary...", startTimeMs := now, compilationStatus := .succeeded
  }
  return some newCancelToken

end Veil.ModelChecker.Concrete
