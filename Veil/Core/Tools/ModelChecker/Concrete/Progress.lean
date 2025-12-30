/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Pîrlea
-/
import Lean.Data.Json
import Std.Data.HashMap

namespace Veil.ModelChecker.Concrete
open Lean

/-- Progress information for model checking. -/
structure Progress where
  status : String := "Initializing..."
  uniqueStates : Nat := 0
  statesProcessed : Nat := 0
  queueLength : Nat := 0
  currentDepth : Nat := 0
  completedDepth : Nat := 0
  isRunning : Bool := true
  startTimeMs : Nat := 0
  elapsedMs : Nat := 0
  deriving ToJson, FromJson, Inhabited, Repr

/-- Refs for tracking progress of a single model checker instance. -/
structure ProgressRefs where
  progressRef : IO.Ref Progress
  resultRef : IO.Ref (Option Lean.Json)

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
  let now ← IO.monoMsNow
  compiledModeStartTime.set now

/-- Output progress to stderr as a JSON line (for compiled mode). -/
def reportProgressToStderr (p : Progress) : IO Unit := do
  IO.eprintln (toJson p).compress

/-- Allocate a new progress instance and return its ID.
    The ID can be safely quoted into Lean syntax. -/
def allocProgressInstance : IO Nat := do
  let id ← nextInstanceId.modifyGet fun n => (n, n + 1)
  let now ← IO.monoMsNow
  let pRef ← IO.mkRef { startTimeMs := now, status := "Running...", isRunning := true : Progress }
  let rRef ← IO.mkRef (none : Option Lean.Json)
  progressRegistry.modify fun m => m.insert id { progressRef := pRef, resultRef := rRef }
  return id

/-- Get the progress refs for an instance ID. -/
def getProgressRefs (instanceId : Nat) : IO (Option ProgressRefs) := do
  let m ← progressRegistry.get
  return m[instanceId]?

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
    reportProgressToStderr p

/-- Update just the status and elapsed time for a given instance ID (useful during compilation). -/
def updateStatus (instanceId : Nat) (status : String) : IO Unit := do
  let now ← IO.monoMsNow
  if let some refs ← getProgressRefs instanceId then
    refs.progressRef.modify fun p => { p with status, elapsedMs := now - p.startTimeMs }

/-- Mark progress as complete for a given instance ID. -/
def finishProgress (instanceId : Nat) (resultJson : Lean.Json) : IO Unit := do
  if let some refs ← getProgressRefs instanceId then
    let now ← IO.monoMsNow
    refs.progressRef.modify fun p => { p with
      status := "Complete"
      isRunning := false
      elapsedMs := now - p.startTimeMs }
    refs.resultRef.set (some resultJson)

/-- Get current progress for an instance ID. -/
def getProgress (instanceId : Nat) : IO Progress := do
  if let some refs ← getProgressRefs instanceId then
    refs.progressRef.get
  else
    return {}

/-- Get result JSON for an instance ID. -/
def getResultJson (instanceId : Nat) : IO (Option Lean.Json) := do
  if let some refs ← getProgressRefs instanceId then
    refs.resultRef.get
  else
    return none

end Veil.ModelChecker.Concrete
