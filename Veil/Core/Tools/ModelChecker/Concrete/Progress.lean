/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Pîrlea
-/
import Lean.Data.Json

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

/-- Global progress ref for the currently running model checker. -/
initialize progressRef : IO.Ref Progress ← IO.mkRef {}

/-- Global result ref for storing the final JSON result. -/
initialize resultJsonRef : IO.Ref (Option Lean.Json) ← IO.mkRef none

/-- Get current progress. -/
def getProgress : IO Progress := progressRef.get

/-- Get result JSON (if available). -/
def getResultJson : IO (Option Lean.Json) := resultJsonRef.get

/-- Initialize progress tracking before starting model checking. -/
def initProgress : IO Unit := do
  let now ← IO.monoMsNow
  progressRef.set { startTimeMs := now, status := "Running...", isRunning := true }
  resultJsonRef.set none

/-- Update progress with current search state. -/
def updateProgress (uniqueStates statesProcessed queueLength currentDepth completedDepth : Nat) : IO Unit := do
  let now ← IO.monoMsNow
  progressRef.modify fun p => { p with
    uniqueStates, statesProcessed, queueLength, currentDepth, completedDepth
    elapsedMs := now - p.startTimeMs }

/-- Mark progress as complete. -/
def finishProgress (resultJson : Lean.Json) : IO Unit := do
  let now ← IO.monoMsNow
  progressRef.modify fun p => { p with
    status := "Complete"
    isRunning := false
    elapsedMs := now - p.startTimeMs }
  resultJsonRef.set (some resultJson)

end Veil.ModelChecker.Concrete
