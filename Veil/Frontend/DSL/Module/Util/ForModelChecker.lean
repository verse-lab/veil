import Veil.Core.UI.Widget.ProgressViewer

namespace Veil.ModelChecker.Compilation

open Lean Meta Elab Command

/-- Status of the model checker compilation process. -/
inductive Status
  | notStarted
  | inProgress (instanceId : Nat)
  | finished
  deriving Inhabited

/-- Global state tracking the model checker compilation status.
This is used to coordinate between `#gen_spec` (which starts compilation)
and `#model_check` (which waits for compilation to finish). -/
initialize statusRef : Std.Mutex Status ← Std.Mutex.new .notStarted

@[inline]
private def stillCurrentCont (instanceId : Nat) (k : Std.AtomicT Status IO Unit) : IO Bool :=
  statusRef.atomically fun ref => do
    match (← ref.get) with
    | .inProgress id => if id == instanceId then k ref ; pure true else pure false
    | _ => pure false

def updateElapsedTimeStatus (instanceId : Nat) (statusPrefix : String) : IO Unit := do
  if let some refs ← ModelChecker.Concrete.getProgressRefs instanceId then
    let elapsed := ModelChecker.formatElapsedTime (← refs.progressRef.get).elapsedMs
    ModelChecker.Concrete.updateStatus instanceId s!"{statusPrefix} ({elapsed})"

-- FIXME: bad name, since `runProcessWithStatus` is dedicated for compilation
-- either restrict the name or parameterize `stillCurrentCont`

/-- Run a process, updating status with elapsed time until it completes. -/
def runProcessWithStatus (cfg : IO.Process.SpawnArgs) (instanceId : Nat) (statusPrefix : String) : IO Unit := do
  let proc ← IO.Process.spawn { cfg with stdin := .piped, stdout := .piped, stderr := .piped }
  let waitTask ← IO.asTask (prio := .dedicated) proc.wait
  while !(← IO.hasFinished waitTask) do
    let current? ← stillCurrentCont instanceId do
      updateElapsedTimeStatus instanceId statusPrefix
    unless current? do
      proc.kill
      break
    IO.sleep 100
  -- let _ ← IO.wait waitTask

/-- Start async compilation of ModelCheckerMain in the background.
Does not display progress; that is handled by `#model_check` if needed. -/
def startCompilation : CommandElabM Unit := do
  let instanceId ← ModelChecker.Concrete.allocProgressInstance
  let cwd ← IO.currentDir
  -- Update state to inProgress
  statusRef.atomically (fun ref => ref.set (.inProgress instanceId))
  let _ ← IO.asTask (prio := .dedicated) do
    -- Compile
    runProcessWithStatus { cmd := "lake", args := #["build", "ModelCheckerMain"], cwd } instanceId "Compiling"
    -- Mark as idle if still current
    let _ ← stillCurrentCont instanceId fun ref => do
      ref.set .finished
      ModelChecker.Concrete.finishProgress instanceId (Json.mkObj [("status", "compiled")])

def pollForCompilationResult (compilationInstanceId runninginstanceId : Nat) : IO Unit := do
  while true do
    let canBreak? ← statusRef.atomically fun ref => do
      match ← ref.get with
      | .finished => pure true
      | .inProgress id' =>
        if id' == compilationInstanceId
        then
          updateElapsedTimeStatus compilationInstanceId "Compiling"
          -- Mirror the compilation progress to our instance
          if let some compilationRefs ← ModelChecker.Concrete.getProgressRefs compilationInstanceId then
            let compilationProgress ← compilationRefs.progressRef.get
            if let some refs ← ModelChecker.Concrete.getProgressRefs runninginstanceId then
              refs.progressRef.set compilationProgress
        pure false
      | .notStarted => pure true    -- This should not happen, but if it happens then
    if canBreak? then break
    IO.sleep 100

end Veil.ModelChecker.Compilation
