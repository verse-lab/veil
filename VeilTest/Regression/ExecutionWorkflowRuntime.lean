module

public import Veil.Core.Tools.ModelChecker.CompiledRuntime
public meta import Veil
public meta import VeilTest.TestUtil
import all Veil.Frontend.DSL.Module.Util.ExecutionWorkflow

public meta section

/-!
Runtime regressions shared by model checking and simulation: elaboration,
handoff, cancellation, result publication, compilation diagnostics, and subprocess
boundaries. Direct helper checks and controlled workers avoid depending on search
speed or native compilation timing.
-/

open Lean Elab Command
open Veil Veil.ModelChecker.Concrete
open Veil.ModelChecker.Compilation

private def waitUntil (message : String) (condition : IO Bool) : IO Unit := do
  let deadline := (← IO.monoMsNow) + 10000
  while !(← condition) do
    expect s!"Timed out: {message}" ((← IO.monoMsNow) < deadline)
    IO.sleep 10

private def verdict := Json.mkObj [
  ("result", "no_violation_found"), ("explored_states", toJson (2 : Nat)),
  ("traces_run", toJson (1 : Nat))]

-- A term error must escape synchronously, without logging a recovered error or
-- generating a `main` whose body contains synthetic `sorry`.
#guard_msgs in
run_cmd do
  let badCall ← `(unknownWorkflowComputation)
  let failed ← try
    discard <| ExecutionWorkflow.generateCCode { name := "simulate" } badCall
    pure false
  catch _ => pure true
  liftIO <| expect "C generation must reject an ill-typed computation" failed
  liftIO <| expect "C generation must not leave recovered elaboration errors"
    (!(← get).messages.hasErrors)
  liftIO <| expect "failed C generation must not leave an entry point" (!(← getEnv).contains `main)

-- A simulation instance stays a simulation, keeping its configured trace budget
-- while the per-run counters restart with the compiled binary.
#eval do
  let (id, _) ← allocProgressInstance (.simulation {})
  updateSimulationProgress id "Running random traces (7/50)" 7 50 {}
  let _ ← resetProgressForHandoff id
  let after ← getProgress id
  expect "handoff must not turn a simulation into a model check" <|
    match after.details with
    | .simulation m => m.numTraces == 50 && m.tracesRun == 0
    | .modelCheck .. => false

-- A model check instance stays a model check, keeping the action labels it needs
-- to report never-enabled actions.
#eval do
  let (id, _) ← allocProgressInstance (.modelCheck { allActionLabels := ["Label.a", "Label.b"] })
  updateModelCheckProgress id 2 10 8 3
  let _ ← resetProgressForHandoff id
  let after ← getProgress id
  expect "handoff must not turn a model check into a simulation" <|
    match after.details with
    | .modelCheck m => m.allActionLabels == ["Label.a", "Label.b"] && m.diameter == 0
    | .simulation .. => false

-- The Stop button must kill the background compilation too, not just the
-- interpreted search. Before `compilationCancelTokenRef` existed, the compilation
-- token was a local in the elaborator and `requestCancellation` could not reach it,
-- so a cancelled run left its `lake build` running to completion.
#eval do
  let (id, interpretedToken) ← allocProgressInstance (.simulation {})
  let compilationToken ← IO.CancelToken.new
  setCompilationCancelToken id (some compilationToken)
  let interpretedSet ← interpretedToken.isSet
  let compilationSet ← compilationToken.isSet
  expect "no token should be set before cancellation" (!interpretedSet && !compilationSet)
  requestCancellation id
  expect "cancelling must stop the interpreted run" (← interpretedToken.isSet)
  expect "cancelling must stop the background compilation" (← compilationToken.isSet)

-- A handoff stops the interpreted run by setting the instance's own cancel token,
-- so after a handoff that token can no longer tell "the user pressed Stop" from
-- "we are handing over". The background compilation token is what separates them:
-- `requestCancellation` sets it, a handoff does not. Guarding the handover on
-- `isCancelled` instead made every `#simulate` handoff abort, leaving the run with
-- no result at all.
#eval do
  let (id, interpretedToken) ← allocProgressInstance (.simulation {})
  let compilationToken ← IO.CancelToken.new
  setCompilationCancelToken id (some compilationToken)
  requestHandoff id
  interpretedToken.set
  expect "a handoff must be recorded as requested" (← checkHandoffRequested id)
  expect "a handoff must leave the instance token looking cancelled" (← isCancelled id)
  expect "a handoff must not cancel the background compilation" (!(← compilationToken.isSet))

-- Once compilation is over its token is cleared, and a later cancellation must not
-- reach back to it.
#eval do
  let (id, _) ← allocProgressInstance (.modelCheck {})
  let compilationToken ← IO.CancelToken.new
  setCompilationCancelToken id (some compilationToken)
  setCompilationCancelToken id none
  requestCancellation id
  let compilationSet ← compilationToken.isSet
  expect "a cleared compilation token must not be cancelled" (!compilationSet)

-- Exercise the shared compilation boundary with a failing compiler, independent
-- of the installed linker. Errors must not depend on veil.violationIsError, and
-- handoff failures must leave interpreted execution running.
open Lean.Elab.Command in
private def checkCompilationFailure (handoff : Bool) : Lean.Elab.Command.CommandElabM Unit := do
  for details in [ProgressDetails.simulation {}, .modelCheck {}] do
    let (id, _) ← allocProgressInstance details
    let result ← ExecutionWorkflow.withCompilationDiagnostics (← Lean.getRef) id handoff
      (liftIO <| throw <| IO.userError "Compilation failed (test compiler)")
    liftIO <| expect "failed compilation must not return a build folder" result.isNone
    let progress ← getProgress id
    liftIO <| expect "compilation failure must be visible in progress" <|
      match progress.compilationStatus with
      | .failed _ => true
      | _ => false
    liftIO <| expect "only compiled-only failure should finish the run"
      (progress.isRunning == handoff)
    let verdict ← getResultJson id
    liftIO <| expect "handoff failure must not replace the interpreted result"
      (verdict.isNone == handoff)

set_option veil.violationIsError false in
/--
error: Compilation failed (test compiler)
---
error: Compilation failed (test compiler)
-/
#guard_msgs in
run_cmd checkCompilationFailure false

/--
warning: Compilation failed (test compiler)
---
warning: Compilation failed (test compiler)
-/
#guard_msgs in
run_cmd checkCompilationFailure true

open Lean.Elab.Command in
/-- `Command.tryCatch` rethrows interrupts, so observe one at the underlying `EIO` layer. -/
private def throwsInterrupt (x : CommandElabM Unit) : CommandElabM Bool := fun ctx s => do
  try
    x ctx s
    pure false
  catch e =>
    if e.isInterrupt then pure true else throw e

-- Successful and interrupted compilations must remain quiet in both modes.
open Lean.Elab.Command in
#guard_msgs in
run_cmd do
  for handoff in [false, true] do
    let (id, _) ← allocProgressInstance (.simulation {})
    let interrupted ← ExecutionWorkflow.withCompilationDiagnostics (← Lean.getRef) id handoff (pure none)
    liftIO <| expect "interruption must return no folder" interrupted.isNone
    -- Generating C elaborates under the command's cancellation token, so Stop can also arrive
    -- as an interrupt. `catch` rethrows it instead of reporting a failure, which is why compiled
    -- runs are ended in a `finally` (see `endRunIfCancelled`).
    let escaped ← throwsInterrupt do
      discard <| ExecutionWorkflow.withCompilationDiagnostics (← Lean.getRef) id handoff Lean.throwInterruptException
    liftIO <| expect "an interrupt must escape compilation diagnostics" escaped
    liftIO <| expect "an interrupt must not be reported as a compilation failure" <|
      match (← getProgress id).compilationStatus with
      | .failed _ => false
      | _ => true
    let folder := System.FilePath.mk "compiled-model"
    let succeeded ← ExecutionWorkflow.withCompilationDiagnostics (← Lean.getRef) id handoff (pure (some folder))
    liftIO <| expect "success must return the build folder" (succeeded == some folder)
    liftIO <| expect "interruption must not finish the run" (← getProgress id).isRunning

-- Stopping a compiled-only run during compilation leaves no verdict behind, whether the build was
-- killed or elaboration was interrupted, so the run must still end as cancelled. A run that
-- already has a verdict must keep it.
#eval do
  let (stopped, stoppedToken) ← allocProgressInstance (.modelCheck {})
  stoppedToken.set
  ExecutionWorkflow.endRunIfCancelled stoppedToken stopped
  let progress ← getProgress stopped
  expect "a run stopped during compilation must end as cancelled"
    (!progress.isRunning && progress.isCancelled)
  let (running, runningToken) ← allocProgressInstance (.modelCheck {})
  ExecutionWorkflow.endRunIfCancelled runningToken running
  expect "a run that was not stopped must keep running" (← getProgress running).isRunning
  let (finished, finishedToken) ← allocProgressInstance (.modelCheck {})
  let verdict := Lean.Json.mkObj [("result", "no_violation")]
  finishProgress finished verdict
  finishedToken.set
  ExecutionWorkflow.endRunIfCancelled finishedToken finished
  expect "a late Stop must not replace a verdict" ((← getResultJson finished) == some verdict)

-- Cancellation can land between computing a real verdict and publishing it.
-- Cover both kinds of runs, including a violation that must not be logged.
#guard_msgs in
run_cmd do
  for kind in [TraceDisplay.ResultKind.modelCheck, .simulate] do
    let details := if kind matches .simulate then ProgressDetails.simulation {} else .modelCheck {}
    for result in [verdict, Json.mkObj [("result", "found_violation")]] do
      let (id, token) ← allocProgressInstance details
      let ctx : ExecutionWorkflow.ExecutionContext := {
        stx := ← getRef, instanceId := id, cancelToken := token,
        assertionSources := {}, parallelCfg := none, resultKind := kind
      }
      token.set
      ExecutionWorkflow.finishWithResult ctx result
      let progress ← getProgress id
      liftIO <| expect "a late cancellation must finish as cancelled"
        (!progress.isRunning && progress.isCancelled)
      liftIO <| expect "a late cancellation must suppress the computed verdict"
        ((← getResultJson id) == some (Json.mkObj [("result", "cancelled")]))

-- Setting the interpreted token for handoff must still allow its completed
-- verdict to win; otherwise the native task unnecessarily repeats the search.
#guard_msgs (drop info) in
run_cmd do
  let (id, token) ← allocProgressInstance (.simulation {})
  let ctx : ExecutionWorkflow.ExecutionContext := {
    stx := ← getRef, instanceId := id, cancelToken := token,
    assertionSources := {}, parallelCfg := none, resultKind := .simulate
  }
  requestHandoff id
  token.set
  ExecutionWorkflow.finishWithResult ctx verdict
  liftIO <| expect "handoff must permit an already-computed verdict"
    ((← getResultJson id) == some verdict && !(← getProgress id).isCancelled)

-- Worker progress omits the parent's compilation state. Model-check metrics
-- also omit action labels and history; simulation metrics have no BFS history.
#eval do
  for details in [ProgressDetails.modelCheck { allActionLabels := ["Label.toggle"] }, .simulation {}] do
    let (id, token) ← allocProgressInstance details
    updateCompilationStatus id .succeeded
    let workerDetails := match details with
      | .modelCheck _ => ProgressDetails.modelCheck { diameter := 2, statesFound := 7, distinctStates := 5, queue := 3 }
      | .simulation _ => .simulation { tracesRun := 4, numTraces := 9 }
    let first : Progress := { details := workerDetails, elapsedMs := 10 }
    let last : Progress := { first with elapsedMs := 20 }
    let result ← ExecutionWorkflow.runBinaryForJson "/bin/sh"
      #["-c", "printf '%s\n' \"$1\" \"$2\" >&2; printf '%s\n' \"$3\"", "worker",
        (toJson first).compress, (toJson last).compress, verdict.compress] id token
    expect "the worker's JSON verdict must be returned" (result == some verdict)
    let progress ← getProgress id
    expect "worker progress must retain the parent's successful compilation" <|
      match progress.compilationStatus with
      | .succeeded => true
      | _ => false
    expect "all worker progress must be consumed before returning" (progress.elapsedMs == 20)
    expect "worker metrics must retain their command kind and parent metadata" <|
      match progress.details with
      | .modelCheck m => m.diameter == 2 && m.statesFound == 7 && m.distinctStates == 5 &&
          m.queue == 3 && m.allActionLabels == ["Label.toggle"] &&
          m.history.map (fun (p : ProgressHistoryPoint) => p.timestamp) == #[10, 20]
      | .simulation m => m.tracesRun == 4 && m.numTraces == 9

-- A worker's nonzero exit must reach the caller's error handler, including its
-- stderr diagnostic, rather than silently setting a result and returning `none`.
#eval do
  let (id, token) ← allocProgressInstance (.simulation {})
  let failure : Option String ← try
    discard <| ExecutionWorkflow.runBinaryForJson "/bin/sh"
      #["-c", "printf 'native worker failed\n' >&2; exit 7"] id token
    pure none
  catch e => pure (some e.toString)
  expect "a nonzero worker exit must throw with its exit code and stderr"
    (failure.any fun (msg : String) => (msg.splitOn "Binary exited with code 7").length > 1 &&
      (msg.splitOn "native worker failed").length > 1)
  expect "the caller must own error finalization" (← getProgress id).isRunning
  expect "a worker failure must not publish a result before the caller handles it"
    (← getResultJson id).isNone

-- Keep stderr open in a descendant after the main process exits (or is killed).
-- A file gate releases that reader only after the test has observed the run.
-- This reproduces late stderr deterministically, without flooding a pipe.
private def checkStderrDrain (cancel : Bool) : IO Unit := IO.FS.withTempDir fun dir => do
  let started := dir / "started"
  let release := dir / "release"
  let emitted := dir / "stderr-emitted"
  let (id, token) ← allocProgressInstance (.simulation {})
  let lateProgress : Progress := {
    status := "late worker progress", elapsedMs := 42,
    details := .simulation { tracesRun := 1, numTraces := 2 }
  }
  let script :=
    "(while [ ! -f \"$2\" ]; do sleep 0.01; done; " ++
    "printf '%s\n' \"$3\" >&2; printf 'late native diagnostic\n' >&2; touch \"$4\") </dev/null >/dev/null &\n" ++
    "touch \"$1\"\n" ++
    (if cancel then "exec sleep 30\n" else "exit 7\n")
  let run ← IO.asTask (prio := .dedicated) do
    try
      ExecutionWorkflow.runBinaryForJson "/bin/sh"
        #["-c", script, "worker", started.toString, release.toString,
          (toJson lateProgress).compress, emitted.toString] id token
    finally
      ExecutionWorkflow.endRunIfCancelled token id
  try
    waitUntil "worker startup" started.pathExists
    if cancel then
      token.set
      waitUntil "cancellation observed" ((·.isCancelled) <$> getProgress id)
    -- The workflow polls the process every 100ms. Give it multiple polls with
    -- the stderr gate closed; it must still be waiting for the reader.
    IO.sleep 300
    expect "the workflow must join stderr before returning, including on cancellation"
      (!(← IO.hasFinished run))
  finally
    IO.FS.writeFile release ""
    waitUntil "late stderr emission" emitted.pathExists
    waitUntil "worker and stderr reader completion" (IO.hasFinished run)
    let result ← IO.wait run
    if cancel then
      let json ← IO.ofExcept result
      expect "a cancelled worker must not return a verdict" json.isNone
      let progress ← getProgress id
      expect "late stderr progress must not resurrect a cancelled run"
        (!progress.isRunning && progress.isCancelled)
      expect "cancelled runs must retain the cancelled result"
        ((← getResultJson id) == some (Json.mkObj [("result", "cancelled")]))
    else
      expect "late stderr diagnostics must be included in the worker exception" <|
        match result with
        | .error e => (e.toString.splitOn "late native diagnostic").length > 1
        | .ok _ => false

#eval checkStderrDrain false
#eval checkStderrDrain true

-- Exercise the actual end-of-run cleanup and its default option, using an
-- isolated working directory so concurrently compiled tests cannot prune it.
open Lean Elab Command in
run_cmd do
  let cwd ← IO.currentDir
  IO.FS.withTempDir fun dir => do
    try
      IO.Process.setCurrentDir dir
      let base ← getBuildBaseDir
      let folder := base / "completed"
      let (idle, idleToken) ← allocProgressInstance (.modelCheck {})
      discard <| withBuildLock base idleToken do
        useBuildFolder idle folder
        releaseBuildFolder idle
      let (id, _) ← allocProgressInstance (.modelCheck {})
      discard <| withBuildLock base (← IO.CancelToken.new) (useBuildFolder id folder)
      ExecutionWorkflow.releaseBuild id
      liftIO <| expect "default cleanup must retain the completed build for reuse" (← folder.pathExists)
      -- Once released it must remain eligible for a later eviction.
      pruneBuildFolders base 0
      liftIO <| expect "cleanup must release the build's use lock" (!(← folder.pathExists))
    finally
      IO.Process.setCurrentDir cwd
