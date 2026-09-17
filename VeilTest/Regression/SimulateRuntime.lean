import Veil

/-!
Runtime regressions shared by simulation and model checking: progress survives
handoff, cancellation reaches compilation, command invocations do not collide in the
compilation registry, model checker builds run one at a time, and pruning never deletes a build
folder in use. These direct checks avoid relying on compilation timing to trigger a handoff.
-/

open Veil Veil.ModelChecker.Simulation Veil.ModelChecker.Concrete
open Veil.ModelChecker.Compilation

private def expect (message : String) (cond : Bool) : IO Unit :=
  unless cond do throw (IO.userError message)

-- Large budgets must keep histogram storage bounded while covering every depth.
#eval do
  let h := depthHistogramFor 100000
  expect "bucket count must be capped" (h.counts.size == Histogram.maxBuckets)
  expect "buckets must span the whole budget"
    (h.counts.size * h.bucketWidth ≥ 100000 + 2)

-- A simulation instance stays a simulation, keeping its configured trace budget
-- while the per-run counters restart with the compiled binary.
#eval do
  let (id, _) ← allocProgressInstance (.simulation {})
  let h := [0, 1, 1, 1, 2, 4, 99].foldl Histogram.record (depthHistogramFor 3)
  expect "depths must be counted, with overflow in the last bucket"
    (h.counts == #[1, 3, 1, 0, 2] && h.total == 7)
  updateSimulationProgress id "Running random traces (7/50)" 7 50 h
  let before ← getProgress id
  expect "a simulation instance must report simulation metrics" <|
    match before.details with
    | .simulation m => m.tracesRun == 7 && m.numTraces == 50 && m.depthHistogram.counts == h.counts
    | .modelCheck .. => false
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

private def modelCheckCommand : CompiledCommandSpec := {
  name := "model_check"
}

private def simulateCommand : CompiledCommandSpec := {
  name := "simulate"
}

private def registryKeySourceFile := "compilation-registry-key.lean"

-- Build folders distinguish command kinds, even for identical generated inputs.
#eval do
  let modelCheckFolder ← generateBuildFolderName registryKeySourceFile modelCheckCommand "/* C */" #[`Veil]
  let simulateFolder ← generateBuildFolderName registryKeySourceFile simulateCommand "/* C */" #[`Veil]
  expect "#model_check and #simulate must not share a build folder"
    (toString modelCheckFolder != toString simulateFolder)

-- Build folders are keyed by the generated program: an unchanged check reuses its folder so Lake
-- can skip the build, while a change to the program or linked modules gets a folder of its own.
#eval do
  let folder ← generateBuildFolderName registryKeySourceFile simulateCommand "/* C */" #[`Veil]
  let again ← generateBuildFolderName registryKeySourceFile simulateCommand "/* C */" #[`Veil]
  let otherC ← generateBuildFolderName registryKeySourceFile simulateCommand "/* other C */" #[`Veil]
  let otherImports ← generateBuildFolderName registryKeySourceFile simulateCommand "/* C */" #[`Veil, `Lean]
  expect "an unchanged program must reuse its build folder" (folder == again)
  expect "programs with different C must not share a build folder" (folder != otherC)
  expect "programs linking different modules must not share a build folder" (folder != otherImports)

-- Distinct invocations in one file each stay current, so none of them is killed.
#eval do
  let entries := [
    (modelCheckCommand, "model-check-a", 1),
    (modelCheckCommand, "model-check-b", 2),
    (simulateCommand, "simulate-a", 3),
    (simulateCommand, "simulate-b", 4),
    (simulateCommand, "simulate-c", 5)
  ]
  for (command, commandId, instanceId) in entries do
    markRegistryInProgress registryKeySourceFile command commandId instanceId
      (System.FilePath.mk "build" / commandId)
  for (command, commandId, instanceId) in entries do
    expect s!"compilation {commandId} was superseded by another invocation in the same file"
      (← stillCurrentCont registryKeySourceFile command commandId instanceId (pure ()))
  for (command, commandId, _) in entries do
    markRegistryFinished registryKeySourceFile command commandId
      (System.FilePath.mk "build" / commandId)

/-- A fresh directory to hold build folders. Tests that touch build folders use one instead of
`.lake/model_checker_builds`, where compiled checks in concurrently elaborated files take the build
lock and prune idle folders. -/
private def isolatedBuildBase : IO System.FilePath := IO.FS.createTempDir

-- Different programs keep independent C and dependency manifests.
#eval do
  let sourceFile := "compilation-build-folder-inputs.lean"
  let base ← isolatedBuildBase
  let firstC := "/* first program */"
  let secondC := "/* second program */"
  let firstImports := #[`Veil]
  let secondImports := #[`Veil, `Lean.Compiler.LCNF.EmitC]
  let inBase (folder : System.FilePath) := base / folder.fileName.getD ""
  let firstFolder := inBase (← generateBuildFolderName sourceFile simulateCommand firstC firstImports)
  let secondFolder := inBase (← generateBuildFolderName sourceFile simulateCommand secondC secondImports)
  for (folder, cCode, imports) in [(firstFolder, firstC, firstImports), (secondFolder, secondC, secondImports)] do
    writeBuildInputs folder cCode imports
  expect "distinct programs must not share generated files" (firstFolder != secondFolder)
  expect "the first program's C must survive the second program's"
    ((← IO.FS.readFile (firstFolder / "ModelCheckerMain.c")) == firstC)
  expect "the second program must receive its own C"
    ((← IO.FS.readFile (secondFolder / "ModelCheckerMain.c")) == secondC)
  for (folder, imports) in [(firstFolder, firstImports), (secondFolder, secondImports)] do
    expect "each program must keep its own dependency manifest"
      ((← IO.FS.readFile (folder / "imports.json")) == (Lean.toJson imports).compress)
    for name in ["lakefile.lean", "Model.lean", "ModelCheckerMain.lean", "lean-toolchain"] do
      expect s!"native compilation must not generate {name}" (!(← (folder / name).pathExists))
  IO.FS.removeDirAll base

-- Record a completed build through the same acquisition/release path used by compilation.
private def createIdleBuild (base folder : System.FilePath) : IO Unit := do
  let (id, token) ← allocProgressInstance (.modelCheck {})
  discard <| withBuildLock base token do
    useBuildFolder id folder
    releaseBuildFolder id

-- Only one model checker build runs at a time, and a check waiting for the build lock must still
-- respond to cancellation.
#eval do
  let base ← isolatedBuildBase
  let acquired ← IO.mkRef false
  let release ← IO.mkRef false
  let holder ← IO.asTask <| withBuildLock base (← IO.CancelToken.new) do
    acquired.set true
    while !(← release.get) do IO.sleep 10
  while !(← acquired.get) do IO.sleep 10
  let waiterToken ← IO.CancelToken.new
  let waiter ← IO.asTask <| withBuildLock base waiterToken (pure ())
  IO.sleep 300
  expect "a second build must wait while another build holds the lock" (!(← IO.hasFinished waiter))
  waiterToken.set
  expect "a cancelled wait for the build lock must give up" ((← IO.ofExcept (← IO.wait waiter)).isNone)
  release.set true
  expect "the holder must finish once released" ((← IO.ofExcept (← IO.wait holder)).isSome)
  expect "the build lock must be free again"
    ((← withBuildLock base (← IO.CancelToken.new) (pure ())).isSome)
  IO.FS.removeDirAll base

-- A superseded compilation must leave the queue while another build still holds the lock.
#eval do
  let base ← isolatedBuildBase
  let lock ← IO.FS.Handle.mk (base / "build.lock") .write
  let token ← IO.CancelToken.new
  let ran ← IO.mkRef false
  let source := "superseded-lock-wait.lean"
  markRegistryInProgress source modelCheckCommand "check" 10 base
  expect "test must acquire the build lock" (← lock.tryLock)
  let waiter ← IO.asTask (prio := .dedicated) <|
    withBuildLock base token (ran.set true)
      (isCurrent := stillCurrentCont source modelCheckCommand "check" 10 (pure ()))
  try
    IO.sleep 200
    expect "the current invocation must wait" (!(← IO.hasFinished waiter))
    markRegistryInProgress source modelCheckCommand "check" 11 base
    for _ in [:200] do
      if ← IO.hasFinished waiter then break
      IO.sleep 10
    expect "superseded invocation must stop waiting before the lock is released" (← IO.hasFinished waiter)
    expect "superseded invocation must not run the compiler" (!(← ran.get))
  finally
    token.set
    lock.unlock
    discard <| IO.ofExcept (← IO.wait waiter)
    IO.FS.removeDirAll base

-- Cancellation and supersession must also be checked when there is no lock contention.
#eval do
  let base ← isolatedBuildBase
  try
    let ran ← IO.mkRef false
    let token ← IO.CancelToken.new
    token.set
    let cancelled ← withBuildLock base token (ran.set true)
    let stale ← withBuildLock base (← IO.CancelToken.new) (ran.set true) (isCurrent := pure false)
    expect "uncontended cancelled/stale builds must not start" (cancelled.isNone && stale.isNone && !(← ran.get))
  finally
    IO.FS.removeDirAll base

-- Pruning keeps the most recently compiled builds and deletes the rest, but never a folder a check
-- is still using: a build that finished compiling but has not run its binary yet would lose it.
#eval do
  let base ← isolatedBuildBase
  let folders := #["oldest", "middle", "newest"].map fun (name : String) => base / name
  for folder in folders do
    createIdleBuild base folder
    -- Distinct usage times, independent of generated input files.
    IO.sleep 20
  IO.FS.writeFile (folders[0]! / "imports.json") "[]"
  pruneBuildFolders base 2
  expect "pruning must delete builds beyond the most recent ones" (!(← folders[0]!.pathExists))
  expect "pruning must keep the most recent builds"
    ((← folders[1]!.pathExists) && (← folders[2]!.pathExists))
  let (id, _) ← allocProgressInstance (.simulation {})
  discard <| withBuildLock base (← IO.CancelToken.new) (useBuildFolder id folders[1]!)
  pruneBuildFolders base 0
  expect "pruning must not delete a folder a check is using" (← folders[1]!.pathExists)
  expect "pruning to zero builds must delete idle folders" (!(← folders[2]!.pathExists))
  releaseBuildFolder id
  pruneBuildFolders base 0
  expect "a released folder must be pruned" (!(← folders[1]!.pathExists))
  IO.FS.removeDirAll base

-- Cleanup must not wait for a different compilation, including when reached
-- while unwinding a cancelled run. Release the lock even if this check fails.
#eval do
  let base ← isolatedBuildBase
  let folder := base / "idle"
  createIdleBuild base folder
  let lock ← IO.FS.Handle.mk (base / "build.lock") .write
  expect "test must acquire the build lock" (← lock.tryLock)
  let cleanup ← IO.asTask (prio := .dedicated) (pruneBuildFolders base 0)
  try
    for _ in [:200] do
      if ← IO.hasFinished cleanup then break
      IO.sleep 10
    expect "pruning must return while another build holds the lock" (← IO.hasFinished cleanup)
    expect "skipped pruning must leave the build alone" (← folder.pathExists)
  finally
    lock.unlock
    discard <| IO.ofExcept (← IO.wait cleanup)
    IO.FS.removeDirAll base

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
      createIdleBuild base folder
      let (id, _) ← allocProgressInstance (.modelCheck {})
      discard <| withBuildLock base (← IO.CancelToken.new) (useBuildFolder id folder)
      elabModelCheck.releaseBuild id
      liftIO <| expect "default cleanup must retain the completed build for reuse" (← folder.pathExists)
      -- Once released it must remain eligible for a later eviction.
      pruneBuildFolders base 0
      liftIO <| expect "cleanup must release the build's use lock" (!(← folder.pathExists))
    finally
      IO.Process.setCurrentDir cwd

-- Stopping a compiled-only run during compilation leaves no verdict behind, whether the build was
-- killed or elaboration was interrupted, so the run must still end as cancelled. A run that
-- already has a verdict must keep it.
#eval do
  let (stopped, stoppedToken) ← allocProgressInstance (.modelCheck {})
  stoppedToken.set
  elabModelCheck.endRunIfCancelled stoppedToken stopped
  let progress ← getProgress stopped
  expect "a run stopped during compilation must end as cancelled"
    (!progress.isRunning && progress.isCancelled)
  let (running, runningToken) ← allocProgressInstance (.modelCheck {})
  elabModelCheck.endRunIfCancelled runningToken running
  expect "a run that was not stopped must keep running" (← getProgress running).isRunning
  let (finished, finishedToken) ← allocProgressInstance (.modelCheck {})
  let verdict := Lean.Json.mkObj [("result", "no_violation")]
  finishProgress finished verdict
  finishedToken.set
  elabModelCheck.endRunIfCancelled finishedToken finished
  expect "a late Stop must not replace a verdict" ((← getResultJson finished) == some verdict)

-- Exercise the shared compilation boundary with a failing compiler, independent
-- of the installed linker. Errors must not depend on veil.violationIsError, and
-- handoff failures must leave interpreted execution running.
open Lean.Elab.Command in
private def checkCompilationFailure (handoff : Bool) : Lean.Elab.Command.CommandElabM Unit := do
  for details in [ProgressDetails.simulation {}, .modelCheck {}] do
    let (id, _) ← allocProgressInstance details
    let result ← withCompilationDiagnostics (← Lean.getRef) id handoff
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
    let interrupted ← withCompilationDiagnostics (← Lean.getRef) id handoff (pure none)
    liftIO <| expect "interruption must return no folder" interrupted.isNone
    -- Generating C elaborates under the command's cancellation token, so Stop can also arrive
    -- as an interrupt. `catch` rethrows it instead of reporting a failure, which is why compiled
    -- runs are ended in a `finally` (see `endRunIfCancelled`).
    let escaped ← throwsInterrupt do
      discard <| withCompilationDiagnostics (← Lean.getRef) id handoff Lean.throwInterruptException
    liftIO <| expect "an interrupt must escape compilation diagnostics" escaped
    liftIO <| expect "an interrupt must not be reported as a compilation failure" <|
      match (← getProgress id).compilationStatus with
      | .failed _ => false
      | _ => true
    let folder := System.FilePath.mk "compiled-model"
    let succeeded ← withCompilationDiagnostics (← Lean.getRef) id handoff (pure (some folder))
    liftIO <| expect "success must return the build folder" (succeeded == some folder)
    liftIO <| expect "interruption must not finish the run" (← getProgress id).isRunning
