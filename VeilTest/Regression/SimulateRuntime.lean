import Veil

/-!
Runtime regressions shared by simulation and model checking: progress survives
handoff, cancellation reaches compilation, and command invocations do not collide
in the compilation registry or discard cached builds. These direct checks avoid
relying on compilation timing to trigger a handoff.
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
  exportedName := "modelCheckerResult"
  supportsParallelConfig := true
}

private def simulateCommand : CompiledCommandSpec := {
  exportedName := "simulateResult"
}

private def registryKeySourceFile := "compilation-registry-key.lean"

-- The build folder depends on the command but not on the individual invocation;
-- the latter is now enforced by the signature of `generateBuildFolderName`, which
-- cannot see the command id at all.
#eval do
  let modelCheckFolder ← generateBuildFolderName registryKeySourceFile modelCheckCommand
  let simulateFolder ← generateBuildFolderName registryKeySourceFile simulateCommand
  expect "#model_check and #simulate must not share a build folder"
    (toString modelCheckFolder != toString simulateFolder)

-- Two files with the same name in different directories must not collide. Keying
-- the folder on the file stem alone used to let them clobber each other's
-- generated sources while both were registered as current.
#eval do
  let inOneDir ← generateBuildFolderName (System.mkFilePath ["one", "Shared.lean"]).toString simulateCommand
  let inAnother ← generateBuildFolderName (System.mkFilePath ["two", "Shared.lean"]).toString simulateCommand
  expect "same-named files in different directories must not share a build folder"
    (toString inOneDir != toString inAnother)

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

-- Recompiling reuses the folder, keeping the Lake cache but refreshing the inputs.
#eval do
  let sourceFile := "compilation-build-folder-cache.lean"
  let firstSource := "namespace CacheFirst\nend CacheFirst\n"
  let secondSource := "namespace CacheSecond\nend CacheSecond\n"
  let firstFolder ← createBuildFolder sourceFile firstSource "CacheFirst" simulateCommand
  try
    let cacheDir := firstFolder / ".lake" / "build"
    let cacheSentinel := cacheDir / "cache-sentinel"
    IO.FS.createDirAll cacheDir
    IO.FS.writeFile cacheSentinel "cached"
    let secondFolder ← createBuildFolder sourceFile secondSource "CacheSecond" simulateCommand
    expect "recompiling must reuse the same build folder"
      (toString firstFolder == toString secondFolder)
    expect "recompiling must not discard the Lake build cache"
      (← cacheSentinel.pathExists)
    expect "Model.lean must be rewritten with the current model source"
      ((← IO.FS.readFile (secondFolder / "Model.lean")) == secondSource)
    expect "ModelCheckerMain.lean must be rewritten for the current specification"
      ((← IO.FS.readFile (secondFolder / "ModelCheckerMain.lean"))
        == modelCheckerMainTemplate "CacheSecond" simulateCommand)
  finally
    -- Do not leave the scratch project behind in the repository's `.lake`.
    if ← firstFolder.pathExists then
      IO.FS.removeDirAll firstFolder
