import Veil

/-!
# Regression tests for the compiled-command registry and build folders

`#model_check` and `#simulate` can both appear in the same file, and either can
appear several times. These tests pin down two properties of
`Veil/Frontend/DSL/Module/Util/ForModelChecker.lean` that this relies on:

* the registry is keyed per command *invocation*, so concurrent compilations in
  one file do not supersede — and therefore kill — each other;
* the build folder is reused across invocations of the same command, keeping the
  Lake build cache while refreshing the generated inputs.

The `sourceFile` values below are identities only: they are hashed and split for
their stem, never opened. They are written as bare file names so that nothing
here depends on the platform's path syntax.
-/

open Veil.ModelChecker.Compilation

/-- Fail with a readable message; `assert!` panics with a backtrace instead. -/
private def expect (message : String) (cond : Bool) : IO Unit :=
  unless cond do throw (IO.userError message)

private def modelCheckCommand : CompiledCommandSpec := {
  exportedName := "modelCheckerResult"
  supportsParallelConfig := true
}

private def simulateCommand : CompiledCommandSpec := {
  exportedName := "simulateResult"
}

private def registryKeySourceFile := "compilation-registry-key.lean"

-- The build folder depends on the command, but not on the individual invocation.
#eval do
  let modelCheckFolderA ← generateBuildFolderName registryKeySourceFile modelCheckCommand "model-check-a"
  let modelCheckFolderB ← generateBuildFolderName registryKeySourceFile modelCheckCommand "model-check-b"
  let simulateFolderA ← generateBuildFolderName registryKeySourceFile simulateCommand "simulate-a"
  expect "two invocations of the same command must share a build folder"
    (toString modelCheckFolderA == toString modelCheckFolderB)
  expect "#model_check and #simulate must not share a build folder"
    (toString modelCheckFolderA != toString simulateFolderA)

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
  let firstFolder ← createBuildFolder sourceFile firstSource "CacheFirst" simulateCommand "simulate-cache"
  try
    let cacheDir := firstFolder / ".lake" / "build"
    let cacheSentinel := cacheDir / "cache-sentinel"
    IO.FS.createDirAll cacheDir
    IO.FS.writeFile cacheSentinel "cached"
    let secondFolder ← createBuildFolder sourceFile secondSource "CacheSecond" simulateCommand "simulate-cache"
    expect "recompiling must reuse the same build folder"
      (toString firstFolder == toString secondFolder)
    expect "recompiling must not discard the Lake build cache"
      (← cacheSentinel.pathExists)
    expect "Model.lean must be rewritten with the current model source"
      ((← IO.FS.readFile (secondFolder / "Model.lean")) == secondSource)
    expect "ModelCheckerMain.lean must be rewritten for the current specification"
      ((← IO.FS.readFile (secondFolder / "ModelCheckerMain.lean"))
        == modelCheckerMainTemplate "CacheSecond" simulateCommand)
    expect "lakefile.lean must match the current template"
      ((← IO.FS.readFile (secondFolder / "lakefile.lean")) == lakefileTemplate)
  finally
    -- Do not leave the scratch project behind in the repository's `.lake`.
    if ← firstFolder.pathExists then
      IO.FS.removeDirAll firstFolder
