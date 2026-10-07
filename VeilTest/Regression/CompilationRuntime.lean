module

public meta import Veil.Frontend.DSL.Module.Util.ForModelChecker
public meta import VeilTest.TestUtil

public meta section

/-!
Regressions for shared native compilation infrastructure: generated inputs,
invocation registry keys, build serialization, and safe cache pruning.
`ExecutionWorkflowRuntime` covers how execution uses these compilation helpers.
-/

open Veil Veil.ModelChecker.Concrete Veil.ModelChecker.Compilation

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
