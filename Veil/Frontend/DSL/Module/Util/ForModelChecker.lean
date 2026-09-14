import Veil.Core.UI.Widget.ProgressViewer

namespace Veil.ModelChecker.Compilation

open Lean Meta Elab Command

/-- Status of the model checker compilation process for a single model. -/
inductive Status
  | inProgress (instanceId : Nat) (buildDir : System.FilePath)
  | finished (buildDir : System.FilePath)
  deriving Inhabited

/-- Description of a command that can be compiled into a generated executable. -/
structure CompiledCommandSpec where
  /-- Short identifier of the command, used in registry keys and build folder names. -/
  name : String

/-- Registry key for one compiled command invocation. -/
structure CompilationKey where
  /-- Source file containing the compiled command invocation. -/
  sourceFile : String
  /-- Identifier of the compiled command, from `CompiledCommandSpec.name`. -/
  commandName : String
  /-- Identity of the specific command invocation within `sourceFile`. -/
  commandId : String
  deriving BEq, Hashable, Inhabited

/-- Global state tracking compilation status for multiple compiled commands.
    Keyed by source file path, command name, and command identity so
    different command invocations in the same file do not supersede each other.
    Uses `Std.Mutex` to prevent race conditions when multiple tasks access the registry. -/
initialize compilationRegistry : Std.Mutex (Std.HashMap CompilationKey Status) ←
  Std.Mutex.new {}

@[inline]
def mkCompilationKey (sourceFile : String) (command : CompiledCommandSpec) (commandId : String) : CompilationKey := {
  sourceFile,
  commandName := command.name,
  commandId,
}

@[inline]
def stillCurrentCont (sourceFile : String) (command : CompiledCommandSpec) (commandId : String) (instanceId : Nat)
    (k : Std.AtomicT (Std.HashMap CompilationKey Status) IO Unit) : IO Bool :=
  compilationRegistry.atomically fun ref => do
    let registry ← ref.get
    match registry[mkCompilationKey sourceFile command commandId]? with
    | some (.inProgress id _) => if id == instanceId then k ref; pure true else pure false
    | _ => pure false

private def setRegistryStatus (sourceFile : String) (command : CompiledCommandSpec) (commandId : String)
    (status : Status) : IO Unit :=
  compilationRegistry.atomically fun ref =>
    ref.modify (·.insert (mkCompilationKey sourceFile command commandId) status)

/-- Mark compilation as finished in the registry. -/
def markRegistryFinished (sourceFile : String) (command : CompiledCommandSpec) (commandId : String)
    (buildFolder : System.FilePath) : IO Unit :=
  setRegistryStatus sourceFile command commandId (.finished buildFolder)

/-- Mark compilation as in progress in the registry. -/
def markRegistryInProgress (sourceFile : String) (command : CompiledCommandSpec) (commandId : String)
    (instanceId : Nat) (buildFolder : System.FilePath) : IO Unit :=
  setRegistryStatus sourceFile command commandId (.inProgress instanceId buildFolder)

/-- Base directory for model checker build folders. This is an absolute path. -/
def getBuildBaseDir : IO System.FilePath := do
  let pwd ← IO.currentDir
  return pwd / ".lake" / "model_checker_builds"

/-- The `lake` executable that builds model checker binaries. Lake exports its own path as
`LAKE` to the processes it starts, including the language server, so this is the `lake` that
launched the current process; without it, fall back to the one in the running toolchain. -/
def getLakeExecutable : IO System.FilePath := do
  if let some lake ← IO.getEnv "LAKE" then
    unless lake.isEmpty do return lake
  return (← Lean.findSysroot) / "bin" / System.FilePath.addExtension "lake" System.FilePath.exeExtension

/-- Build folder for one generated program, named after its C and the modules it links against.
Checks that emit the same program share a folder, so re-running an unchanged check lets Lake skip
the C compilation and the link instead of producing another binary. Touch a folder only inside
`withBuildLock`, after marking it as in use with `useBuildFolder`. -/
def generateBuildFolderName (sourceFile : String) (command : CompiledCommandSpec)
    (cCode : String) (imports : Array Name) : IO System.FilePath := do
  let stem := System.FilePath.mk sourceFile |>.fileStem.getD "unrecognized_model"
  let baseDir ← getBuildBaseDir
  return baseDir / s!"{stem}_{command.name}_{mixHash (hash cCode) (hash imports)}"

/-- Entry point shared by the generated model checker executables. -/
def runMain (check : Option ModelChecker.ParallelConfig → Nat → IO.CancelToken → IO Json) (args : List String) : IO Unit := do
  let _ ← IO.asTask (prio := .dedicated) exitWhenParentDies
  -- Enable progress reporting to stderr for the IDE to read
  Veil.ModelChecker.Concrete.enableCompiledModeProgress
  let pcfg : Option Veil.ModelChecker.ParallelConfig :=
    match args with
    | a :: b :: args' =>
      let numSubSteps := args'.head?.bind String.toNat? |>.getD 1
      match a.toNat?, b.toNat? with
      | some numSubTasks, some thresholdToParallel => some { numSubTasks, thresholdToParallel, numSubSteps : Veil.ModelChecker.ParallelConfig }
      | _, _ => none
    | _ => none
  -- Instance ID is not used in compiled mode, pass 0
  -- Cancel token is created locally; cancellation is handled by killing the process from outside
  let cancelTk ← IO.CancelToken.new
  let res ← check pcfg 0 cancelTk
  IO.println s!"{res}"
  flushStdoutAndStderr
  IO.Process.forceExit 0
where
  flushStdoutAndStderr : IO Unit := do
    let stdout ← IO.getStdout
    let stderr ← IO.getStderr
    stdout.flush
    stderr.flush
  exitWhenParentDies : IO Unit := do
    let stdin ← IO.getStdin
    let _ ← stdin.readToEnd
    flushStdoutAndStderr
    IO.Process.forceExit 2

/-
NOTE: Locks on build folders.

A build folder is named after the program it builds, so checks that emit the same program share it,
possibly from different processes (e.g., when `lake build` and the editor both process a file).
Two file locks keep compilations and cleanups from interfering:

1. `build.lock` next to the folders, exclusive, held by `withBuildLock`. A check holds it while
   marking its folder as in use, writing the folder's inputs and building; `pruneBuildFolders` holds
   it for a whole prune.
   - Only *one* model checker build runs in a workspace at a time: builds of different programs still
     share the object files of the modules they import, and Lake deletes an object file before
     rebuilding it, so two `lake` processes building the same missing object make each other fail
     with "no such file or directory". Those objects are missing on a fresh checkout or in CI, where
     several compiled checks start building at once.
   - A check never starts using a folder while a prune deletes it. `use.lock` cannot ensure this
     itself: it is deleted along with its folder, so a check waiting for it during a deletion would
     end up locking a deleted file, whereas `build.lock` is never deleted.
2. `<folder>/use.lock`, shared, held from `useBuildFolder` until `releaseBuildFolder`, that is, from
   before the build until the run ends. A prune deletes a folder only if it can lock this
   exclusively, so it never deletes a folder a check still needs. A folder deleted before a check
   takes this lock is simply rebuilt by that check's own build.

Waiting for `build.lock` polls `tryLock` so that cancellation stays responsive, while `use.lock` is
only ever tried, never waited for. A lock is released as soon as its handle is no longer referenced,
since Lean then frees the handle and closes the file, so keep the handle alive while the lock is
needed.
-/

/-- Run `act` while holding the build lock of the build folders in `baseDir` (see the note on
build-folder locks). Returns `none` without running `act` if `cancelToken` is set while waiting. -/
def withBuildLock (baseDir : System.FilePath) (cancelToken : IO.CancelToken)
    (act : IO α) : IO (Option α) := do
  IO.FS.createDirAll baseDir
  let lock ← IO.FS.Handle.mk (baseDir / "build.lock") .write
  while !(← lock.tryLock) do
    if ← cancelToken.isSet then return none
    IO.sleep 100
  try
    return some (← act)
  finally
    -- NOTE: Besides unlocking, this keeps `lock` referenced while `act` runs. Once nothing refers
    -- to a handle, Lean frees it and closes the file, which releases its lock, so without this
    -- line the lock would be gone right after `tryLock` succeeds.
    lock.unlock

private def openUseLock (buildFolder : System.FilePath) : IO IO.FS.Handle :=
  IO.FS.Handle.mk (buildFolder / "use.lock") .write

/-- Rewritten by every compilation, so its modification time is when the folder was last used. -/
private def importsFile (buildFolder : System.FilePath) : System.FilePath :=
  buildFolder / "imports.json"

/-- Write the generated C and the names of the modules it links against, creating the folder. -/
def writeBuildInputs (buildFolder : System.FilePath) (cCode : String) (imports : Array Name) : IO Unit := do
  IO.FS.createDirAll buildFolder
  IO.FS.writeFile (buildFolder / "ModelCheckerMain.c") cCode
  IO.FS.writeFile (importsFile buildFolder) (toJson imports).compress

/-- Build folders that checks in this process are using, by progress instance, each with the
shared lock held on the folder's `use.lock`. -/
initialize buildFolderUses : IO.Ref (Std.HashMap Nat IO.FS.Handle) ← IO.mkRef {}

/-- Mark `buildFolder` as in use by `instanceId` until `releaseBuildFolder`, so that
`pruneBuildFolders` leaves it alone. Call it while holding `withBuildLock`. -/
def useBuildFolder (instanceId : Nat) (buildFolder : System.FilePath) : IO Unit := do
  IO.FS.createDirAll buildFolder
  let lock ← openUseLock buildFolder
  -- Cannot fail: a prune locks `use.lock` exclusively only while holding the build lock.
  discard <| lock.tryLock (exclusive := false)
  -- NOTE: Storing the handle is what keeps the folder marked as in use. Once nothing refers to a
  -- handle, Lean frees it and closes the file, which releases its lock, so the shared lock lasts
  -- exactly as long as this entry, until `releaseBuildFolder` removes it.
  buildFolderUses.modify (·.insert instanceId lock)

/-- Stop marking the build folder used by `instanceId` as in use. -/
def releaseBuildFolder (instanceId : Nat) : IO Unit := do
  if let some lock ← buildFolderUses.modifyGet fun uses => (uses[instanceId]?, uses.erase instanceId) then
    lock.unlock

/-- Delete the build folders in `baseDir` beyond the `keep` most recently compiled ones, skipping
any that a check is using. -/
def pruneBuildFolders (baseDir : System.FilePath) (keep : Nat) : IO Unit := do
  unless ← baseDir.isDir do return
  discard <| withBuildLock baseDir (← IO.CancelToken.new) do
    let mut folders : Array (System.FilePath × IO.FS.SystemTime) := #[]
    for entry in ← baseDir.readDir do
      unless ← entry.path.isDir do continue
      let lastUsed ← try (·.modified) <$> (importsFile entry.path).metadata catch _ => pure default
      folders := folders.push (entry.path, lastUsed)
    let newestFirst := folders.qsort fun a b => compare a.2 b.2 == .gt
    for (folder, _) in newestFirst.extract keep do
      try
        let use ← openUseLock folder
        if ← use.tryLock then
          try IO.FS.removeDirAll folder finally use.unlock
      catch _ => pure ()

/-- Result of running a compilation process. -/
structure ProcessResult where
  exitCode : UInt32
  stdout : String
  stderr : String
  interrupted : Bool := false
  deriving Inhabited

/-- Run a process with callbacks for status updates and line-by-line output capture,
checking both explicit cancellation and whether this compilation is still current. -/
def runProcessWithStatusCallback (sourceFile : String) (command : CompiledCommandSpec) (commandId : String)
    (cfg : IO.Process.SpawnArgs)
    (instanceId : Nat) (cancelToken : IO.CancelToken)
    (statusCallback : Nat → IO Unit)
    (lineCallback : String → Bool → Nat → IO Unit := fun _ _ _ => pure ())
    : IO ProcessResult := do
  let startTime ← IO.monoMsNow
  let proc ← IO.Process.spawn { cfg with stdin := .piped, stdout := .piped, stderr := .piped }
  let stdoutAccum ← IO.mkRef ""
  let stderrAccum ← IO.mkRef ""
  -- Helper to read lines from a handle
  let readLines (handle : IO.FS.Handle) (accum : IO.Ref String) (isError : Bool) : IO Unit := do
    while true do
      let line ← handle.getLine
      if line.isEmpty then break
      accum.modify (· ++ line)
      lineCallback line.trimAsciiEnd.toString isError ((← IO.monoMsNow) - startTime)
  let stdoutTask ← IO.asTask (prio := .dedicated) (readLines proc.stdout stdoutAccum false)
  let stderrTask ← IO.asTask (prio := .dedicated) (readLines proc.stderr stderrAccum true)
  let waitTask ← IO.asTask (prio := .dedicated) proc.wait
  let mut interrupted := false
  while !(← IO.hasFinished waitTask) do
    -- Stop once cancelled, or once a newer invocation of the same command supersedes this one.
    let wanted ← if ← cancelToken.isSet then pure false else
      stillCurrentCont sourceFile command commandId instanceId do
        statusCallback ((← IO.monoMsNow) - startTime)
    unless wanted do
      proc.kill
      interrupted := true
      break
    IO.sleep 500
  let _ ← IO.wait stdoutTask
  let _ ← IO.wait stderrTask
  match ← IO.wait waitTask with
  | .ok exitCode => return { exitCode, stdout := ← stdoutAccum.get, stderr := ← stderrAccum.get, interrupted }
  | .error err => return { exitCode := 1, stdout := ← stdoutAccum.get, stderr := s!"{← stderrAccum.get}\nIO error: {err}", interrupted }

end Veil.ModelChecker.Compilation
