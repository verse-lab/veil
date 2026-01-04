import Veil.Core.UI.Widget.ProgressViewer

namespace Veil.ModelChecker.Compilation

open Lean Meta Elab Command

/-- Find the byte position right after all `import` statements in a source string.
    Used to insert `set_option` commands after imports during model compilation. -/
def findPosAfterImports (src : String) : String.Pos.Raw :=
  let lines := src.splitOn "\n"
  let (_, lastImportEnd) := lines.foldl (init := ((0 : Nat), (0 : Nat))) fun (pos, lastImportEnd) line =>
    let nextPos := pos + line.utf8ByteSize + 1  -- +1 for newline
    (nextPos, if line.trimLeft.startsWith "import " then nextPos else lastImportEnd)
  ⟨lastImportEnd⟩

/-- Find the byte position right after `#gen_spec` in the source.
    Used to filter out everything after `#gen_spec` from compiled model source. -/
def findGenSpecEnd (src : String) : String.Pos.Raw :=
  let parts := src.splitOn "#gen_spec"
  if parts.length == 1 then
    ⟨src.utf8ByteSize⟩  -- #gen_spec not found
  else
    ⟨parts.head!.utf8ByteSize + "#gen_spec".utf8ByteSize⟩

/-- Status of the model checker compilation process for a single model. -/
inductive Status
  | inProgress (instanceId : Nat) (buildDir : System.FilePath)
  | finished (buildDir : System.FilePath)
  deriving Inhabited

/-- Global state tracking compilation status for multiple models.
Keyed by the source file path (absolute path).
Uses `Std.Mutex` to prevent race conditions when multiple tasks access the registry. -/
initialize compilationRegistry : Std.Mutex (Std.HashMap String Status) ←
  Std.Mutex.new {}

@[inline]
def stillCurrentCont (sourceFile : String) (instanceId : Nat) (k : Std.AtomicT (Std.HashMap String Status) IO Unit) : IO Bool :=
  compilationRegistry.atomically fun ref => do
    let registry ← ref.get
    match registry[sourceFile]? with
    | some info =>
      match info with
      | .inProgress id _ => if id == instanceId then k ref ; pure true else pure false
      | _ => pure false
    | none => pure false

/-- Mark compilation as finished in the registry. -/
def markRegistryFinished (sourceFile : String) (buildFolder : System.FilePath) : IO Unit :=
  compilationRegistry.atomically fun ref =>
    ref.modify fun registry => registry.insert sourceFile (.finished buildFolder)

/-- Mark compilation as in progress in the registry. -/
def markRegistryInProgress (sourceFile : String) (instanceId : Nat) (buildFolder : System.FilePath) : IO Unit :=
  compilationRegistry.atomically fun ref =>
    ref.modify fun registry => registry.insert sourceFile (.inProgress instanceId buildFolder)

/-- Base directory for model checker build folders. This is an absolute path. -/
def getBuildBaseDir : IO System.FilePath := do
  let pwd ← IO.currentDir
  return pwd / ".lake" / "model_checker_builds"

/-- Generate a build folder name based on the source file name, so that for the
same source file we get the same build folder. -/
def generateBuildFolderName (sourceFile : String) : IO System.FilePath := do
  -- Use the source file's stem (filename without extension) for readability
  let stem := System.FilePath.mk sourceFile |>.fileStem.getD "unrecognized_model"
  let baseDir ← getBuildBaseDir
  return baseDir / stem

/-- Template for the `lakefile.lean` in the temp project. Note that it does
not only require the parent Veil project, but also *all the dependencies*;
otherwise the temp project will clone and build all of them. -/
def lakefileTemplate : String :=
s!"import Lake
open Lake DSL System

require Veil from \"../../..\"
require Cli from \"../../../.lake/packages/Cli\"
require cvc5 from \"../../../.lake/packages/cvc5\"
require smt from \"../../../.lake/packages/smt\"
require Loom from \"../../../.lake/packages/Loom\"
require mathlib from \"../../../.lake/packages/mathlib\"
require auto from \"../../../.lake/packages/auto\"
require plausible from \"../../../.lake/packages/plausible\"
require LeanSearchClient from \"../../../.lake/packages/LeanSearchClient\"
require importGraph from \"../../../.lake/packages/importGraph\"
require proofwidgets from \"../../../.lake/packages/proofwidgets\"
require aesop from \"../../../.lake/packages/aesop\"
require Qq from \"../../../.lake/packages/Qq\"
require batteries from \"../../../.lake/packages/batteries\"

package veilmodel

lean_lib Model where
  globs := #[Glob.one `Model]

lean_exe ModelCheckerMain where
  root := `ModelCheckerMain
  buildType := .release
"

/-- Template for the ModelCheckerMain.lean in the temp project. -/
def modelCheckerMainTemplate : String :=
"import Model

set_option maxHeartbeats 6400000

def main (args : List String) : IO Unit := do
  -- Enable progress reporting to stderr for the IDE to read
  Veil.ModelChecker.Concrete.enableCompiledModeProgress
  let pcfg : Option Veil.ModelChecker.ParallelConfig :=
    match args with
    | [a, b] =>
      match a.toNat?, b.toNat? with
      | some n1, some n2 => some <| Veil.ModelChecker.ParallelConfig.mk n1 n2
      | _, _ => none
    | _ => none
  -- Instance ID is not used in compiled mode, pass 0
  -- Cancel token is created locally; cancellation is handled by killing the process from outside
  let cancelTk ← IO.CancelToken.new
  let res ← modelCheckerResult pcfg 0 cancelTk
  IO.println s!\"{Lean.toJson res}\"
"

/-- Create the temp build folder with all necessary files.
Returns the absolute path to the build folder. -/
def createBuildFolder (sourceFile : String) (modelSource : String) : IO System.FilePath := do
  let veilPath ← IO.currentDir
  let buildFolder ← generateBuildFolderName sourceFile
  -- Create the build folder
  IO.FS.createDirAll buildFolder
  -- Write the lakefile
  IO.FS.writeFile (buildFolder / "lakefile.lean") lakefileTemplate
  -- Write the model source (renamed to Model.lean)
  IO.FS.writeFile (buildFolder / "Model.lean") modelSource
  -- Write the ModelCheckerMain.lean
  IO.FS.writeFile (buildFolder / "ModelCheckerMain.lean") modelCheckerMainTemplate
  -- Create a minimal lean-toolchain file (copy from parent)
  let toolchainPath := veilPath / "lean-toolchain"
  if ← toolchainPath.pathExists then
    let toolchain ← IO.FS.readFile toolchainPath
    IO.FS.writeFile (buildFolder / "lean-toolchain") toolchain
  return buildFolder

/-- Update elapsed time status for a progress instance. -/
def updateElapsedTimeStatus (instanceId : Nat) (statusPrefix : String) : IO Unit := do
  if let some refs ← ModelChecker.Concrete.getProgressRefs instanceId then
    let elapsed := ModelChecker.formatElapsedTime (← refs.progressRef.get).elapsedMs
    ModelChecker.Concrete.updateStatus instanceId s!"{statusPrefix} ({elapsed})"

/-- Result of running a compilation process. -/
structure ProcessResult where
  exitCode : UInt32
  stdout : String
  stderr : String
  interrupted : Bool := false
  deriving Inhabited

/-- Run a process with status updates, checking if compilation is still current or cancelled.
    Returns the exit code, stdout, stderr, and whether it was interrupted. -/
def runProcessWithStatus (sourceFile : String) (cfg : IO.Process.SpawnArgs)
    (instanceId : Nat) (statusPrefix : String) (cancelToken : IO.CancelToken) : IO ProcessResult := do
  let proc ← IO.Process.spawn { cfg with stdin := .piped, stdout := .piped, stderr := .piped }
  -- Start reading stdout/stderr in background tasks to avoid blocking
  let stdoutTask ← IO.asTask (prio := .dedicated) proc.stdout.readToEnd
  let stderrTask ← IO.asTask (prio := .dedicated) proc.stderr.readToEnd
  let waitTask ← IO.asTask (prio := .dedicated) proc.wait
  let mut interrupted := false
  while !(← IO.hasFinished waitTask) do
    -- Check for explicit cancellation request
    if ← cancelToken.isSet then
      proc.kill
      interrupted := true
      break
    -- Check if this compilation is still current (not superseded)
    let current? ← stillCurrentCont sourceFile instanceId do
      updateElapsedTimeStatus instanceId statusPrefix
    unless current? do
      proc.kill
      interrupted := true
      break
    IO.sleep 100
  let stdout ← IO.ofExcept (← IO.wait stdoutTask)
  let stderr ← IO.ofExcept (← IO.wait stderrTask)
  match ← IO.wait waitTask with
  | .ok exitCode => return { exitCode, stdout, stderr, interrupted }
  | .error err => return { exitCode := 1, stdout, stderr := s!"{stderr}\nIO error: {err}", interrupted }

/-- Run a process with a callback for status updates.
    The callback is called periodically while the process runs.
    This variant does not check for cancellation - it runs to completion. -/
def runProcessWithStatusCallback (cfg : IO.Process.SpawnArgs)
    (updateStatus : IO Unit) : IO ProcessResult := do
  let proc ← IO.Process.spawn { cfg with stdin := .piped, stdout := .piped, stderr := .piped }
  -- Start reading stdout/stderr in background tasks to avoid blocking
  let stdoutTask ← IO.asTask (prio := .dedicated) proc.stdout.readToEnd
  let stderrTask ← IO.asTask (prio := .dedicated) proc.stderr.readToEnd
  let waitTask ← IO.asTask (prio := .dedicated) proc.wait
  while !(← IO.hasFinished waitTask) do
    updateStatus
    IO.sleep 500  -- Update every 500ms
  let stdout ← IO.ofExcept (← IO.wait stdoutTask)
  let stderr ← IO.ofExcept (← IO.wait stderrTask)
  match ← IO.wait waitTask with
  | .ok exitCode => return { exitCode, stdout, stderr, interrupted := false }
  | .error err => return { exitCode := 1, stdout, stderr := s!"{stderr}\nIO error: {err}", interrupted := false }

-- /-- Clean up all build folders older than the specified age (in milliseconds). -/
-- def cleanupOldBuildFolders (maxAgeMs : Nat := 24 * 60 * 60 * 1000) : IO Nat := do
--   let now ← IO.monoMsNow
--   let mut count := 0
--   if !(← getBuildBaseDir.pathExists) then return 0

--   for entry in ← getBuildBaseDir.readDir do
--     -- Check if it's a directory
--     let isDir ← entry.path.isDir
--     if isDir then
--       -- Try to parse the timestamp from the folder name (format: stem_timestamp_random)
--       let parts := entry.fileName.splitOn "_"
--       if parts.length >= 2 then
--         let timestampStr := parts[parts.length - 2]!
--         if let some timestamp := timestampStr.toNat? then
--           if now - timestamp > maxAgeMs then
--             IO.FS.removeDirAll entry.path
--             count := count + 1
--   return count

end Veil.ModelChecker.Compilation
