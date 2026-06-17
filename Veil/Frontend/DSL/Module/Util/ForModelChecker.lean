import Veil.Core.UI.Widget.ProgressViewer

namespace Veil.ModelChecker.Compilation

open Lean Meta Elab Command

/-- Find the byte position right after all `import` statements in a source string.
    Used to insert `set_option` commands after imports during model compilation. -/
def findPosAfterImports (src : String) : String.Pos.Raw :=
  let lines := src.splitOn "\n"
  let (_, lastImportEnd) := lines.foldl (init := ((0 : Nat), (0 : Nat))) fun (pos, lastImportEnd) line =>
    let nextPos := pos + line.utf8ByteSize + 1  -- +1 for newline
    (nextPos, if line.trimAsciiStart.startsWith "import " then nextPos else lastImportEnd)
  ⟨lastImportEnd⟩

/-- Status of the model checker compilation process for a single model. -/
inductive Status
  | inProgress (instanceId : Nat) (buildDir : System.FilePath)
  | finished (buildDir : System.FilePath)
  deriving Inhabited

/-- Description of a command that can be compiled into a generated executable. -/
structure CompiledCommandSpec where
  /-- Name of the generated definition that the compiled executable calls. -/
  exportedName : String
  /-- Whether the generated definition accepts an optional parallel configuration. -/
  supportsParallelConfig : Bool := false

/-- Registry key for one compiled command invocation. -/
structure CompilationKey where
  /-- Source file containing the compiled command invocation. -/
  sourceFile : String
  /-- Generated definition called by the compiled executable. -/
  exportedName : String
  /-- Identity of the specific command invocation within `sourceFile`. -/
  commandId : String
  deriving BEq, Hashable, Inhabited

/-- Global state tracking compilation status for multiple compiled commands.
    Keyed by source file path, exported command name, and command identity so
    different command invocations in the same file do not supersede each other.
    Uses `Std.Mutex` to prevent race conditions when multiple tasks access the registry. -/
initialize compilationRegistry : Std.Mutex (Std.HashMap CompilationKey Status) ←
  Std.Mutex.new {}

@[inline]
def mkCompilationKey (sourceFile : String) (command : CompiledCommandSpec) (commandId : String) : CompilationKey := {
  sourceFile,
  exportedName := command.exportedName,
  commandId,
}

@[inline]
def stillCurrentCont (sourceFile : String) (command : CompiledCommandSpec) (commandId : String) (instanceId : Nat)
    (k : Std.AtomicT (Std.HashMap CompilationKey Status) IO Unit) : IO Bool :=
  compilationRegistry.atomically fun ref => do
    let registry ← ref.get
    match registry[mkCompilationKey sourceFile command commandId]? with
    | some info =>
      match info with
      | .inProgress id _ => if id == instanceId then k ref ; pure true else pure false
      | _ => pure false
    | none => pure false

/-- Mark compilation as finished in the registry. -/
def markRegistryFinished (sourceFile : String) (command : CompiledCommandSpec) (commandId : String)
    (buildFolder : System.FilePath) : IO Unit :=
  compilationRegistry.atomically fun ref =>
    ref.modify fun registry =>
      registry.insert (mkCompilationKey sourceFile command commandId) (.finished buildFolder)

/-- Mark compilation as in progress in the registry. -/
def markRegistryInProgress (sourceFile : String) (command : CompiledCommandSpec) (commandId : String)
    (instanceId : Nat) (buildFolder : System.FilePath) : IO Unit :=
  compilationRegistry.atomically fun ref =>
    ref.modify fun registry =>
      registry.insert (mkCompilationKey sourceFile command commandId) (.inProgress instanceId buildFolder)

/-- Base directory for model checker build folders. This is an absolute path. -/
def getBuildBaseDir : IO System.FilePath := do
  let pwd ← IO.currentDir
  return pwd / ".lake" / "model_checker_builds"

/-- Generate a build folder name based on the source file and exported command. -/
def generateBuildFolderName (sourceFile : String) (command : CompiledCommandSpec) (_commandId : String) : IO System.FilePath := do
  let stem := System.FilePath.mk sourceFile |>.fileStem.getD "unrecognized_model"
  let suffix := toString (hash (sourceFile ++ ":" ++ command.exportedName))
  let baseDir ← getBuildBaseDir
  return baseDir / s!"{stem}_{command.exportedName}_{suffix}"

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
  buildType := .relWithDebInfo
"

/-- Template for the ModelCheckerMain.lean in the temp project.
    Takes the namespace of the specification to open scoped instances. -/
def modelCheckerMainTemplate (specNamespace : String) (command : CompiledCommandSpec) : String :=
"import Model

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 10000

open " ++ specNamespace ++ "

def flushStdoutAndStderr : IO Unit := do
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  stdout.flush
  stderr.flush

def exitWhenParentDies : IO Unit := do
  let stdin ← IO.getStdin
  let _ ← stdin.readToEnd
  flushStdoutAndStderr
  IO.Process.forceExit 2

def main (args : List String) : IO Unit := do
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
  let res ← " ++
    (if command.supportsParallelConfig
      then command.exportedName ++ " pcfg 0 cancelTk"
      else command.exportedName ++ " 0 cancelTk") ++ "
  IO.println s!\"{res}\"
  flushStdoutAndStderr
  IO.Process.forceExit 0
"

/-- Create the temp build folder with all necessary files.
Returns the absolute path to the build folder. Generated inputs are overwritten
on each call while preserving the Lake build cache in the folder. -/
def createBuildFolder (sourceFile : String) (modelSource : String) (specNamespace : String)
    (command : CompiledCommandSpec) (commandId : String) : IO System.FilePath := do
  let veilPath ← IO.currentDir
  let buildFolder ← generateBuildFolderName sourceFile command commandId
  IO.FS.createDirAll buildFolder
  -- Write the lakefile
  IO.FS.writeFile (buildFolder / "lakefile.lean") lakefileTemplate
  -- Write the model source (renamed to Model.lean)
  IO.FS.writeFile (buildFolder / "Model.lean") modelSource
  -- Write the ModelCheckerMain.lean
  IO.FS.writeFile (buildFolder / "ModelCheckerMain.lean") (modelCheckerMainTemplate specNamespace command)
  -- Create a minimal lean-toolchain file (copy from parent)
  let toolchainPath := veilPath / "lean-toolchain"
  if ← toolchainPath.pathExists then
    let toolchain ← IO.FS.readFile toolchainPath
    IO.FS.writeFile (buildFolder / "lean-toolchain") toolchain
  return buildFolder

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
    if ← cancelToken.isSet then
      proc.kill
      interrupted := true
      break
    let current? ← stillCurrentCont sourceFile command commandId instanceId do
      statusCallback ((← IO.monoMsNow) - startTime)
    unless current? do
      proc.kill
      interrupted := true
      break
    IO.sleep 500
  let _ ← IO.wait stdoutTask
  let _ ← IO.wait stderrTask
  match ← IO.wait waitTask with
  | .ok exitCode => return { exitCode, stdout := ← stdoutAccum.get, stderr := ← stderrAccum.get, interrupted }
  | .error err => return { exitCode := 1, stdout := ← stdoutAccum.get, stderr := s!"{← stderrAccum.get}\nIO error: {err}", interrupted }

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
