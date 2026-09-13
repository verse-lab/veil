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
  /-- Name of the generated definition that the compiled executable calls. -/
  exportedName : String

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

/-- The `lake` executable that builds model checker binaries. Lake exports its own path as
`LAKE` to the processes it starts, including the language server, so this is the `lake` that
launched the current process; without it, fall back to the one in the running toolchain. -/
def getLakeExecutable : IO System.FilePath := do
  if let some lake ← IO.getEnv "LAKE" then
    unless lake.isEmpty do return lake
  return (← Lean.findSysroot) / "bin" / System.FilePath.addExtension "lake" System.FilePath.exeExtension

/-- Each invocation owns its files, including concurrent checks in the same source. -/
def generateBuildFolderName (sourceFile : String) (command : CompiledCommandSpec) (instanceId : Nat) : IO System.FilePath := do
  let stem := System.FilePath.mk sourceFile |>.fileStem.getD "unrecognized_model"
  let baseDir ← getBuildBaseDir
  return baseDir / s!"{stem}_{command.exportedName}_{hash sourceFile}_{← IO.Process.getPID}_{instanceId}"

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

/-- Write the current environment's C output and its native dependency names. -/
def createBuildFolder (sourceFile : String) (command : CompiledCommandSpec) (instanceId : Nat)
    (cCode : String) (imports : Array Name) : IO System.FilePath := do
  let buildFolder ← generateBuildFolderName sourceFile command instanceId
  IO.FS.createDirAll buildFolder
  -- Write the C IR
  IO.FS.writeFile (buildFolder / "ModelCheckerMain.c") cCode
  IO.FS.writeFile (buildFolder / "imports.json") (toJson imports).compress
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

end Veil.ModelChecker.Compilation
