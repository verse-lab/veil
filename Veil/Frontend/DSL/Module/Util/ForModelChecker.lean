import Veil.Core.UI.Widget.ProgressViewer
import Veil.Util.Meta
import Batteries.Data.String.Matcher

namespace Veil.ModelChecker.Compilation

/-!

NOTE: Currently there are two approaches for running the model checker call after
compilation, both in this file.
- Old approach: copy the file under editing into the temporary Lake project
directory with name `Model.lean`, set the `veil.__modelCheckCompileMode` option
at the beginning of `Model.lean`, and compile the copy together with a temporarily
generated main entry file `ModelCheckerMain.lean`
- New approach: first bring the `modelCheckerResult` and `main` definitions into
the current environment, then use `Lean.IR.emitC` to output the C IR, still to a
temporary directory, and finally compile the C IR into an object file, and link
this object file with the other dependent object files

For now, the compilation and linking command in the new approach is obtained from
the verbose output of the old approach, so at this stage the new approach is based
on the old one. To get rid of this dependency, some more thorough hack into `lake`
is required.

That said, there are some things to take care of, regardless of whether the old
approach will be kept:
- More definitions should be removed from the environment before compiling into C,
including the `act.do`, `act` and `act.ext` definitions
- The main entry function might be made into an object-level definition instead
of a meta-level one (i.e., syntax)
- There seems to be some time gap in starting running the model checker and
displaying the result; what's happening there?
- The workflow of `compiled` mode and handoff mode should reuse more code

-/

open Lean Meta Elab Command

/-- Find the byte position right after all `import` statements in a source string.
    Used to insert `set_option` commands after imports during model compilation. -/
def findPosAfterImports (src : String) : String.Pos.Raw :=
  let lines := src.splitOn "\n"
  let (_, lastImportEnd) := lines.foldl (init := ((0 : Nat), (0 : Nat))) fun (pos, lastImportEnd) line =>
    let nextPos := pos + line.utf8ByteSize + 1  -- +1 for newline
    (nextPos, if line.trimLeft.startsWith "import " then nextPos else lastImportEnd)
  ⟨lastImportEnd⟩

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

lean_exe ModelCheckerMain where
  root := `ModelCheckerMain
  buildType := .release
"

namespace ToBeInsertedIntoMain

private def flushStdoutAndStderr : IO Unit := do
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  stdout.flush
  stderr.flush

private def exitWhenParentDies : IO Unit := do
  let stdin ← IO.getStdin
  let _ ← stdin.readToEnd
  flushStdoutAndStderr
  IO.Process.forceExit 2

-- NOTE: This uses `addVeilDefinition` to avoid prepending the name `main`
-- with the current scope name
def addMain (specNamespace : Name) : TermElabM Unit := do
  let mainType := mkApp (mkConst ``IO) (mkConst ``Unit)
  let mainBody ← Term.elabTerm (← `(term|do
    let _ ← IO.asTask (prio := .dedicated) $(mkIdent ``ToBeInsertedIntoMain.exitWhenParentDies):term
    -- Enable progress reporting to stderr for the IDE to read
    Veil.ModelChecker.Concrete.enableCompiledModeProgress
    let pcfg : Option Veil.ModelChecker.ParallelConfig := $(mkIdent ``Option.none)
    -- Instance ID is not used in compiled mode, pass 0
    -- Cancel token is created locally; cancellation is handled by killing the process from outside
    let cancelTk ← IO.CancelToken.new
    -- `modelCheckerResult` is to be defined in the model
    -- NOTE: For now, just sequential
    let res ← $(mkIdent <| specNamespace ++ `modelCheckerResult):term pcfg 0 cancelTk
    IO.println s!"{Lean.toJson res}"
    $(mkIdent ``ToBeInsertedIntoMain.flushStdoutAndStderr):term
    IO.Process.forceExit 0
  )) mainType
  Term.synthesizeSyntheticMVarsNoPostponing
  let mainBody ← instantiateMVars mainBody
  let _ ← addVeilDefinition `main mainBody (type := mainType) (addNamespace := false)

end ToBeInsertedIntoMain

/-- Create the temp build folder with all necessary files.
Returns the absolute path to the build folder. -/
def createBuildFolder (sourceFile : String) (modelSource : String)
  (buildFolderOpt : Option System.FilePath := .none) : IO System.FilePath := do
  let veilPath ← IO.currentDir
  let buildFolder ← match buildFolderOpt with
    | some p => pure p
    | none => generateBuildFolderName sourceFile
  -- Create the build folder
  IO.FS.createDirAll buildFolder
  -- Write the lakefile
  IO.FS.writeFile (buildFolder / "lakefile.lean") lakefileTemplate
  -- Write the model source (renamed to Model.lean)
  IO.FS.writeFile (buildFolder / "ModelCheckerMain.lean") modelSource
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

/-- Run a process with callbacks for status updates and line-by-line output capture.
    - `statusCallback` is called periodically (every 500ms) with the elapsed time in ms.
    - `lineCallback` is called for each line of output (content, isError, elapsedMs).
    This variant does not check for cancellation - it runs to completion. -/
def runProcessWithStatusCallback (cfg : IO.Process.SpawnArgs)
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
      lineCallback line.trimRight isError ((← IO.monoMsNow) - startTime)
  let stdoutTask ← IO.asTask (prio := .dedicated) (readLines proc.stdout stdoutAccum false)
  let stderrTask ← IO.asTask (prio := .dedicated) (readLines proc.stderr stderrAccum true)
  let waitTask ← IO.asTask (prio := .dedicated) proc.wait
  while !(← IO.hasFinished waitTask) do
    statusCallback ((← IO.monoMsNow) - startTime)
    IO.sleep 500
  let _ ← IO.wait stdoutTask
  let _ ← IO.wait stderrTask
  match ← IO.wait waitTask with
  | .ok exitCode => return { exitCode, stdout := ← stdoutAccum.get, stderr := ← stderrAccum.get, interrupted := false }
  | .error err => return { exitCode := 1, stdout := ← stdoutAccum.get, stderr := s!"{← stderrAccum.get}\nIO error: {err}", interrupted := false }

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

/-- Path to the compile script in the build folder. -/
def getCompileScriptPath (buildFolder : System.FilePath) : System.FilePath :=
  buildFolder / "compile_and_link.sh"

/-- Check if the compile script exists. -/
def compileScriptExists (buildFolder : System.FilePath) : IO Bool :=
  (getCompileScriptPath buildFolder).pathExists

/-- Extract compile and link commands from `lake --verbose` output.
    Returns `(compileCommand, linkCommand)` if both are found.
    Looks for commands related to `Model` or `ModelCheckerMain` compilation.

    The verbose output from `lake build --verbose` has lines like:
    - `trace: .> ... -c -o .../ModelCheckerMain.c.o.export .../ModelCheckerMain.c ...`  (C compile)
    - `trace: .> ... -o .../bin/ModelCheckerMain .../ModelCheckerMain.c.o.export ...`  (link)

    The C compile command has `-c` flag and the output `.c.o` file.
    The link command has `-o` followed by the binary output path `/bin/ModelCheckerMain`. -/
def extractCompileLinkCommands (verboseOutput : String) : Option (String × String) := Id.run do
  let lines := verboseOutput.splitOn "\n"
  let mut compileCmd : Option String := none
  let mut linkCmd : Option String := none
  for line in lines do
    let trimmed := line.trim
    if trimmed.isEmpty then continue
    -- Look for C compile command: compiling `.c` to `.o` using `clang`
    -- Contains `-c` and `ModelCheckerMain.c.o*` (the output object file)
    if hasSubstr trimmed "-c" && hasSubstr trimmed "ModelCheckerMain.c.o" && compileCmd.isNone then
      compileCmd := some (stripTracePrefix trimmed)
    -- Look for link command: linking `.o` files to create executable
    -- Contains `-o` followed by the binary path `.../bin/ModelCheckerMain`
    else if hasSubstr trimmed "/bin/ModelCheckerMain " && linkCmd.isNone then
      linkCmd := some (stripTracePrefix trimmed)
    else pure ()
  match compileCmd, linkCmd with
  | some c, some l => some (c, l)
  | _, _ => none
where
 hasSubstr (s : String) (pattern : String) : Bool :=
  s.containsSubstr pattern.toSubstring
 stripTracePrefix (line : String) : String :=
  let tracePrefix := "trace: .> "
  if line.startsWith tracePrefix then
    line.drop tracePrefix.length
  else
    line

-- CHECK `saveCompileScript` might be called from `IO.Process.spawn`?
-- CHECK `createBuildFolderForCCode` might be merged with `createBuildFolder`?

/-- Save compile and link commands to a script file. -/
def saveCompileScript (buildFolder : System.FilePath) (compileCmd linkCmd : String) : IO Unit := do
  let scriptPath := getCompileScriptPath buildFolder
  let scriptContent := s!"#!/bin/bash
set -e

# Working directory: {buildFolder}
cd \"{buildFolder}\"

# Compile C to object file
{compileCmd}

# Link to create executable
{linkCmd}
"
  IO.FS.writeFile scriptPath scriptContent

/-- Run the compile script. Returns `(success, stdout, stderr)`. -/
def runCompileScript (buildFolder : System.FilePath) : IO (Bool × String × String) := do
  let scriptPath := getCompileScriptPath buildFolder
  let result ← IO.Process.output { cmd := "/bin/bash", args := #[scriptPath.toString], cwd := buildFolder }
  return (result.exitCode == 0, result.stdout, result.stderr)

/-- The IR directory for the new approach (different from Lake's default to avoid clashing). -/
def getNewApproachIrDir (buildFolder : System.FilePath) : System.FilePath :=
  buildFolder / ".lake" / "model_check_build" / "ir"

/-- Write C code for the new approach. Unlike `createBuildFolder`, this skips
some steps, as by calling this function, we assume the temporary Lake project is
already set up. The C file is written to `.lake/model_check_build/ir/` to avoid
clashing with Lake's default `.lake/build/ir/` directory. -/
def writeCCode (cCode : String) (buildFolder : System.FilePath) : IO Unit := do
  -- Create the build folder and the IR subdirectory
  let irDir := getNewApproachIrDir buildFolder
  IO.FS.createDirAll irDir
  -- Write the C code file to the IR directory
  IO.FS.writeFile (irDir / "ModelCheckerMain.c") cCode

/-- Adapt a compile command for the new approach.
    Changes `.lake/build/ir/ModelCheckerMain.c` to `.lake/model_check_build/ir/ModelCheckerMain.c`
    for both source and target paths. -/
def adaptCompileCommand (cmd : String) : String :=
  -- Replace the old IR path with the new one for ModelCheckerMain files
  cmd.replace ".lake/build/ir/ModelCheckerMain" ".lake/model_check_build/ir/ModelCheckerMain"

/-- Adapt a link command for the new approach.
    Changes `.lake/build/ir/ModelCheckerMain.c.o.export` to `.lake/model_check_build/ir/ModelCheckerMain.c.o.export`. -/
def adaptLinkCommand (cmd : String) : String :=
  -- First, replace the ModelCheckerMain path
  let cmd := cmd.replace ".lake/build/ir/ModelCheckerMain" ".lake/model_check_build/ir/ModelCheckerMain"
  -- Escape `'`
  let cmd := cmd.replace "\'" "\\\'"
  cmd

/-- Save adapted compile and link commands to a script file for the new approach. -/
def saveAdaptedCompileScript (buildFolder : System.FilePath) (compileCmd linkCmd : String) : IO Unit := do
  let adaptedCompile := adaptCompileCommand compileCmd
  let adaptedLink := adaptLinkCommand linkCmd
  saveCompileScript buildFolder adaptedCompile adaptedLink

end Veil.ModelChecker.Compilation
