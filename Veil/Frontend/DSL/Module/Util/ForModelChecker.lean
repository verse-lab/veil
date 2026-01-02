import Veil.Core.UI.Widget.ProgressViewer

namespace Veil.ModelChecker.Compilation

open Lean Meta Elab Command

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
private def stillCurrentCont (sourceFile : String) (instanceId : Nat) (k : Std.AtomicT (Std.HashMap String Status) IO Unit) : IO Bool :=
  compilationRegistry.atomically fun ref => do
    let registry ← ref.get
    match registry[sourceFile]? with
    | some info =>
      match info with
      | .inProgress id _ => if id == instanceId then k ref ; pure true else pure false
      | _ => pure false
    | none => pure false

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
"import Veil

set_option maxHeartbeats 6400000

-- The following code is inspired by
-- `https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Trouble.20parsing.20Lean.20code.20from.20string/`

open Lean Meta Elab Term in
/-- Parse and evaluate a model checker call expression. -/
unsafe def parseAndEvalModelCheckerCall (code : String) : IO Json := do
  -- Run elaboration and evaluation
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let imports := #[`Lean, `Model]
  let env ← importModules (imports.map (Import.mk · false true false)) Options.empty
    (leakEnv := true)
    (loadExts := true)
  let (ioResult, _) ← Core.CoreM.toIO (ctx := { fileName := \"<CoreM>\", fileMap := default }) (s := { env := env }) do
    let .ok stx := Parser.runParserCategory (← getEnv) `term code \"<stdin>\"
      | return none
    MetaM.run' do
      TermElabM.run' do
        let stx ← `($(mkIdent ``Functor.map) $(mkIdent ``Lean.toJson) ($(TSyntax.mk stx)))
        let ty := mkApp (mkConst ``IO) (mkConst ``Json)
        let tm ← elabTerm stx ty
        synthesizeSyntheticMVarsNoPostponing
        let tm ← instantiateMVars tm
        let res ← evalExpr (IO Json) ty tm
        return some res

  let some ioResult := ioResult | throw (IO.userError s!\"Failed to parse input\")
  ioResult

def main : IO Unit := do
  Veil.ModelChecker.Concrete.enableCompiledModeProgress
  let stdin ← IO.getStdin
  let code ← stdin.readToEnd
  let result ← unsafe parseAndEvalModelCheckerCall code
  IO.println s!\"{result}\"
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

/-- Run a process with status updates, checking if compilation is still current. -/
def runProcessWithStatus (sourceFile : String) (cfg : IO.Process.SpawnArgs)
    (instanceId : Nat) (statusPrefix : String) : IO Unit := do
  let proc ← IO.Process.spawn { cfg with stdin := .piped, stdout := .piped, stderr := .piped }
  let waitTask ← IO.asTask (prio := .dedicated) proc.wait
  while !(← IO.hasFinished waitTask) do
    let current? ← stillCurrentCont sourceFile instanceId do
      updateElapsedTimeStatus instanceId statusPrefix
    unless current? do
      proc.kill
      break
    IO.sleep 100
  match ← IO.wait waitTask with
  | .ok _ => return
  | .error err =>
    dbg_trace s!"Model compilation process failed: {err}"
    return

/-- Start async compilation for a model in its isolated build folder.
Does not display progress; that is handled by `#model_check` if needed. -/
def startModelCompilation (sourceFile : String) (modelSource : String) : CommandElabM System.FilePath := do
  let instanceId ← ModelChecker.Concrete.allocProgressInstance
  -- Create the build folder
  let buildFolder ← createBuildFolder sourceFile modelSource
  -- Update status to inProgress
  compilationRegistry.atomically fun ref => do
    ref.modify fun registry => registry.insert sourceFile (.inProgress instanceId buildFolder)
  -- Start compilation in a background task
  let _ ← IO.asTask (prio := .dedicated) do
    -- Run lake build in the temp folder
    runProcessWithStatus sourceFile
      { cmd := "lake", args := #["build", "ModelCheckerMain"], cwd := buildFolder }
      instanceId "Compiling"
    -- Mark as idle if still current
    let _ ← stillCurrentCont sourceFile instanceId fun ref => do
      ref.modify fun registry => registry.insert sourceFile (.finished buildFolder)
      ModelChecker.Concrete.finishProgress instanceId (Json.mkObj [("status", "compiled")])

  return buildFolder

/-- Poll for compilation result, updating progress while waiting. -/
def pollForCompilationResult (sourceFile : String) (compilationInstanceId runningInstanceId : Nat) : IO (Option System.FilePath) := do
  while true do
    let (canBreak?, res) ← compilationRegistry.atomically fun ref => do
      let registry ← ref.get
      match registry[sourceFile]? with
      | some info =>
        match info with
        | .finished buildDir => pure (true, some buildDir)
        | .inProgress id' _ =>
          if id' == compilationInstanceId
          then
            updateElapsedTimeStatus compilationInstanceId "Compiling"
            -- Mirror the compilation progress to our instance
            if let some compilationRefs ← ModelChecker.Concrete.getProgressRefs compilationInstanceId then
              let compilationProgress ← compilationRefs.progressRef.get
              if let some refs ← ModelChecker.Concrete.getProgressRefs runningInstanceId then
                refs.progressRef.set compilationProgress
          pure (false, none)
      | none => pure (true, none)            -- This should not happen, but if it happens then
    if canBreak? then return res
    IO.sleep 100
  return none

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
