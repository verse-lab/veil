module

public meta import Veil.Frontend.DSL.Module.Util.Basic
public meta import Veil.Frontend.DSL.Module.Syntax
public meta import Veil.Frontend.DSL.Module.Util.ForModelChecker
public meta import Veil.Frontend.DSL.Module.AssertionInfo
public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Util.Multiprocessing

public meta section

open Lean Elab Command Term

namespace Veil.ExecutionWorkflow

/-- Model checking mode: interpreted only, compiled only, or default (both with handoff). -/
inductive ModelCheckingMode where
  | interpreted
  | compiled
  | default
  deriving Repr, DecidableEq

/-- Context for model checking operations. Bundles common parameters to reduce duplication. -/
private structure ExecutionContext where
  stx : Syntax
  instanceId : Nat
  /-- Stop signal for the run this context owns. Currently, three parties can set it:

  * the Stop button, through `requestCancellation`, which also sets the background
    compilation token registered on the progress instance;
  * the handoff in default mode, which sets it to wind the interpreted run down
    before the compiled binary takes over, having first set `handoffRequested`;
  * the editor, which owns it as the `cancelTk?` of the interpreted task's
    snapshot and sets it when the command is elaborated again. -/
  cancelToken : IO.CancelToken
  assertionSources : Std.HashMap AssertionId AssertionSourceInfo
  parallelCfg : Option ModelChecker.ParallelConfig
  /-- Which command owns this context; selects the infoview renderer. -/
  resultKind : TraceDisplay.ResultKind
  /-- Where the actions and the properties of the module are, which the result gives the infoview,
  if known -/
  sources : Json := .null

/-- Report compilation failures without stopping an interpreted run during handoff.
Interruptions produce no diagnostic: a killed build returns `none`, and an interrupt raised
while generating C propagates, since `catch` rethrows interrupts. -/
private def withCompilationDiagnostics (stx : Syntax) (instanceId : Nat) (handoff : Bool)
    (compile : CommandElabM (Option System.FilePath)) : CommandElabM (Option System.FilePath) := do
  try
    compile
  catch e : Exception =>
    -- `elabTermForExecution` uses `throwAbortTerm` once an error has been logged.
    -- Mark the build as failed, but keep the original diagnostic instead of reporting the abort.
    let aborted := isAbortException e
    let message ← if aborted then pure "Execution configuration elaboration failed." else e.toMessageData.toString
    let ref := if e.getRef.getPos?.isSome then e.getRef else stx
    ModelChecker.Concrete.updateCompilationStatus instanceId (.failed message)
    if handoff then
      unless aborted do logWarningAt ref message
    else
      ModelChecker.Concrete.finishProgress instanceId (Json.mkObj [("error", toJson message)])
      unless aborted do logErrorAt ref message
    return none

/-- Extract the model checking mode from the optional mode syntax. -/
def getModelCheckingMode (modeStx : Syntax) : ModelCheckingMode :=
  if modeStx.isNone then .default
  else match modeStx[0] with
    | `(modelCheckMode| interpreted) => .interpreted
    | `(modelCheckMode| compiled) => .compiled
    | _ => .default

/-- The names of the module's actions, for never-enabled action warnings: the constructors of its
labels, as the labels' `Display` names them (`ValueDisplay.ctorJson`). -/
def actionLabelNames (mod : Module) : List String :=
  mod.actions.toList.map fun a => match a.name.eraseMacroScopes with
    | .str _ s => s
    | n => toString n

/-- Where the actions and the properties of `mod` are in this file, by the names that model checking
results give them. -/
def getDeclSources (mod : Module) : CommandElabM (Array DeclSource × Array DeclSource) := do
  let actions ← mod.procedures.filterMapM fun p => match p.info with
    -- Traces name the initial step `after_init`
    | .initializer => source "after_init" p.userSyntax
    | .action name _ => source name.toString p.userSyntax
    | .procedure _ => pure none
  let assertions ← mod.assertions.filterMapM fun a => source a.name.toString a.userSyntax
  return (actions, assertions)
where
  source (name : String) (stx : Syntax) : CommandElabM (Option DeclSource) := do
    let some pos := stx.getPos? | return none
    let position := (← getFileMap).utf8PosToLspPos pos
    return some { name, file := ← getFileName, line := position.line, character := position.character }

/-- The sources of the actions and the properties of a module, as the trace display of the infoview
links to them (see `widget/src/traceDisplayInfoview.tsx`): with the URIs of their files, a relative
file being in `workspace`. -/
def infoviewSources (actions properties : Array DeclSource) (workspace : System.FilePath) : Json :=
  let entry (source : DeclSource) :=
    let file : System.FilePath := source.file
    json% { name: $(source.name), uri: $(System.Uri.pathToUri (if file.isAbsolute then file else workspace / file)),
            line: $(source.line), character: $(source.character) }
  json% { actions: $(actions.map entry), properties: $(properties.map entry) }

/-- Stable identity for a single compiled command invocation within a file. -/
private def getCompiledCommandId (cmdName : String) (stx : Syntax) : CommandElabM String := do
  let some startPos := stx.getPos? | throwError s!"Unexpected error: {cmdName} has no position"
  let some endPos := stx.getTailPos? | throwError s!"Unexpected error: {cmdName} has no end position"
  pure s!"{startPos.1}-{endPos.1}"

/-- Elaborate the complete computation for this workflow's compiled or interpreted entry point.
Both callers pass expressions directly to the compiler/evaluator rather than elaborating a Lean
definition or `#eval`. Run normal elaboration and synthesis, abort on logged errors, and reject
remaining metavariables before that handoff. On failure, supplement the original error with a
user-hole diagnostic when possible, without replacing it. -/
private def elabTermForExecution (term : Term) : TermElabM Expr := do
  try
    let expr ← Term.elabTerm term none
    if ← MonadLog.hasErrors then throwAbortTerm
    Term.synthesizeSyntheticMVarsNoPostponing
    if ← MonadLog.hasErrors then throwAbortTerm
    let expr ← instantiateMVars expr
    if expr.hasMVar then
      if ← Term.logUnassignedUsingErrorInfos (← Meta.getMVars expr) then throwAbortTerm
      throwErrorAt term "The execution configuration contains unresolved metavariables. Fill in the remaining placeholders."
    return expr
  catch exception =>
    -- Preserve Lean's internal control-flow exceptions, including aborts.
    if exception matches .internal .. then throw exception
    -- An ordinary exception can stop elaboration before any diagnostic is logged. If so,
    -- add one hint at an unresolved user-written hole, not a generated placeholder.
    unless ← MonadLog.hasErrors do
      -- Error infos are prepended; reverse them to inspect holes in registration order.
      for info in (← get).mvarErrorInfos.reverse do
        if (info.kind matches .hole) && (info.ref.getHeadInfo matches .original ..) then
          -- Follow assignments too: a filled hole may still depend on unresolved metavariables.
          unless (← Meta.getMVars (mkMVar info.mvarId)).isEmpty do
            -- Print the goal in the hole's local context.
            info.mvarId.withContext <| info.logError none
            break
    -- A remaining hole does not prove it caused the failure; retain the original error as well.
    throw exception

/-- Compile a temporary entry point in the current snapshot, then emit its C module
with runtime initialization. -/
private def generateCCode (command : ModelChecker.Compilation.CompiledCommandSpec) (callExpr : Term) : CommandElabM String := withoutModifyingEnv do
  -- In a `module` file, a plain `def main` is private. A Veil namespace exports
  -- generated definitions, so also leave exporting mode when looking for it.
  let env := (← getEnv).setExporting false
  if env.contains `main || env.contains (mkPrivateNameCore env.mainModule `main) then
    throwError "Cannot compile #{command.name}: the file already declares `main`, \
      which the generated binary needs as its entry point. \
      Move the `main` declaration into another file, or use `#{command.name} interpreted`."
  unless (← getEnv).header.isModule do
    throwError "Compiled checks require Lean's module system. Start this file with `module`, and write \
      `public import Veil` (instead of `import Veil`)."
  liftCoreM ModelChecker.Compilation.compileRuntimeInitializers
  -- NOTE: Elaborate a term and add it with `addVeilDefinition` instead of elaborating a `def`
  -- command. `elabCommand` logs errors rather than
  -- throwing, and error recovery still adds `main` with a `sorry` body, so a failed
  -- elaboration would go on to build a binary that panics on `sorry` instead of stopping
  -- in `withCompilationDiagnostics`. It would also leave messages and info trees behind,
  -- which `withoutModifyingEnv` does not roll back.
  liftTermElabM <| Term.withoutErrToSorry <| withOptions (·.setBool `compiler.postponeCompile false) do
    let entry ← `(ModelChecker.Compilation.runMain $(quote command.actionLabels)
      (fun pcfg progressInstanceId cancelToken finish =>
        $callExpr pcfg progressInstanceId cancelToken (fun result => finish (Lean.toJson result))))
    let expr ← elabTermForExecution entry
    discard <| addVeilDefinition `main expr (addNamespace := false)
  liftCoreM <| ModelChecker.Compilation.emitCWithRuntimeInitializers `main

/-- Create an error JSON object. -/
private def errorJson (msg : String) : Json := Json.mkObj [("error", msg)]

/-- Whether a result JSON is the placeholder produced by a run that was stopped
before it finished, as opposed to a real verdict. -/
private def resultWasCancelled (json : Json) : Bool :=
  match json.getObjValAs? String "result" |>.toOption with
  | some "cancelled" => true
  | _ => false

/-- Check if cancelled (ignoring handoff-triggered cancellations). -/
private def checkCancelled (cancelToken : IO.CancelToken) (instanceId : Nat) : IO Bool := do
  if ← cancelToken.isSet then
    unless ← ModelChecker.Concrete.checkHandoffRequested instanceId do
      ModelChecker.Concrete.cancelProgress instanceId
      return true
  return false

/-- End a run that was cancelled before reaching a verdict, excluding handoff. -/
private def endRunIfCancelled (cancelToken : IO.CancelToken) (instanceId : Nat) : IO Unit := do
  if (← ModelChecker.Concrete.getProgress instanceId).isRunning then
    discard <| checkCancelled cancelToken instanceId

/-- Called only by the task that compiles and runs the binary, never its interpreted peer.
Stop using the build folder of a run that has ended, then prune build folders to
`veil.modelChecker.maxStoredBuilds`, or not at all when the limit is 0.
Pruning is best-effort cleanup and never fails the run or waits for another build. -/
private def releaseBuild (instanceId : Nat) : CommandElabM Unit := do
  let limit := veil.modelChecker.maxStoredBuilds.get (← getOptions)
  liftIO do
    ModelChecker.Compilation.releaseBuildFolder instanceId
    if limit = 0 then return
    try
      ModelChecker.Compilation.pruneBuildFolders (← ModelChecker.Compilation.getBuildBaseDir)
        limit
    catch _ => pure ()

/-- Build compilation error message from process result. -/
private def mkCompilationErrorMsg (result : ModelChecker.Compilation.ProcessResult) : String :=
  s!"Compilation failed (exit code {result.exitCode}):\n" ++
    (if result.stderr.isEmpty then "" else s!"[stderr]\n{result.stderr}") ++
    (if result.stdout.isEmpty then "" else s!"[stdout]\n{result.stdout}\n")

/-- Check if the compiled binary exists. Returns `some binPath` if found. -/
private def verifyBinaryExists (buildFolder : System.FilePath) (instanceId : Nat) : IO (Option System.FilePath) := do
  let binPath := ModelChecker.Compilation.buildFolderBinary buildFolder
  if ← binPath.pathExists then return some binPath
  ModelChecker.Concrete.finishProgress instanceId (errorJson s!"Binary not found at {binPath}")
  return none

/-- Run the compiled binary and return its JSON result if completed. -/
private def runBinaryForJson (binPath : System.FilePath) (args : Array String)
    (instanceId : Nat) (cancelToken : IO.CancelToken) : IO (Option Json) := do
  ModelChecker.Concrete.updateStatus instanceId "Running compiled binary..."
  let child ← IO.Process.spawn {
    cmd := binPath.toString, args,
    stdin := .piped, stdout := .piped, stderr := .piped }
  -- Read stderr for progress updates
  let stderrAccum ← IO.mkRef ""
  let stderrTask ← IO.asTask (prio := .dedicated) do
    while true do
      let line ← child.stderr.getLine
      if line.isEmpty then break
      match Json.parse line >>= FromJson.fromJson? (α := ModelChecker.Concrete.Progress) with
      | .ok p => if let some refs ← ModelChecker.Concrete.getProgressRefs instanceId then
          refs.progressRef.modify fun old =>
            -- Compilation status belongs to the parent; worker progress defaults to `.none`.
            -- Preserve it when replacing the progress reported by the worker.
            let p := { p with compilationStatus := old.compilationStatus }
            match p.details with
            -- Only the BFS checker reports a time series.
            | .modelCheck m =>
              let oldMetrics : ModelChecker.Concrete.ModelCheckProgress :=
                match old.details with
                | .modelCheck om => om
                | _ => default
              let historyPoint : ModelChecker.Concrete.ProgressHistoryPoint := {
                timestamp := p.elapsedMs
                diameter := m.diameter
                statesFound := m.statesFound
                distinctStates := m.distinctStates
                queue := m.queue
              }
              { p with details := .modelCheck { m with
                  allActionLabels := oldMetrics.allActionLabels
                  history := oldMetrics.history.push historyPoint } }
            | _ => p
      | .error _ =>
        -- The start report is for IDEs, and the progress instance has the labels already
        unless (Json.parse line).toOption.any (·.getObjVal? "start" |>.isOk) do
          stderrAccum.modify (· ++ line)
  let stdoutTask ← IO.asTask (prio := .dedicated) child.stdout.readToEnd
  let waitTask ← IO.asTask (prio := .dedicated) child.wait
  -- Monitor for cancellation
  while !(← IO.hasFinished waitTask) do
    if ← checkCancelled cancelToken instanceId then
      child.kill
      -- Wait for the process and both readers before ending cancellation: a late
      -- stderr progress update could otherwise overwrite the cancelled state.
      -- Cancellation takes precedence over errors returned by these tasks.
      discard <| IO.wait waitTask
      discard <| IO.wait stdoutTask
      discard <| IO.wait stderrTask
      return none
    IO.sleep 100
  let stdout ← IO.ofExcept (← IO.wait stdoutTask)
  let exitCode ← IO.ofExcept (← IO.wait waitTask)
  -- Process exit does not imply stderr has been drained. Join the reader before
  -- consuming diagnostics or publishing a final result; propagate reader failures.
  IO.ofExcept (← IO.wait stderrTask)
  let stderr ← stderrAccum.get
  if exitCode != 0 then
    throw <| IO.userError s!"Binary exited with code {exitCode}{if stderr.isEmpty then "" else s!"\n{stderr}"}"
  return some (Json.parse stdout |>.toOption.getD (errorJson s!"Failed to parse output: {stdout.take 500}"))

/-- Elaborate the interpreted mode computation. Must be called synchronously. -/
private def elaborateInterpretedComputation (instanceId : Nat) (callExpr : Term)
    (parallelCfg : Option ModelChecker.ParallelConfig) : CommandElabM (IO Lean.Json) := do
  let resultExpr ← `(do
    let some refs ← Veil.ModelChecker.Concrete.getProgressRefs $(quote instanceId) | pure Lean.Json.null
    Lean.toJson <$> $callExpr ($(quote parallelCfg)) ($(quote instanceId)) refs.cancelToken pure)
  trace[veil.desugar] "{resultExpr}"
  liftTermElabM <| Term.withoutErrToSorry do
    let expr ← elabTermForExecution resultExpr
    ModelChecker.Compilation.evalJsonComputation expr

/-- Log model checking result. -/
private def logModelCheckResult (kind : TraceDisplay.ResultKind) (stx : Syntax)
    (resultJson : Json) : CommandElabM Unit := do
  let msg := TraceDisplay.formatResult kind resultJson
  let isViolation := resultJson.getObjValD "result" == Json.str "found_violation" ||
                     resultJson.getObjValD "error" != .null
  let violationIsError := veil.violationIsError.get (← getOptions)
  if isViolation && violationIsError then logErrorAt stx msg else logInfoAt stx msg

/-- Allocate a model check context with progress tracking. -/
private def allocExecutionContext (mod : Module) (stx : Syntax)
    (parallelCfg : Option ModelChecker.ParallelConfig)
    (resultKind : TraceDisplay.ResultKind) : CommandElabM ExecutionContext := do
  let details : ModelChecker.Concrete.ProgressDetails ← do
    match resultKind with
    | .simulate => pure <| .simulation {}
    | _ =>
      let actionLabels := actionLabelNames mod
      pure <|.modelCheck { allActionLabels := actionLabels }
  let (instanceId, cancelToken) ← ModelChecker.Concrete.allocProgressInstance details
  let assertionSources := extractAssertionSources (← globalEnv.get).assertions (← getFileMap)
  let (actions, properties) ← getDeclSources mod
  let sources := infoviewSources actions properties (← IO.currentDir)
  return { stx, instanceId, cancelToken, assertionSources, parallelCfg, resultKind, sources }

/-- Handle errors in model checking computations. -/
private def handleModelCheckError (ctx : ExecutionContext) (e : Exception) : CommandElabM Unit := do
  let json := errorJson s!"{← e.toMessageData.toString}"
  logModelCheckResult ctx.resultKind ctx.stx json
  ModelChecker.Concrete.finishProgress ctx.instanceId json

/-- Finish model checking with a successful result. -/
private def finishWithResult (ctx : ExecutionContext) (json : Json) : CommandElabM Unit := do
  if resultWasCancelled json then
    ModelChecker.Concrete.cancelProgress ctx.instanceId json
    return
  -- Cancellation can arrive after the computation returns. Honor it before
  -- publishing a verdict; `checkCancelled` still permits a verdict during handoff.
  if ← checkCancelled ctx.cancelToken ctx.instanceId then return
  let json := enrichJsonWithAssertions json ctx.assertionSources
  -- For the trace display of the infoview to link the actions and the properties to their sources
  let json := if json matches .obj _ && !ctx.sources.isNull then json.setObjVal! "sources" ctx.sources else json
  logModelCheckResult ctx.resultKind ctx.stx json
  ModelChecker.Concrete.finishProgress ctx.instanceId json

/-- Run the compiled binary and log the result. -/
private def runBinaryAndLogResult (ctx : ExecutionContext) (buildFolder : System.FilePath)
    (sourceFile : String) (command : ModelChecker.Compilation.CompiledCommandSpec)
    (commandId : String) : CommandElabM Unit := do
  let some binPath ← verifyBinaryExists buildFolder ctx.instanceId | return
  let args := ctx.parallelCfg.map (fun p => #[s!"{p.numSubTasks}", s!"{p.thresholdToParallel}", s!"{p.numSubSteps}"]) |>.getD #[]
  let some json ← runBinaryForJson binPath args ctx.instanceId ctx.cancelToken | return
  ModelChecker.Compilation.markRegistryFinished sourceFile command commandId buildFolder
  finishWithResult ctx json

/-- Compile the model. Return `none` on interruption; throw on compilation failure. -/
private def compileModel (sourceFile : String) (callExpr : Term)
    (commandId : String) (instanceId : Nat) (cancelToken : IO.CancelToken)
    (command : ModelChecker.Compilation.CompiledCommandSpec) : CommandElabM (Option System.FilePath) := do
  if ← cancelToken.isSet then return none
  let cCode ← generateCCode command callExpr
  if ← cancelToken.isSet then return none
  let imports ← liftCoreM <| ModelChecker.Compilation.executionImports (← getEnv)
  let buildFolder ← ModelChecker.Compilation.generateBuildFolderName sourceFile command cCode imports
  let lake ← ModelChecker.Compilation.getLakeExecutable
  let sourcePath := (← IO.currentDir) / sourceFile
  ModelChecker.Compilation.markRegistryInProgress sourceFile command commandId instanceId buildFolder
  let result? ← ModelChecker.Compilation.withBuildLock (← ModelChecker.Compilation.getBuildBaseDir) cancelToken
      (isCurrent := ModelChecker.Compilation.stillCurrentCont sourceFile command commandId instanceId (pure ())) do
    ModelChecker.Compilation.useBuildFolder instanceId buildFolder
    ModelChecker.Compilation.writeBuildInputs buildFolder cCode imports
    ModelChecker.Compilation.runProcessWithStatusCallback
      sourceFile
      command
      commandId
      { cmd := lake.toString, args := #["script", "run", "veilModelCheckBuild", sourcePath.toString, buildFolder.toString] }
      instanceId cancelToken
      (fun elapsedMs => ModelChecker.Concrete.updateCompilationElapsed instanceId elapsedMs)
      (fun line isError elapsedMs => ModelChecker.Concrete.updateCompilationLog instanceId elapsedMs line isError)
  let some result := result? | return none
  if result.interrupted then
    return none
  if result.exitCode != 0 then
    throwError "{mkCompilationErrorMsg result}"
  ModelChecker.Concrete.updateCompilationStatus instanceId .succeeded
  return some buildFolder

/-- Handle interpreted mode: evaluate and display results directly. -/
private def runInterpreted
    (kind : TraceDisplay.ResultKind) (mod : Module) (stx : Syntax) (callExpr : Term)
    (parallelCfg : Option ModelChecker.ParallelConfig) : CommandElabM Unit := do
  let ctx ← allocExecutionContext mod stx parallelCfg kind
  let ioComputation ← elaborateInterpretedComputation ctx.instanceId callExpr parallelCfg
  let computation ← Command.wrapAsyncAsSnapshot (fun () => do
    try
      if ← checkCancelled ctx.cancelToken ctx.instanceId then return
      let json ← IO.ofExcept (← ioComputation.toIO')
      finishWithResult ctx json
    catch e : Exception =>
      handleModelCheckError ctx e
    finally
      endRunIfCancelled ctx.cancelToken ctx.instanceId
  ) ctx.cancelToken
  let mkTask ← BaseIO.asTask (computation ()) (prio := .dedicated)
  Command.logSnapshotTask { stx? := none, cancelTk? := ctx.cancelToken, task := mkTask }
  ModelChecker.displayStreamingProgress stx ctx.instanceId

/-- Compile `callExpr` in the background, then pass the build folder to `withBinary`, with the source
file and the identity of the command in it. The build folder stays in use until `withBinary`
returns. Compilation failures are logged at `stx`; `onError` handles the other exceptions. -/
private def compileThen (command : ModelChecker.Compilation.CompiledCommandSpec) (stx : Syntax)
    (callExpr : Term) (instanceId : Nat) (cancelToken : IO.CancelToken)
    (withBinary : (buildFolder : System.FilePath) → (sourceFile commandId : String) → CommandElabM Unit)
    (onError : Exception → CommandElabM Unit) : CommandElabM Unit := do
  let sourceFile ← getFileName
  let commandId ← getCompiledCommandId s!"#{command.name}" stx

  let compilationComputation ← Command.wrapAsyncAsSnapshot (fun () => do
    try
      let some buildFolder ← withCompilationDiagnostics stx instanceId false <|
        compileModel sourceFile callExpr commandId instanceId cancelToken command | return
      if ← checkCancelled cancelToken instanceId then return
      withBinary buildFolder sourceFile commandId
    catch e : Exception =>
      onError e
    finally
      endRunIfCancelled cancelToken instanceId
      releaseBuild instanceId
  ) cancelToken

  let compilationTask ← BaseIO.asTask (compilationComputation ()) (prio := .dedicated)
  Command.logSnapshotTask { stx? := none, cancelTk? := cancelToken, task := compilationTask }

/-- Handle compiled-only mode: compile and run binary without interpreted fallback. -/
private def runCompiled (command : ModelChecker.Compilation.CompiledCommandSpec)
    (kind : TraceDisplay.ResultKind) (mod : Module) (stx : Syntax) (callExpr : Term)
    (parallelCfg : Option ModelChecker.ParallelConfig) : CommandElabM Unit := do
  let ctx ← allocExecutionContext mod stx parallelCfg kind
  compileThen command stx callExpr ctx.instanceId ctx.cancelToken
    (fun buildFolder sourceFile commandId =>
      runBinaryAndLogResult ctx buildFolder sourceFile command commandId)
    (handleModelCheckError ctx)
  ModelChecker.displayStreamingProgress stx ctx.instanceId

/-- Handle default mode: run interpreted + background compile with handoff. -/
private def runWithHandoff (command : ModelChecker.Compilation.CompiledCommandSpec)
    (kind : TraceDisplay.ResultKind) (mod : Module) (stx : Syntax) (callExpr : Term)
    (parallelCfg : Option ModelChecker.ParallelConfig) : CommandElabM Unit := do
  let ctx ← allocExecutionContext mod stx parallelCfg kind
  let sourceFile ← getFileName
  let commandId ← getCompiledCommandId s!"#{command.name}" stx
  let ioComputation ← elaborateInterpretedComputation ctx.instanceId callExpr parallelCfg

  -- Register the compilation token before starting either task.
  let compilationCancelTk ← IO.CancelToken.new
  liftIO <| ModelChecker.Concrete.setCompilationCancelToken ctx.instanceId (some compilationCancelTk)
  -- Interpreted mode task (wrapped for async logging)
  let interpretedComputation ← Command.wrapAsyncAsSnapshot (fun () => do
    try
      let json ← IO.ofExcept (← ioComputation.toIO')
      match (← ctx.cancelToken.isSet, ← ModelChecker.Concrete.checkHandoffRequested ctx.instanceId) with
      | (true, false) =>
        -- User clicked Stop
        ModelChecker.Concrete.cancelProgress ctx.instanceId
          -- If the result was already cancelled, propagate that since it may carry additional information
          (if resultWasCancelled json then json else Json.mkObj [("result", "cancelled")])
      | (false, _) => finishWithResult ctx json
      | (true, true) =>
          -- Handoff requested, let the compiled binary take over -- unless this run
          -- had already finished in the window before the handoff landed, in which
          -- case its verdict stands and the binary would only redo the work.
          unless resultWasCancelled json do
            finishWithResult ctx json
    catch e : Exception =>
      handleModelCheckError ctx e
    finally
      endRunIfCancelled ctx.cancelToken ctx.instanceId
  ) ctx.cancelToken
  let interpretedTask ← BaseIO.asTask (interpretedComputation ()) (prio := .dedicated)
  Command.logSnapshotTask { stx? := none, cancelTk? := ctx.cancelToken, task := interpretedTask }

  -- Background compilation with handoff. The token is registered on the progress
  -- instance so that `requestCancellation` (the Stop button) also kills the
  -- background native build, not just the interpreted search.
  let finishCompilation (buildFolder : System.FilePath) : IO Unit := do
    ModelChecker.Compilation.markRegistryFinished sourceFile command commandId buildFolder
    ModelChecker.Concrete.setCompilationCancelToken ctx.instanceId none
  let compilationComputation ← Command.wrapAsyncAsSnapshot (fun () => do
    try
      let some buildFolder ← withCompilationDiagnostics stx ctx.instanceId true <|
        compileModel sourceFile callExpr commandId ctx.instanceId compilationCancelTk
        command | do
          ModelChecker.Concrete.setCompilationCancelToken ctx.instanceId none
          return
      -- Skip handoff if violation found or interpreted finished
      if (← ModelChecker.Concrete.isViolationFound ctx.instanceId) || (← IO.hasFinished interpretedTask) ||
          (← ModelChecker.Concrete.isCancelled ctx.instanceId) then
        finishCompilation buildFolder
        return
      -- Handoff to compiled binary
      ModelChecker.Concrete.requestHandoff ctx.instanceId
      ctx.cancelToken.set
      let _ ← IO.wait interpretedTask
      -- The interpreted run can finish in the window between the check above and the
      -- handoff request. In that case, it then reports its own result.
      if (← ModelChecker.Concrete.getResultJson ctx.instanceId).isSome then
        finishCompilation buildFolder
        return
      -- If the user cancels the run, then early returns.
      if ← compilationCancelTk.isSet then
        ModelChecker.Concrete.cancelProgress ctx.instanceId
        finishCompilation buildFolder
        return
      let some newCancelToken ← ModelChecker.Concrete.resetProgressForHandoff ctx.instanceId | do
        ModelChecker.Concrete.setCompilationCancelToken ctx.instanceId none
        return
      -- The editor owns the compilation snapshot's token even after handoff.
      -- Without this forwarding, cancelling the old snapshot in the editor does not
      -- reach the binary's fresh token, so the binary continues running.
      compilationCancelTk.onSet newCancelToken.set
      -- Compilation is done; the binary run is guarded by the fresh token instead.
      ModelChecker.Concrete.setCompilationCancelToken ctx.instanceId none
      let ctxWithNewToken := { ctx with cancelToken := newCancelToken }
      try
        runBinaryAndLogResult ctxWithNewToken buildFolder sourceFile command commandId
      catch e : Exception =>
        handleModelCheckError ctxWithNewToken e
      finally
        -- If cancellation interrupts the native run before it reports a result,
        -- finalize it using the fresh token; completed verdicts remain untouched.
        endRunIfCancelled newCancelToken ctx.instanceId
    catch e : Exception =>
      ModelChecker.Concrete.setCompilationCancelToken ctx.instanceId none
      ModelChecker.Concrete.updateCompilationStatus ctx.instanceId (.failed s!"{← e.toMessageData.toString}")
    finally
      releaseBuild ctx.instanceId
  ) compilationCancelTk
  let compilationTask ← BaseIO.asTask (compilationComputation ()) (prio := .dedicated)
  Command.logSnapshotTask { stx? := none, cancelTk? := compilationCancelTk, task := compilationTask }

  ModelChecker.displayStreamingProgress stx ctx.instanceId

/-- Shared execution workflow for safety checking and simulation.
`callExpr` takes parallel configuration, progress ID, cancellation token, and a result
continuation, in that order. Its result must have a `ToJson` instance. -/
def run (command : ModelChecker.Compilation.CompiledCommandSpec)
    (kind : TraceDisplay.ResultKind) (mod : Module) (stx : Syntax)
    (mode : ModelCheckingMode) (callExpr : Term)
    (parallelCfg : Option ModelChecker.ParallelConfig := none) : CommandElabM Unit := do
  let mode := if (← liftIO isVeilOnlineEnv) then .interpreted else mode
  match mode with
  | .interpreted => runInterpreted kind mod stx callExpr parallelCfg
  | .compiled => runCompiled command kind mod stx callExpr parallelCfg
  | .default => runWithHandoff command kind mod stx callExpr parallelCfg

/-- Directory of the binaries that `buildOnly` builds. They are copied there out of their build
folders, which another check may prune before the binaries run. -/
private def getCheckerBaseDir : IO System.FilePath := do
  return (← IO.currentDir) / ".lake" / "model_checkers"

/-- Copy the binary built in `buildFolder` to `dir`, named after the folder. The copy replaces an
earlier one at once, so a process running the earlier one keeps it. Call it while holding
`withBuildLock` and the folder's use lock. -/
private def copyCheckerBinary (buildFolder dir : System.FilePath) : IO System.FilePath := do
  let name := buildFolder.fileName.getD "ModelCheckerMain"
  let dest := ModelChecker.Compilation.buildFolderBinary dir name
  -- Hidden, so that `pruneCheckerBinaries` leaves an unfinished copy alone
  let tmp := dir / s!".{name}.tmp"
  IO.FS.createDirAll dir
  IO.FS.writeBinFile tmp (← IO.FS.readBinFile (ModelChecker.Compilation.buildFolderBinary buildFolder))
  IO.setAccessRights tmp {
    user := { read := true, write := true, execution := true }
    group := { read := true, execution := true }
    other := { read := true, execution := true } }
  IO.FS.rename tmp dest
  return dest

/-- Delete the binaries in `dir` beyond the `keep` most recently copied ones; 0 means no limit. -/
private def pruneCheckerBinaries (dir : System.FilePath) (keep : Nat) : IO Unit := do
  if keep == 0 then return
  let mut binaries : Array (System.FilePath × IO.FS.SystemTime) := #[]
  for entry in ← dir.readDir do
    unless entry.fileName.startsWith "." do
      let copied ← try (·.modified) <$> entry.path.metadata catch _ => pure default
      binaries := binaries.push (entry.path, copied)
  let newestFirst := binaries.qsort fun a b => compare a.2 b.2 == .gt
  for (binary, _) in newestFirst.extract keep do
    -- A process running the binary keeps it
    try IO.FS.removeFile binary catch _ => pure ()

/-- Compile `callExpr` into a model checker binary in the background, as `runCompiled` does, but
without running it, and report where the binary is. The binary is copied out of its build folder,
which another check may prune before the binary runs. -/
def buildOnly (command : ModelChecker.Compilation.CompiledCommandSpec) (stx : Syntax) (callExpr : Term) :
    CommandElabM Unit := do
  -- The progress instance only follows the compilation, as nothing displays it
  let (instanceId, cancelToken) ← ModelChecker.Concrete.allocProgressInstance (.modelCheck {})
  let keep := veil.modelChecker.maxStoredCheckers.get (← getOptions)
  compileThen command stx callExpr instanceId cancelToken
    (fun buildFolder sourceFile commandId => do
      -- Copy under the build lock, so that no other build relinks the binary meanwhile
      let some binary ← ModelChecker.Compilation.withBuildLock
          (← ModelChecker.Compilation.getBuildBaseDir) cancelToken do
          let dir ← getCheckerBaseDir
          let binary ← copyCheckerBinary buildFolder dir
          pruneCheckerBinaries dir keep
          return binary
        | return
      ModelChecker.Compilation.markRegistryFinished sourceFile command commandId buildFolder
      ModelChecker.Concrete.finishProgress instanceId (Json.mkObj [("binary", toJson binary.toString)])
      logInfoAt stx m!"Model checker built: {binary}")
    (fun e => do
      let message ← e.toMessageData.toString
      ModelChecker.Concrete.finishProgress instanceId (errorJson message)
      logErrorAt stx message)

end Veil.ExecutionWorkflow
