import Veil.Frontend.DSL.Module.Util.Compilation
import Veil.Frontend.DSL.Module.AssertionInfo

/-!
Execution shared by `#model_check` and `#simulate`. Elaboration supplies an
interpreted computation, a compiler, and a binary runner; the same drivers are
also exercised with controlled computations in the regression tests.
-/

namespace Veil.CommandRunner
open Lean Elab Command
open ModelChecker.Concrete
open ModelChecker.Compilation (BuildResult cancelledJson)

/-- Live command state. Compilation inputs are prepared separately, only when needed. -/
structure Context where
  stx : Syntax
  instanceId : Nat
  /-- Shared by both snapshot tasks, the engines, and the subprocess monitors.
  Only Stop/editor cancellation sets this token; handoff uses its own flag. -/
  cancelToken : IO.CancelToken
  assertionSources : Std.HashMap AssertionId AssertionSourceInfo := {}
  resultKind : TraceDisplay.ResultKind

private def resultWasCancelled (json : Json) : Bool :=
  json.getObjValD "result" == Json.str "cancelled"

private def errorJson (message : String) : Json := Json.mkObj [("error", message)]

private def logResult (ctx : Context) (json : Json) : CommandElabM Unit := do
  let msg := TraceDisplay.formatResult ctx.resultKind json
  let isViolation := json.getObjValD "result" == Json.str "found_violation" ||
    json.getObjValD "error" != .null
  if isViolation && veil.violationIsError.get (← getOptions) then
    logErrorAt ctx.stx msg
  else
    logInfoAt ctx.stx msg

/-- The owner of the result calls this once. Preserve cancellation metadata when
available, and accept cancellation observed before publishing a verdict. -/
private def finishWithResult (ctx : Context) (json : Json) : CommandElabM Unit := do
  let json := if (← ctx.cancelToken.isSet) && !resultWasCancelled json then cancelledJson else json
  let json := enrichJsonWithAssertions json ctx.assertionSources
  if resultWasCancelled json then
    cancelProgress ctx.instanceId json
  else
    finishProgress ctx.instanceId json
  logResult ctx json

private def handleError (ctx : Context) (e : Exception) : CommandElabM Unit := do
  if ← ctx.cancelToken.isSet then
    cancelProgress ctx.instanceId
  else
    finishWithResult ctx (errorJson (← e.toMessageData.toString))

private def spawn (ctx : Context) (action : CommandElabM Unit) :
    CommandElabM (Task Language.SnapshotTree) := do
  let computation ← Command.wrapAsyncAsSnapshot (fun () => do
    try action catch e : Exception => handleError ctx e
  ) ctx.cancelToken
  let task ← BaseIO.asTask (computation ()) (prio := .dedicated)
  Command.logSnapshotTask { stx? := none, cancelTk? := ctx.cancelToken, task }
  return task

/-- Interpreted execution owns publication unless it yields to a handoff. -/
def runInterpreted (ctx : Context) (computation : IO Json) :
    CommandElabM (Task Language.SnapshotTree) :=
  spawn ctx do
    if ← ctx.cancelToken.isSet then
      cancelProgress ctx.instanceId
      return
    let json ← computation
    if !(← ctx.cancelToken.isSet) && (← checkHandoffRequested ctx.instanceId) && resultWasCancelled json then
      return
    finishWithResult ctx json

/-- Catch build exceptions at the compilation stage, not around binary execution. -/
private def tryCompile (ctx : Context) (compile : IO BuildResult) : IO BuildResult := do
  if ← ctx.cancelToken.isSet then return .interrupted
  try compile catch e => return .failed e.toString

private def runBinaryAndFinish (ctx : Context) (folder : System.FilePath)
    (runBinary : System.FilePath → IO Json) : CommandElabM Unit := do
  if ← ctx.cancelToken.isSet then
    cancelProgress ctx.instanceId
    return
  finishWithResult ctx (← runBinary folder)

def runCompiled (ctx : Context) (compile : IO BuildResult)
    (runBinary : System.FilePath → IO Json) : CommandElabM (Task Language.SnapshotTree) :=
  spawn ctx do
    match ← tryCompile ctx compile with
    | .interrupted => cancelProgress ctx.instanceId
    | .failed message =>
        updateCompilationStatus ctx.instanceId (.failed message)
        finishWithResult ctx (errorJson message)
    | .built folder =>
        updateCompilationStatus ctx.instanceId .succeeded
        runBinaryAndFinish ctx folder runBinary

/-- Keep separate snapshot tasks so an interpreted verdict can be displayed
while compilation continues to fill its cache. The compiled task takes ownership
of the result only after joining the interpreted task and finding no result. -/
def runWithHandoff (ctx : Context) (computation : IO Json) (compile : IO BuildResult)
    (runBinary : System.FilePath → IO Json) :
    CommandElabM (Task Language.SnapshotTree × Task Language.SnapshotTree) := do
  let interpretedTask ← runInterpreted ctx computation
  let compilationTask ← spawn ctx do
    match ← tryCompile ctx compile with
    | .interrupted => pure () -- The interpreted task owns cancellation/finalization.
    | .failed message => updateCompilationStatus ctx.instanceId (.failed message)
    | .built folder =>
        updateCompilationStatus ctx.instanceId .succeeded
        if (← isViolationFound ctx.instanceId) || (← IO.hasFinished interpretedTask) ||
            (← ctx.cancelToken.isSet) then return
        requestHandoff ctx.instanceId
        let _ ← IO.wait interpretedTask
        -- The interpreted task may have produced a verdict just as we requested
        -- handoff. Its result (including errors and cancellation) takes precedence.
        if (← getResultJson ctx.instanceId).isSome then return
        if ← ctx.cancelToken.isSet then
          cancelProgress ctx.instanceId
          return
        resetProgressForHandoff ctx.instanceId
        runBinaryAndFinish ctx folder runBinary
  return (interpretedTask, compilationTask)

end Veil.CommandRunner
