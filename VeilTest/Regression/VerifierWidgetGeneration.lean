module
meta import all Veil.Frontend.DSL.Module.Elaborators.Verification
meta import all Veil.Core.Tools.ModelChecker.Symbolic.TraceLang
meta import all Veil.Core.UI.Verifier.VerificationResults
meta import VeilTest.Regression.VerifierGenerationSupport
meta import Batteries.Tactic.OpenPrivate

open Lean Elab Command Veil Veil.Verifier ProofWidgets VeilTest.VerifierGeneration
meta section

open private Veil.captureInvariantResults from Veil.Frontend.DSL.Module.Elaborators.Verification
open private Veil.runTraceRefreshStep from Veil.Core.Tools.ModelChecker.Symbolic.TraceLang
open private Veil.Verifier.runStreamingResults from Veil.Core.UI.Verifier.VerificationResults

/-- Run the actual refresh loops, checking their first publication or completion.
The timeout bounds a broken test; it does not select the replacement ordering. -/
private def refresh (traceWidget : Bool) (owner : VCManagerEnvironment)
    (getManager : BaseIO (VCManager VCMetadata SmtResult)) (managerId : ManagerId)
    (getter : CoreM (VerificationResults VCMetadata SmtResult × StreamingStatus))
    (shouldReject : Bool) : CommandElabM Unit := do
  let (_, token) ← ProofWidgets.mkRefreshComponent
  let initialVersion := (← token.state.get).idx
  let tk ← IO.CancelToken.new
  let wrapped ← liftCoreM <| Core.wrapAsyncAsSnapshot (fun () => do
    if traceWidget then
      runTraceRefreshStep owner getManager managerId false `original (fun _ => true) token
    else
      runStreamingResults { line := 0, character := 0 } none "" getter token) tk
  let task ← (wrapped ()).asTask (prio := .dedicated)
  try
    await "refresh completes or publishes" do
      return (← IO.hasFinished task) || (← token.state.get).idx > initialVersion
    let updated := (← token.state.get).idx > initialVersion
    check (updated != shouldReject) s!"widget (trace={traceWidget}) accepted stale generation or lost current result"
    if shouldReject then
      check (← IO.hasFinished task) "stale widget kept refreshing"
    else
      await "current widget completes" (IO.hasFinished task)
  finally
    if !(← IO.hasFinished task) then owner.cancelTk.set
    tk.set
    await "refresh cleanup" (IO.hasFinished task)
    discard <| IO.wait task

private def checkCase (traceWidget : Bool) (replacementBoundary : Nat) : CommandElabM Unit := do
  runManager
  let _ ← fresh #[`original] (replacementBoundary == 3)
  let owner ← getVCManagerOwner
  let savedTasks := (← get).snapshotTasks
  modify fun st => { st with snapshotTasks := #[] }
  let calls ← IO.mkRef 0
  let requested ← runFilteredAsyncWithManagerId (fun _ => true) (fun _ => calls.modify (· + 1))
  let some observer := (← get).snapshotTasks[0]? | throwError "async start lost observer snapshot"
  modify fun st => { st with snapshotTasks := savedTasks }
  try
    -- 0: reset after actual async start and before widget construction.
    if replacementBoundary == 0 then reset requested
    let getter ← captureInvariantResults requested (fun _ => true)
    let getManager ← captureVCManager
    -- 1: reset after the widget captures its proof checkpoint but before it reads.
    if replacementBoundary == 1 then reset requested
    -- 2: the owner is canceled in the same generation.
    if replacementBoundary == 2 then owner.cancelTk.set
    refresh traceWidget owner getManager requested getter (replacementBoundary != 3)
    await "observer completion" (IO.hasFinished observer.task)
    discard <| IO.wait observer.task
    check ((← calls.get) == if replacementBoundary == 3 then 1 else 0)
      "stale callback fired or current callback was lost"
    IO.println s!"widget generation (trace={traceWidget}, boundary={replacementBoundary}): PASS"
  finally
    owner.cancelTk.set
    observer.cancelRec
    await "observer cleanup" (IO.hasFinished observer.task)
    discard <| IO.wait observer.task

run_cmd do
  for traceWidget in [false, true] do
    for boundary in [0, 1, 2, 3] do
      checkCase traceWidget boundary
