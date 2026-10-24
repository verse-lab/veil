module
meta import Veil.Core.Tools.Verifier.TheoremDischarger
meta import VeilTest.Regression.VerifierObserverSupport

open Lean Elab Command Veil Veil.Verifier VeilTest.VerifierObserver
meta section

private def snapshots (mgr : VCManager VCMetadata SmtResult) :
    CommandElabM (Array (Language.SnapshotTask Language.SnapshotTree)) := do
  let saved := (← get).snapshotTasks
  modify fun st => { st with snapshotTasks := #[] }
  try
    discard <| logPendingDischargerTasks mgr (fun _ => true) {}
    return (← get).snapshotTasks
  finally
    modify fun st => { st with snapshotTasks := saved }

run_cmd do
  runManager
  let mgr ← readVCManager
  let automatic ← worker mgr 0 0 `automatic (.pure (← tree "automatic"))
  withVCManager fun ref => do
    let (mgr, _) := (← ref.get).addVC (← data `snapshotProof) {} #[automatic]
    ref.set mgr
  let automaticGetter ← captureVCManager
  elabCommand (← `(command| @[veil] public theorem $(mkIdent `snapshotProof) : True := True.intro))
  let proofSnapshots ← snapshots (← readVCManager)
  unless proofSnapshots.size == 1 do
    throwError "proof view attached hidden automatic snapshots"
  let some proofTree ← awaitTask "proof snapshot" proofSnapshots[0]!.task
    | throwError "missing proof snapshot"
  unless proofTree.element.diagnostics.msgLog.toArray.isEmpty do
    throwError "proof view attached hidden automatic diagnostics"
  let autoSnapshots ← snapshots (← automaticGetter)
  unless autoSnapshots.size == 1 do
    throwError "automatic checkpoint lost its snapshot"
  let some autoTree ← awaitTask "automatic snapshot" autoSnapshots[0]!.task
    | throwError "missing automatic snapshot"
  let diagnostics := autoTree.element.diagnostics.msgLog.toArray
  unless diagnostics.size == 1 do
    throwError "automatic checkpoint lost its diagnostic"
  unless (← diagnostics[0]!.data.toString) == "automatic diagnostic" do
    throwError "automatic checkpoint attached the wrong diagnostic"
  unless !(← automatic.cancelTk.isSet) do
    throwError "proof observation canceled shared automatic task"
  liftIO <| IO.println "proof snapshots hide automatic diagnostics; original automatic checkpoint retains them: PASS"
