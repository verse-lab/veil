import Veil.Core.Tools.Verifier.Results

open Lean Elab Command Veil

private def testDischarger (id : DischargerIdentifier) (result : Option (DischargerResult Unit)) : BaseIO (Discharger Unit) := do
  let promise ← IO.Promise.new
  if let some result := result then promise.resolve result
  return {
    id, cancelTk := ← IO.CancelToken.new, task := none
    startTimePromise := ← IO.Promise.new, resultPromise := promise
    mkTask := pure (Task.pure default) }

run_cmd do
  let ch ← Std.Channel.new
  let mgr : VCManager VCMetadata Unit ← VCManager.new ch
  let data : VCData VCMetadata := {name := `test, params := #[], statement := ← `(term| True), metadata := default}
  let (mgr, parent) := mgr.addVC data {}
  let (mgr, child) := mgr.addVC data ((Std.HashSet.emptyWithCapacity).insert parent)
  let (mgr, grandchild) := mgr.addVC data ((Std.HashSet.emptyWithCapacity).insert child)
  let parentId : DischargerIdentifier := {managerId := mgr._managerId, vcId := parent, dischargerId := 0, name := `parent}
  let childId := {parentId with vcId := child, name := `child}
  let grandchildId := {parentId with vcId := grandchild, name := `grandchild}
  let mgr := mgr.addDischarger parent (← testDischarger parentId (some (.error #[] 0)))
  let mgr := mgr.addDischarger child (← testDischarger childId none)
  let mgr := mgr.addDischarger grandchild (← testDischarger grandchildId none)
  let mgr ← mgr.enableAll.reconcileFinished
  unless mgr.isDone && mgr._doneWith[child]? == some .error && mgr._doneWith[grandchild]? == some .error do
    throwError "failed prerequisite left transitive dependents pending"
  let result ← liftCoreM (mgr.toResults (fun _ => true))
  let some childResult := result.vcs.find? (·.id == child) | throwError "missing dependent result"
  unless childResult.timing.dischargers.any (fun d => d.name == `dependency) do
    throwError "blocked result lost its prerequisite diagnostic"
  let (mgr, late) := mgr.addVC data ((Std.HashSet.emptyWithCapacity).insert parent)
  unless mgr._doneWith[late]? == some .error do throwError "late dependent of a failed VC was not blocked"
  -- Registering another solver reopens the failed prerequisite and dependents.
  let retryId := {parentId with dischargerId := 1}
  let mgr := mgr.addDischarger parent (← testDischarger retryId (some (.proven (some (mkConst ``True.intro)) none 0)))
  let mgr ← mgr.reconcileFinished
  unless mgr._doneWith[parent]? == some .proven && !mgr._doneWith.contains child && !mgr._doneWith.contains grandchild do
    throwError "dependent failure did not recover after prerequisite retry"
  let ready ← mgr.readyTasks
  let [(readyVC, _)] := ready | throwError "expected one ready dependent"
  unless readyVC.uid == child do
    throwError "recovered dependency chain did not schedule the next prerequisite"
