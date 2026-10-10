import Veil.Core.Tools.Verifier.Manager

open Lean Elab Command Veil

private def fresh (id : DischargerIdentifier) (interactive := false) : BaseIO (Discharger Unit) := do
  return {
    id, isInteractive := interactive, cancelTk := ← IO.CancelToken.new, task := none
    startTimePromise := ← IO.Promise.new, resultPromise := ← IO.Promise.new
    mkTask := pure (Task.pure default) }

private def finish (mgr : VCManager Unit Unit) (vcId dischargerId : Nat)
    (result : DischargerResult Unit) : CommandElabM (VCManager Unit Unit) := do
  let some d := mgr.nodes[vcId]!.dischargers[dischargerId]? | throwError "missing test discharger"
  d.resultPromise.resolve result
  mgr.recordDischargerResult d.id result

private def replaceParent (mgr : VCManager Unit Unit) (result : DischargerResult Unit) : CommandElabM (VCManager Unit Unit) := do
  let id : DischargerIdentifier := {managerId := mgr._managerId, vcId := 0, dischargerId := mgr.nodes[0]!.dischargers.size, name := `interactive}
  let mgr := mgr.addDischarger 0 (← fresh id true)
  finish mgr 0 id.dischargerId result

private def chain : CommandElabM (VCManager Unit Unit) := do
  let ch ← Std.Channel.new
  let mgr : VCManager Unit Unit ← VCManager.new ch
  let data : VCData Unit := {name := `test, params := #[], statement := ← `(term| True), metadata := ()}
  let (mgr, root) := mgr.addVC data {}
  let (mgr, child) := mgr.addVC data ((Std.HashSet.emptyWithCapacity).insert root)
  let (mgr, _) := mgr.addVC data ((Std.HashSet.emptyWithCapacity).insert child)
  let mut mgr := mgr
  for id in [:3] do
    mgr ← mgr.mkAddDischarger id fun _ id _ => fresh id
  return mgr.enableAll

run_cmd do
  let proof : DischargerResult Unit := .proven (some (mkConst ``True.intro)) none 0
  let mut mgr ← chain
  for id in [:3] do mgr ← finish mgr id 0 proof
  let some oldChild := mgr.nodes[1]!.dischargers[0]? | throwError "missing child"
  mgr ← replaceParent mgr (.error #[] 0)
  unless mgr._doneWith[1]? == some .error && mgr._doneWith[2]? == some .error do
    throwError "withdrawn proof left transitive descendants successful"
  unless mgr.provenWitness? 1 |>.isNone do throwError "retained invalidated child witness"
  mgr ← mgr.recordDischargerResult oldChild.id proof
  unless mgr._doneWith[1]? == some .error do throwError "late completion restored an invalidated proof"
  mgr ← replaceParent mgr proof
  let some child := mgr.nodes[1]!.dischargers[0]? | throwError "missing recreated child"
  unless child.id.revision == oldChild.id.revision + 1 && !(← child.cancelTk.isSet) do
    throwError "dependent did not receive fresh attempt resources"
  let [(ready, _)] ← mgr.readyTasks | throwError "expected only the next dependent to be ready"
  unless ready.uid == 1 do throwError "dependency ordering was lost during restart"
  mgr ← finish mgr 1 0 proof
  mgr ← finish mgr 2 0 proof
  unless mgr._totalSolved == 3 && mgr.isDone do throwError "recreated dependency chain failed to finish"

run_cmd do
  let proof : DischargerResult Unit := .proven (some (mkConst ``True.intro)) none 0
  let mgr ← finish (← chain) 0 0 proof
  let some child := mgr.nodes[1]!.dischargers[0]? | throwError "missing child"
  let release ← IO.Promise.new
  let task := release.result!.map (fun (_ : Unit) => (default : Language.SnapshotTree))
  let child := {child with task := some task}
  let vc := {mgr.nodes[1]! with dischargers := #[child]}
  let mgr := {mgr with nodes := mgr.nodes.insert 1 vc}
  let mgr ← replaceParent mgr (.error #[] 0)
  unless (← child.cancelTk.isSet) && mgr.retiredDischargers.size == 1 && (← mgr.inFlightCount) == 1 do
    throwError "displaced running attempt lost cancellation or capacity accounting"
  release.resolve ()
  let _ ← IO.wait task
  child.resultPromise.resolve proof
  let mgr ← mgr.reconcileFinished
  unless mgr.retiredDischargers.isEmpty && (← mgr.inFlightCount) == 0 do
    throwError "finished retired attempt was not reclaimed"
  let mgr ← mgr.recordDischargerResult child.id proof
  unless mgr._doneWith[1]? == some .error do throwError "retired attempt overwrote its replacement"

run_cmd do
  -- A custom completed attempt without a reconstruction factory cannot be
  -- safely restarted. It gets an explicit error rather than its old witness.
  let proof : DischargerResult Unit := .proven (some (mkConst ``True.intro)) none 0
  let mut mgr ← chain
  mgr := {mgr with factories := mgr.factories.erase (1, 0)}
  mgr ← finish mgr 0 0 proof
  mgr ← finish mgr 1 0 proof
  mgr ← replaceParent mgr (.error #[] 0)
  mgr ← replaceParent mgr proof
  mgr ← mgr.reconcileFinished
  unless mgr._doneWith[1]? == some .error do throwError "unsupported restart reused a stale proof"
  let result : Option (DischargerResult Unit) := mgr._dischargerResults[(1, 0)]?
  let some (.error errors _) := result | throwError "missing restart diagnostic"
  unless errors.any (fun (_, json) => json == toJson "Verification invalidated: prerequisite VC 0 changed; re-register this discharger or regenerate the specification") do
    throwError "unsupported restart was not explained"
