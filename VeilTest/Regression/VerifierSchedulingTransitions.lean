module

public meta import Veil.Core.Tools.Verifier.Manager

public meta section
open Lean Elab Command Veil

private def attempt (id : DischargerIdentifier) : BaseIO (Discharger Unit) := do
  return {
    id, task := none, cancelTk := ← IO.CancelToken.new
    startTimePromise := ← IO.Promise.new, resultPromise := ← IO.Promise.new
    mkTask := pure (Task.pure default)}

run_cmd do
  let mgr : VCManager Unit Unit ← VCManager.new (← Std.Channel.new)
  let (mgr, id) := mgr.addVC {name := `sequential, params := #[], statement := ← `(term| True), metadata := ()} {}
  let first ← attempt {managerId := mgr._managerId, vcId := id, dischargerId := 0, name := `first}
  let second ← attempt {first.id with dischargerId := 1, name := `second}
  -- The first worker publishes between the driver's reconcile and fill passes.
  let first := {first with task := some (Task.pure default)}
  first.resultPromise.resolve (.unknown none 0)
  let mgr := ((mgr.addDischarger id first).addDischarger id second).enableAll
  unless (← mgr.readyTasks).isEmpty do
    throwError "publication advanced scheduling before the result was committed"
  let mgr ← mgr.reconcileFinished
  let [(_, next)] ← mgr.readyTasks | throwError "committed failure did not enable the fallback"
  unless next.id == second.id do throwError "wrong fallback"
  -- Also guard the aggregate transition itself against running/exhausted confusion.
  let release ← IO.Promise.new
  let running := release.result!.map (fun (_ : Unit) => (default : Language.SnapshotTree))
  let vc := {mgr.nodes[id]! with dischargers := #[first, {second with task := some running}]}
  let mgr := {mgr with nodes := mgr.nodes.insert id vc, _dischargerResults := {}, _doneWith := {}}
  let mgr ← mgr.recordDischargerResult first.id (.unknown none 0)
  release.resolve ()
  unless !mgr.isDone do throwError "running fallback was treated as exhausted"

run_cmd do
  -- Result publication does not mean the worker has exited.
  let mgr : VCManager Unit Unit ← VCManager.new (← Std.Channel.new)
  let (mgr, id) := mgr.addVC {name := `cleanup, params := #[], statement := ← `(term| True), metadata := ()} {}
  let d ← attempt {managerId := mgr._managerId, vcId := id, dischargerId := 0, name := `cleanup}
  let release ← IO.Promise.new
  let task := release.result!.map (fun (_ : Unit) => (default : Language.SnapshotTree))
  let d := {d with task := some task}
  d.resultPromise.resolve (.proven (some (mkConst ``True.intro)) none 0)
  let mgr := mgr.addDischarger id d
  unless (← mgr.inFlightCount) == 1 do throwError "published result released an occupied physical slot"
  let retired := {mgr with nodes := {}, retiredDischargers := #[d]}
  unless (← retired.reconcileFinished).retiredDischargers.size == 1 do
    throwError "published but still-running retired worker was discarded"
  release.resolve ()
  let _ ← IO.wait task
  unless (← mgr.inFlightCount) == 0 do throwError "exited worker retained capacity"

run_cmd do
  let mgr : VCManager Nat Unit ← VCManager.new (← Std.Channel.new)
  let data : VCData Nat := {name := `primary, params := #[], statement := ← `(term| True), metadata := 0}
  let (mgr, primary) := mgr.addVC data {}
  let (mgr, alt) := mgr.addAlternativeVC {data with name := `alternative, metadata := 1} primary
  let (mgr, _) := mgr.addVC {data with name := `leaf, metadata := 2} {alt}
  let mut mgr := mgr
  for id in [:3] do
    mgr ← mgr.mkAddDischarger id fun _ id _ => attempt id
  mgr := mgr.enableMatching (· == 2)
  let .ok () := mgr.validateRegistrations | throwError "unexpected rejection"
  let [(_, ready)] ← mgr.readyTasks | throwError "dormant prerequisite cannot execute"
  unless ready.id.vcId == alt && !mgr.enabledVCs.contains primary do
    throwError "explicit prerequisite did not run independently of its primary"
