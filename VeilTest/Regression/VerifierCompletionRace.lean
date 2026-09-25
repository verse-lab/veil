import Veil.Core.Tools.Verifier.Manager

open Lean Elab Command Veil

run_cmd do
  let data : VCData Unit := {name := `race, params := #[], statement := ← `(term| True), metadata := ()}
  for i in [:3000] do
    let promise ← IO.Promise.new
    let gate ← IO.Promise.new
    let proof : DischargerResult Unit := .proven (some (mkConst ``True.intro)) none 0
    let task ← (do
      let _ ← IO.wait gate.result?
      promise.resolve proof
      pure (default : Language.SnapshotTree)).asTask (prio := .dedicated)
    let mgr : VCManager Unit Unit ← VCManager.new (← Std.Channel.new)
    let (mgr, _) := mgr.addVC data {}
    let d : Discharger Unit := {
      id := {managerId := mgr._managerId, vcId := 0, dischargerId := 0, name := `race}
      cancelTk := ← IO.CancelToken.new, task := some task
      startTimePromise := ← IO.Promise.new, resultPromise := promise
      mkTask := pure task }
    let mut mgr := (mgr.addDischarger 0 d).enableAll
    gate.resolve ()
    for _ in [:1000] do
      mgr ← mgr.reconcileFinished
      if mgr.isDone then break
    let _ ← IO.wait task
    mgr ← mgr.reconcileFinished
    unless mgr._doneWith[0]? == some .proven do
      throwError "reconciliation discarded a valid proof on iteration {i}"
