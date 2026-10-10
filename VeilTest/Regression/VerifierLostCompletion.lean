import Veil.Core.Tools.Verifier.Manager

open Lean Elab Command Veil

run_cmd do
  let ch ← Std.Channel.new
  let mgr : VCManager Unit Unit ← VCManager.new ch
  let data : VCData Unit := {name := `test, params := #[], statement := ← `(term| True), metadata := ()}
  let (mgr, vcId) := mgr.addVC data {}
  let id : DischargerIdentifier := {managerId := mgr._managerId, vcId, dischargerId := 0, name := `broken}
  -- A custom task terminates without resolving its result or sending a message.
  let d : Discharger Unit := {
    id, cancelTk := ← IO.CancelToken.new, task := some (Task.pure default)
    startTimePromise := ← IO.Promise.new, resultPromise := ← IO.Promise.new
    mkTask := pure (Task.pure default) }
  let mgr := (mgr.addDischarger vcId d).enableAll
  let mgr ← mgr.reconcileFinished
  unless mgr._doneWith[vcId]? == some .error && (← mgr.inFlightCount) == 0 do
    throwError "finished task without a notification did not terminate its VC"
  unless mgr._totalDischarged == 1 do throwError "completion was not recorded"
  let mgr ← mgr.reconcileFinished
  unless mgr._totalDischarged == 1 do throwError "reconciliation recorded a completion twice"
  -- A resolved result with no channel notification is equally recoverable.
  let (mgr, vcId) := mgr.addVC data {}
  let promise ← IO.Promise.new
  promise.resolve (.proven (some (mkConst ``True.intro)) none 0)
  let d := {d with id := {id with vcId}, resultPromise := promise}
  let mgr ← (mgr.addDischarger vcId d).reconcileFinished
  unless mgr._doneWith[vcId]? == some .proven do throwError "lost successful notification was not recovered"
