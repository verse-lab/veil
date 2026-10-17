import Veil.Core.Tools.Verifier.Manager

open Lean Elab Command Veil

run_cmd do
  let mgr : VCManager Unit Unit ← VCManager.new (← Std.Channel.new)
  let (mgr, vcId) := mgr.addVC {name := `test, params := #[], statement := ← `(term| True), metadata := ()} {}
  let promise ← IO.Promise.new
  let d : Discharger Unit := {
    id := {managerId := mgr._managerId, vcId, dischargerId := 0, name := `late}
    cancelTk := ← IO.CancelToken.new, startTimePromise := ← IO.Promise.new
    resultPromise := promise, task := none, mkTask := pure (Task.pure default) }
  let failed := {mgr with _doneWith := mgr._doneWith.insert vcId .disproven}
  let failed := failed.addDischarger vcId d
  unless failed.isDone && failed._doneWith[vcId]? == some .disproven do
    throwError "late automatic discharger reopened conclusive failure without a runnable attempt"
  let retryable := {mgr with _doneWith := mgr._doneWith.insert vcId .error}
  unless !(retryable.addDischarger vcId d).isDone do
    throwError "late discharger did not reopen an inconclusive failure"
  unless !(failed.addDischarger vcId {d with isInteractive := true}).isDone do
    throwError "explicit interactive replacement could not reopen conclusive failure"
