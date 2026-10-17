import Veil.Core.Tools.Verifier.Manager

open Lean Elab Command Veil

private def finished (id : DischargerIdentifier) (result : DischargerResult Unit)
    (interactive := false) : BaseIO (Discharger Unit) := do
  let resultPromise ← IO.Promise.new
  resultPromise.resolve result
  return {
    id, isInteractive := interactive, resultPromise
    cancelTk := ← IO.CancelToken.new
    task := none, startTimePromise := ← IO.Promise.new
    mkTask := pure (Task.pure default) }

run_cmd do
  let ch ← Std.Channel.new
  let mgr : VCManager Unit Unit ← VCManager.new ch
  let (mgr, vcId) := mgr.addVC { name := `test, params := #[], statement := ← `(term| True), metadata := () } {}
  let id : DischargerIdentifier := {managerId := mgr._managerId, vcId, dischargerId := 0, name := `test}
  let success : DischargerResult Unit := .proven (some (mkConst ``True.intro)) none 0
  let failure : DischargerResult Unit := .error #[] 0
  let mgr := mgr.addDischarger vcId (← finished id success)
  -- A previous manager's result must be rejected even on direct delivery.
  let wrongManager ← mgr.recordDischargerResult {id with managerId := id.managerId + 1} success
  unless wrongManager.provenWitness? vcId |>.isNone do throwError "accepted another manager's result"
  -- Unknown slots must never manufacture a successful witness/index.
  let wrongSlot ← mgr.recordDischargerResult {id with dischargerId := 1} success
  unless wrongSlot.provenWitness? vcId |>.isNone do throwError "accepted unknown discharger"
  let mgr ← mgr.recordDischargerResult id success
  let duplicate ← mgr.recordDischargerResult id failure
  unless duplicate._totalDischarged == 1 && duplicate._doneWith[vcId]? == some .proven do
    throwError "duplicate notification changed a recorded result"
  -- Replace the same slot, as interactive theorem re-registration does.
  let newId := {id with revision := 1}
  let d ← finished newId failure true
  let vc := { mgr.nodes[vcId]! with dischargers := #[d] }
  let mgr := {mgr with nodes := mgr.nodes.insert vcId vc, _dischargerResults := {}}
  let stale ← mgr.recordDischargerResult id success
  unless stale._dischargerResults.isEmpty do throwError "accepted old slot revision"
  let mgr ← stale.recordDischargerResult newId failure
  unless mgr._doneWith[vcId]? == some .error do throwError "replacement result not applied"
  let duplicate ← mgr.recordDischargerResult newId success
  unless duplicate._doneWith[vcId]? == some .error do throwError "duplicate resurrected replaced proof"
