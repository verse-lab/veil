module
meta import Veil.Core.Tools.Verifier.Server

open Lean Elab Command Veil Veil.Verifier

run_cmd do
  for supplied in [false, true] do
    let origin ← IO.CancelToken.new
    let owner ← withReader (fun ctx : Command.Context => { ctx with cancelTk? := some origin }) do
      runManager (if supplied then some origin else none)
      let owner ← getVCManagerOwner
      let some marker := (← get).snapshotTasks.back!.cancelTk?
        | throwError "missing owner marker"
      withVCManager fun ref => do
        let (mgr, _) := (← ref.get).addVC {
          name := `lateMutation, params := #[], statement := ← `(True), metadata := default } {}
        -- Both callbacks run synchronously. Taking either mutex here would
        -- deadlock; asynchronous cleanup must include this later mutation.
        origin.set
        unless (← owner.cancelTk.isSet) == supplied do
          throwError "implicit and explicitly supplied cancellation were confused"
        marker.set
        unless ← owner.cancelTk.isSet do
          throwError "source marker cancellation was not immediately forwarded"
        ref.set mgr
      return owner
    let deadline := (← IO.monoMsNow) + 2000
    while !(← owner.manager.atomically (m := BaseIO) fun ref => return (← ref.get).nodes.isEmpty) &&
        (← IO.monoMsNow) < deadline do
      IO.sleep 1
    unless (← owner.manager.atomically (m := BaseIO) fun ref => ref.get).nodes.isEmpty do
      throwError "cleanup failed to remove the mutation that raced cancellation"
    unless (← dispatcher.atomically (m := BaseIO) fun ref => return (← ref.get).owners.size) == 0 do
      throwError "cleanup retained canceled owner"
  IO.println "source marker and explicit-token cancellation under owner lock complete finite cleanup: PASS"
