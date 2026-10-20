module
meta import Veil.Core.Tools.Verifier.Server

open Lean Elab Command Veil Veil.Verifier

run_cmd do
  let origin ← IO.CancelToken.new
  let owner ← withReader (fun ctx : Command.Context => { ctx with cancelTk? := some origin }) do
    runManager (some origin)
    let owner ← getVCManagerOwner
    withVCManager fun ref => do
      let (mgr, _) := (← ref.get).addVC {
        name := `lateMutation, params := #[], statement := ← `(True), metadata := default } {}
      -- The lifetime callback is synchronous. Taking either mutex here from
      -- that callback would deadlock; cleanup must instead run after return.
      origin.set
      unless ← owner.cancelTk.isSet do
        throwError "origin cancellation was not immediately forwarded"
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
  IO.println "source-token alias and cancellation under owner lock complete finite cleanup: PASS"
