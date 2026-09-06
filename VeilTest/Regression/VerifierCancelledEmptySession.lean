import Veil.Core.Tools.Verifier.Server

open Lean Elab Command Veil Veil.Verifier

run_cmd do
  let cancel ← IO.CancelToken.new
  runManager (some cancel)
  let session ← getSession
  cancel.set
  let mut rejected := false
  try let _ ← session.snapshot; pure ()
  catch ex => rejected := (← ex.toMessageData.toString).contains "cancelled"
  unless rejected do throwError "cancelled empty session exposed a successful snapshot"
  rejected := false
  try let _ ← waitFilteredSync (fun _ => true); pure ()
  catch ex => rejected := (← ex.toMessageData.toString).contains "cancelled"
  unless rejected do throwError "cancelled empty session returned empty success without a driver"
