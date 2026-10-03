import Veil.Core.Tools.Verifier.Manager

open Lean Elab Command Veil

run_cmd do
  let ch ← Std.Channel.new
  let mgr : VCManager Unit Unit ← VCManager.new ch
  let data : VCData Unit := {name := `test, params := #[], statement := ← `(term| True), metadata := ()}
  let (mgr, primary) := mgr.addVC data {}
  let (mgr, alternative) := mgr.addAlternativeVC data primary
  -- An interactive theorem can finish an alternative while it is dormant.
  let mgr := {mgr with _doneWith := mgr._doneWith.insert alternative .proven}
  unless !mgr.isDone do throwError "done/dormant overlap hid the unfinished primary"
  let mgr := {mgr with _doneWith := mgr._doneWith.insert primary .proven}
  unless mgr.isDone && mgr.isDoneFiltered (fun _ => true) do
    throwError "done/dormant overlap prevented completion"
