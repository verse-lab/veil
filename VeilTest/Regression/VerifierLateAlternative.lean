import Veil.Core.Tools.Verifier.Manager

open Lean Elab Command Veil

run_cmd do
  let ch ← Std.Channel.new
  let mgr : VCManager Unit Unit ← VCManager.new ch
  let data : VCData Unit := {name := `test, params := #[], statement := ← `(term| True), metadata := ()}
  let (mgr, primary) := mgr.addVC data {}
  let failed := {mgr with _doneWith := mgr._doneWith.insert primary .error}
  let (failed, alternative) := failed.addAlternativeVC data primary
  unless !failed.dormantVCs.contains alternative && failed.enabledVCs.contains alternative do
    throwError "alternative registered after primary failure stayed dormant"
  let proven := {mgr with _doneWith := mgr._doneWith.insert primary .proven}
  let (proven, alternative) := proven.addAlternativeVC data primary
  unless proven.dormantVCs.contains alternative && !proven.enabledVCs.contains alternative do
    throwError "successful primary unnecessarily started its late alternative"
