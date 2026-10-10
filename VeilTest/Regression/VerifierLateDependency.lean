import Veil.Core.Tools.Verifier.Manager

open Lean Elab Command Veil

run_cmd do
  let ch ← Std.Channel.new
  let mgr : VCManager Unit Unit ← VCManager.new ch
  let data : VCData Unit := {name := `test, params := #[], statement := ← `(term| True), metadata := ()}
  let (mgr, parent) := mgr.addVC data {}
  let mgr := {mgr with _doneWith := mgr._doneWith.insert parent .proven}
  let (mgr, child) := mgr.addVC data ((Std.HashSet.emptyWithCapacity).insert parent)
  unless mgr.inDegree[child]? == some 0 do
    throwError "late dependent still waits for an already completed proof"
  let (mgr, pending) := mgr.addVC data {}
  let (mgr, child) := mgr.addVC data (((Std.HashSet.emptyWithCapacity).insert parent).insert pending)
  unless mgr.inDegree[child]? == some 1 do
    throwError "dependency count must include only outstanding prerequisites"
