import Veil.Core.Tools.Verifier.Server

open Lean Elab Command Veil Veil.Verifier

run_cmd do
  runManager
  withVCManager fun ref => do
    let data : VCData VCMetadata := {name := `unconfigured, params := #[], statement := ← `(term| True), metadata := default}
    ref.set ((← ref.get).addVC data {}).1
  let mut rejected := false
  try startAll
  catch ex => rejected := (← ex.toMessageData.toString).contains "has no discharger"
  unless rejected do throwError "unconfigured VC did not fail explicitly at startup"

run_cmd do
  let mgr : VCManager Unit Unit ← VCManager.new (← Std.Channel.new)
  let data : VCData Unit := {name := `test, params := #[], statement := ← `(term| True), metadata := ()}
  let (mgr, primary) := mgr.addVC data {}
  let mgr := {mgr with _doneWith := mgr._doneWith.insert primary .proven}
  let (mgr, alternative) := mgr.addAlternativeVC data primary
  unless mgr.enableAll.validateEnabled matches .ok _ do
    throwError "dormant partial registration was rejected"
  let mgr := {mgr.enableAll with dormantVCs := mgr.dormantVCs.erase alternative}
  unless mgr.validateEnabled matches .error _ do
    throwError "activated alternative without a discharger was accepted"
