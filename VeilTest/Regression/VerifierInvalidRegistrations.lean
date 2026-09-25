import Veil.Core.Tools.Verifier.Server

open Lean Elab Command Veil Veil.Verifier

run_cmd do
  let ch ← Std.Channel.new
  let mgr : VCManager Unit Unit ← VCManager.new ch
  let data : VCData Unit := {name := `test, params := #[], statement := ← `(term| True), metadata := ()}
  let (missing, _) := mgr.addVC data ((Std.HashSet.emptyWithCapacity).insert 100)
  unless missing.validateRegistrations matches .error _ do throwError "missing dependency accepted"
  let (cyclic, _) := mgr.addVC data ((Std.HashSet.emptyWithCapacity).insert 0)
  unless cyclic.validateRegistrations matches .error _ do throwError "cyclic dependency accepted"
  let (forward, _) := mgr.addVC data ((Std.HashSet.emptyWithCapacity).insert 1)
  let (forward, _) := forward.addVC data {}
  unless forward.validateRegistrations matches .error _ do throwError "forward dependency accepted"
  let (mgr, parent) := mgr.addVC data {}
  let (mgr, _) := mgr.addVC data ((Std.HashSet.emptyWithCapacity).insert parent)
  unless mgr.validateRegistrations matches .ok _ do throwError "valid dependencies rejected"

run_cmd do
  runManager
  let mut rejected := false
  try
    withVCManager fun ref => do
      let data : VCData VCMetadata := {name := `invalid, params := #[], statement := ← `(term| True), metadata := default}
      ref.set ((← ref.get).addVC data ((Std.HashSet.emptyWithCapacity).insert 100)).1
    startAll
  catch ex =>
    rejected := (← ex.toMessageData.toString).contains "missing VC"
  unless rejected do throwError "malformed registration did not produce a frontend diagnostic"
