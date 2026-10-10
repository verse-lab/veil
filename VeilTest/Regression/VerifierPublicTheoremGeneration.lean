module

public import Veil

open Lean Elab Command Veil Veil.Verifier

run_cmd do
  runManager
  withVCManager fun ref => do
    let data : VCData VCMetadata := {
      name := `publicProof, params := #[], statement := ← `(term| True), metadata := default }
    let (mgr, id) := (← ref.get).addVC data {}
    let term ← `(term| by fail)
    ref.set (← mgr.mkAddDischarger id fun statement id ch =>
      Discharger.fromTermWith term statement id ch fun _ result time =>
        match result with
        | .inl witness => pure (.proven witness none time)
        | .inr ex => pure (.error #[(ex, toJson "automatic proof failed")] time))

@[veil] public theorem publicProof : True := by trivial

run_cmd do
  let old ← getSession
  let oldMgr ← old.snapshot
  unless oldMgr._doneWith[0]? == some .proven do
    throwError "public interactive theorem was not registered"
  withReader (fun ctx => {ctx with fileMap := FileMap.ofString (ctx.fileMap.source ++ "\n-- edited")}) do
    let fresh ← getSession
    let mgr ← fresh.snapshot
    unless mgr._managerId != oldMgr._managerId do throwError "document generation was not forked"
    unless mgr.nodes[0]!.hasInteractiveDischarger && mgr._doneWith[0]? == some .proven do
      throwError "unchanged public proof did not survive document generation replay"
    let results ← waitFilteredSync (fun _ => true)
    unless results.totalSolved == 1 do throwError "public proof fell back to the failing automatic attempt"
