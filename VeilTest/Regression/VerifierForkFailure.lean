import VeilTest.Regression.VerifierCancellationSupport

open Lean Elab Command Veil Veil.Verifier

run_cmd do
  for hasFactory in [false, true] do
    runManager
    let calls ← IO.mkRef 0
    withVCManager fun ref => do
      let data : VCData VCMetadata := {name := `forkFailure, params := #[], statement := ← `(term| True), metadata := default}
      let (mgr, id) := (← ref.get).addVC data {}
      let term ← `(term| by trivial)
      let mgr ← mgr.mkAddDischarger id fun statement id ch => do
        let call ← calls.modifyGet fun n => (n, n + 1)
        if call > 0 then throwError "deliberate factory replay failure"
        Discharger.fromTermWith term statement id ch fun _ outcome time =>
          match outcome with
          | .inl witness => pure (.proven witness none time)
          | .inr ex => pure (.error #[(ex, toJson "test failed")] time)
      ref.set (if hasFactory then mgr else {mgr with factories := {}})
    let old ← getSession
    let result ← waitFilteredSync (fun _ => true)
    unless result.totalSolved == 1 do throwError "original attempt failed"
    withReader (fun ctx => {ctx with fileMap := FileMap.ofString (ctx.fileMap.source ++ "\n-- fork")}) do
      let fresh ← getSession
      let result ← waitFilteredSync (fun _ => true)
      unless result.totalSolved == 0 && (← fresh.snapshot)._doneWith[0]? == some .error do
        throwError "failed factory replay did not produce a terminal diagnostic"
      unless (← old.snapshot)._doneWith[0]? == some .proven do
        throwError "failed factory replay damaged the original session"
