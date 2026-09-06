import Veil

open Lean Elab Command Veil Veil.Verifier

private def addGenerationVC (name : Name) (term : Term) : CommandElabM Unit :=
  withVCManager fun ref => do
    let data : VCData VCMetadata := {name, params := #[], statement := ← `(term| True), metadata := default}
    let (mgr, id) := (← ref.get).addVC data {}
    ref.set (← mgr.mkAddDischarger id fun statement id ch =>
      Discharger.fromTermWith term statement id ch fun _ result time =>
        match result with
        | .inl witness => pure (.proven witness none time)
        | .inr ex => pure (.error #[(ex, toJson "automatic proof failed")] time))

run_cmd do
  -- Reusing an unchanged #gen_spec snapshot must recreate one-shot resources,
  -- rather than reusing cancelled tasks/promises from the old document.
  runManager
  addGenerationVC `restart (← `(term| by trivial))
  let old ← getSession
  let cachedEnv ← getEnv
  let mgr ← old.snapshot
  let some d := mgr.nodes[0]!.dischargers[0]? | throwError "missing discharger"
  d.cancelTk.set
  let oldResult ← waitFilteredSync (fun _ => true)
  unless oldResult.totalSolved == 0 do throwError "cancelled task unexpectedly proved VC"
  withReader (fun ctx => {ctx with fileMap := FileMap.ofString (ctx.fileMap.source ++ "\n-- edited")}) do
    let fresh ← getSession
    let freshMgr ← fresh.snapshot
    unless freshMgr._managerId != mgr._managerId do throwError "reused old document generation"
    let some freshD := freshMgr.nodes[0]!.dischargers[0]? | throwError "missing fresh discharger"
    unless !(← freshD.cancelTk.isSet) do throwError "reused cancelled token"
    let result ← waitFilteredSync (fun _ => true)
    unless result.totalSolved == 1 do throwError "fresh generation could not rerun cancelled work"
  -- Undoing an edit can reuse the original command snapshot and source text.
  -- Its superseded mutable session must still be replaced.
  setEnv cachedEnv
  let restored ← getSession
  unless (← restored.snapshot)._managerId != mgr._managerId do
    throwError "undo revived a superseded manager"
  let result ← waitFilteredSync (fun _ => true)
  unless result.totalSolved == 1 do throwError "undo could not restart verification"

run_cmd do
  runManager
  addGenerationVC `sourceProof (← `(term| by fail))
  let beforeProof ← getEnv
  let old ← getSession
  let declareProof := elabCommand (← `(command| @[veil] theorem $(mkIdent `sourceProof) : True := by trivial))
  let lateRegistration ← Command.wrapAsync (fun () => declareProof) none
  declareProof
  unless (← old.snapshot)._doneWith[0]? == some .proven do throwError "manual proof was not registered"
  -- Simulate deleting the theorem after an unchanged #gen_spec: the immutable
  -- command environment no longer contains it, but the old manager did.
  setEnv beforeProof
  withReader (fun ctx => {ctx with fileMap := FileMap.ofString (ctx.fileMap.source ++ "\n-- proof removed")}) do
    let fresh ← getSession
    unless !(← fresh.snapshot).nodes[0]!.hasInteractiveDischarger do
      throwError "deleted interactive proof survived in cached mutable state"
    let result ← waitFilteredSync (fun _ => true)
    unless result.totalSolved == 0 do throwError "deleted proof was reported successful"
    -- A delayed attribute callback from the old command retains its old
    -- session and must not replace the new generation's automatic failure.
    let _ ← (lateRegistration ()).toBaseIO
    unless (← fresh.snapshot)._doneWith[0]? == some .error do
      throwError "old attribute callback overwrote the new document's result"
