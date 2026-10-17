module
meta import Veil.Core.Tools.Verifier.TheoremDischarger
meta import VeilTest.Regression.VerifierOwnedTheoremSupport

open Lean Elab Command Veil Veil.Verifier
meta section

run_cmd do
  runManager
  withVCManager fun ref => do
    let (mgr, _) := (← ref.get).addVC {
      name := `same, params := #[], statement := ← `(True), metadata := default } {}
    ref.set mgr
  environments.modify (·.push (← getEnv))
  owners.modify (·.push (← getVCManagerOwner))
  runManager
  withVCManager fun ref => do
    let (mgr, _) := (← ref.get).addVC {
      name := `same, params := #[], statement := ← `(False), metadata := default } {}
    ref.set mgr
  owners.modify (·.push (← getVCManagerOwner))
  -- Restore the command environment captured by A before B was created.
  let some env := (← environments.get)[0]? | throwError "missing A environment"
  setEnv env

@[veil] public theorem same : True := True.intro

run_cmd do
  let some a := (← owners.get)[0]? | throwError "missing A"
  let some b := (← owners.get)[1]? | throwError "missing B"
  let amgr ← a.manager.atomically fun ref => ref.get
  let bmgr ← b.manager.atomically fun ref => ref.get
  unless amgr.provenWitness? 0 |>.isSome do throwError "A theorem did not register in A"
  unless bmgr._doneWith.isEmpty do throwError "A theorem registered in B"
  -- The generated-theorem reader must also use restored A's owner.
  withVCManager fun ref => do
    let (mgr, id) := (← ref.get).addVC {
      name := `generated, params := #[], statement := ← `(True), metadata := default } {}
    let nodes := mgr.nodes.modify id fun vc => { vc with successful := some 0 }
    let mgr := { mgr with
      nodes := nodes
      _dischargerResults := mgr._dischargerResults.insert (id, 0) (.proven (some (mkConst ``True.intro)) none 0) }
    ref.set mgr
  addProvenTheoremsInDependencyOrder (fun _ => true)
  unless (← getEnv).contains `generated do throwError "A generation read another owner"
  liftIO <| IO.println "owned AttrM registration and generated theorem lookup: PASS"
