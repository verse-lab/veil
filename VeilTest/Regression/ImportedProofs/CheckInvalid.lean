module

public import VeilTest.Regression.ImportedProofs.Invalid

veil module NodeProofs
#gen_spec

open Lean Elab Command Veil in
run_cmd do
  let results ← Verifier.waitFilteredSync VCMetadata.isInduction
  unless Verifier.hasFailedVCs results do throwError "expected invalid imported proofs to fail"
  let mgr ← Verifier.readVCManager
  for name in [`keep_off, `initializer_off_tr] do
    let some vc := mgr.nodes.valuesArray.find? (·.name == name) | throwError "missing {name}"
    let some proof := vc.dischargers.find? (·.isInteractive) | throwError "missing proof for {name}"
    unless (mgr._dischargerResults[(vc.uid, proof.id.dischargerId)]?).any (· matches .error ..) do
      throwError "invalid proof accepted for {name}"
  let some auto := mgr.nodes.valuesArray.find? (·.name == `keep_doesNotThrow) | throwError "missing VC"
  unless auto.dischargers.all (!·.isInteractive) && (mgr.provenWitness? auto.uid).isSome do
    throwError "expected automatic verification for the unregistered VC"

end NodeProofs
