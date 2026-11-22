module

public import VeilTest.Regression.ImportedProofs.Step
public import VeilTest.Regression.ImportedProofs.Init

open Lean Elab Command in
private meta def checkImportedProofs : CommandElabM Unit := do
  let mgr ← Veil.Verifier.readVCManager
  -- Two exception VCs plus both styles of each invariant VC.
  unless mgr.nodes.size == 6 do throwError "expected six VCs, found {mgr.nodes.size}"
  for name in [`keep_off, `initializer_off_tr] do
    let some vc := mgr.nodes.valuesArray.find? (·.name == name)
      | throwError "missing {name}"
    let #[d] := vc.dischargers.filter (·.isInteractive)
      | throwError "expected exactly one imported proof for {name}"
    unless vc.effectiveDischargers.all (·.isInteractive) &&
        (mgr._dischargerResults[(vc.uid, d.id.dischargerId)]?).any (·.isSuccessful) do
      throwError "imported proof failed for {name}"

veil module NodeProofs
-- Definitions generated at the defining file's end M are available immediately.
example := @keep.ext.wp
run_cmd checkImportedProofs
#gen_executable
#guard_msgs (drop info) in
#check_action keep
run_cmd do
  let mgr ← Veil.Verifier.readVCManager
  if mgr.nodes.valuesArray.any (fun vc =>
      vc.name == `initializer_off && mgr.enabledVCs.contains vc.uid) then
    throwError "checking keep started the initializer"
#check_invariants
run_cmd checkImportedProofs
end NodeProofs

veil module FlagProofs
#check_invariants
run_cmd checkImportedProofs
-- First extraction in an importing file still points traces at the spec.
#gen_executable
run_cmd do
  let some em ← Veil.getExecutableModule? `FlagProofs | throwError "missing executable"
  unless em.actionSources.any (fun s => s.name == "keep" && s.file.endsWith "Spec.lean") do
    throwError "imported extraction lost the original action location"
end FlagProofs
