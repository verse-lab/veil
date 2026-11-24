module

public import VeilTest.Regression.ImportedProofs.ProofChain.KeepDoesNotThrow

namespace ImportedProofChain

open Lean Elab Command in
public meta def checkProofs (names : List Name) : CommandElabM Unit := do
  let mgr ← Veil.Verifier.readVCManager
  let interactiveVCs := mgr.nodes.valuesArray.filter (·.hasInteractiveDischarger)
  unless interactiveVCs.size == names.length do
    throwError "expected {names.length} VCs with interactive proofs, found {interactiveVCs.size}"
  for name in names do
    let some vc := interactiveVCs.find? (·.name == name)
      | throwError "missing interactive proof for {name}"
    let #[d] := vc.effectiveDischargers
      | throwError "expected exactly one effective discharger for {name}"
    unless d.isInteractive &&
        (mgr._dischargerResults[(vc.uid, d.id.dischargerId)]?).any (·.isSuccessful) do
      throwError "interactive proof failed for {name}"

end ImportedProofChain

veil module NodeProofs
-- The last proof file sees all three previous proofs through its single import.
run_cmd ImportedProofChain.checkProofs [
  `initializer_doesNotThrow, `initializer_off_tr, `keep_doesNotThrow]

prove_veil_invariant_goal keep off using wp by
  grind

#check_invariants
run_cmd ImportedProofChain.checkProofs [
  `initializer_doesNotThrow, `initializer_off_tr, `keep_doesNotThrow, `keep_off]
end NodeProofs
