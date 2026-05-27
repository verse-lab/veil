import Veil
import VeilTest.ExternalVeilProof.Spec
import VeilTest.ExternalVeilProof.Proof

veil module ExternalVeilProof

#check_invariants

run_cmd do
  let mgr ← Veil.Verifier.vcManager.atomically fun ref => ref.get
  let some vc := mgr.nodes.valuesArray.find? (fun vc => vc.name == `keep_excluded)
    | throwError "expected keep_excluded VC to be registered"
  unless vc.hasInteractiveDischarger do
    throwError "expected imported @[veil] theorem to register as an interactive discharger"
  unless mgr._doneWith[vc.uid]? == some .proven do
    throwError "expected keep_excluded VC to be proven by imported @[veil] theorem"

#gen_theorems

end ExternalVeilProof
