module
public import Veil

veil module InvariantRequestOptions
type node
relation r : node → Bool
after_init { r N := false }
action keep { pure () }
invariant [excluded] r N ∨ ¬ r N
set_option veil.smt.trust true
#gen_spec

#guard_msgs (drop info, drop warning) in
#check_action keep

run_cmd do
  let mgr ← Veil.Verifier.readVCManager
  let some vc := mgr.nodes.valuesArray.find? (·.name == `keep_excluded) | throwError "missing VC"
  unless (mgr.provenWitness? vc.uid).any (·.2.hasSorry) do throwError "expected a trusted first attempt"

-- The LSP regression edits just this option and compares the published proof.
#guard_msgs (drop info, drop warning) in
set_option veil.smt.trust false in
#check_invariants

#guard_msgs (drop warning) in
#gen_theorems

end InvariantRequestOptions

run_meta do
  let admitted := (← Lean.collectAxioms ``InvariantRequestOptions.keep_excluded).contains ``sorryAx
  if admitted then throwError "the retry reused the trusted proof"
