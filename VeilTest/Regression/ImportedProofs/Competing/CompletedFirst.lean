module

public import VeilTest.Regression.ImportedProofs.Competing.Completed
public import VeilTest.Regression.ImportedProofs.Competing.Unfinished

set_option veil.smt.trust false

veil module NodeProofs
run_meta do
  if (← Lean.collectAxioms ``keep_off).contains ``sorryAx then
    throwError "expected Lean to select the completed declaration"
#check_invariants
end NodeProofs

veil module FlagProofs
#check_invariants
run_cmd checkCompetingFlagProofs true
end FlagProofs
