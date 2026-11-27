module

public import VeilTest.Regression.ImportedProofs.Competing.Unfinished
public import VeilTest.Regression.ImportedProofs.Competing.Completed

set_option veil.smt.trust false

veil module NodeProofs
run_meta do
  unless (← Lean.collectAxioms ``keep_off).contains ``sorryAx do
    throwError "expected Lean to select the unfinished declaration"

/-- interactive proof `NodeProofs.keep_off` depends on `sorry` -/
#guard_msgs (error, drop info, substring := true) in
#check_invariants
end NodeProofs

veil module FlagProofs
#check_invariants
run_cmd checkCompetingFlagProofs false
end FlagProofs
