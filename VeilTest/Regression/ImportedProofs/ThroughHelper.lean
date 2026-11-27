module

public import VeilTest.Regression.ImportedProofs.Spec

set_option veil.smt.trust false
veil module NodeProofs

/-- warning: declaration uses `sorry` -/
#guard_msgs in
private theorem unfinishedHelper : False := by sorry

prove_veil_invariant_goal keep off using wp by
  exact unfinishedHelper.elim

/-- interactive proof `NodeProofs.keep_off` depends on `sorry` -/
#guard_msgs (error, drop info, substring := true) in
#check_action keep
end NodeProofs
