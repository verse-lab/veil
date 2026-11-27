module

public import VeilTest.Regression.ImportedProofs.ThroughHelper

set_option veil.smt.trust false
veil module NodeProofs
/-- interactive proof `NodeProofs.keep_off` depends on `sorry` -/
#guard_msgs (error, drop info, substring := true) in
#check_action keep
end NodeProofs
