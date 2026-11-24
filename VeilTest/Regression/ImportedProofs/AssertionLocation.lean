module

public import VeilTest.Regression.ImportedProofs.AssertionLocationSpec
meta import VeilTest.Regression.ImportedProofs.AssertionLocationSpec

veil module ImportedAssertionLocation
set_option veil.violationIsError false
#guard_msgs (drop info) in
#model_check interpreted {}
run_cmd checkAssertionLocation
end ImportedAssertionLocation
