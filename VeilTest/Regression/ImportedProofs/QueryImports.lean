module

public import VeilTest.Regression.ImportedProofs.Queries
public import VeilTest.Regression.ImportedProofs.Step
meta import VeilTest.Regression.ImportedProofs.Queries

veil module FlagProofs

-- Independently prepared proof files preserve the same finalized property set.
/-- info: ✅ No liveness violation (checked 2 properties, explored 2 product states) -/
#guard_msgs in
#temporal_check interpreted {}

end FlagProofs
