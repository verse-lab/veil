module

public import VeilTest.Regression.ImportedProofs.ScopeReplaySpec

open ImportedOpenCollisionOtherTypes

veil module ImportedOpenCollision
-- The action parameter should still resolve to ImportedOpenCollisionTypes.Arg.
#check_invariants
end ImportedOpenCollision
