module

public import VeilTest.Regression.ImportedProofs.ScopeReplaySpec

-- Even the fully qualified spelling from the spec has a competing interpretation.
namespace ImportedOpenCollision.ImportedOpenCollisionTypes
public abbrev Arg := Nat
end ImportedOpenCollision.ImportedOpenCollisionTypes

open ImportedOpenCollisionOtherTypes

veil module ImportedOpenCollision
-- The action parameter should still resolve to ImportedOpenCollisionTypes.Arg.
#check_invariants
end ImportedOpenCollision
