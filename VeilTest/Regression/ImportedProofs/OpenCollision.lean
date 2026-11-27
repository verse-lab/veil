module

public import VeilTest.Regression.ImportedProofs.ScopeReplaySpec

-- Even the fully qualified spelling from the spec has a competing interpretation.
namespace ImportedOpenCollision.ImportedOpenCollisionTypes
public abbrev Arg := Nat
end ImportedOpenCollision.ImportedOpenCollisionTypes

open ImportedOpenCollisionOtherTypes

veil module ImportedOpenCollision
-- The checking file keeps its own type for ordinary Lean declarations.
example (x : Arg) : Nat := x
-- Veil enum projections remain available as they are in the specification.
example {shade : Type} [shade_EnumClass shade] : shade := light
example {α : Type} [ActionTag_EnumClass α] (x : α) : x = ActionTag_EnumClass.keep := complete x
-- The action parameter should still resolve to ImportedOpenCollisionTypes.Arg.
#check_invariants
end ImportedOpenCollision
