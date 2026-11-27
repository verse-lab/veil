module

public import Veil

namespace ImportedOpenCollisionTypes
public abbrev Arg := Bool
end ImportedOpenCollisionTypes

namespace ImportedOpenCollisionOtherTypes
public abbrev Arg := Nat
end ImportedOpenCollisionOtherTypes

open ImportedOpenCollisionTypes

veil module ImportedOpenCollision
set_option veil.deferVCGeneration true
enum shade = { light, dark }
individual flag : Bool
after_init { flag := false }
action keep (x : Arg) { require x; flag := false }
invariant [off] ¬ flag
#gen_spec

-- The action-tag enum is generated inside this section.
section
#guard_msgs (drop info) in
#check_invariants
end
end ImportedOpenCollision

namespace ImportedScopeNotation
scoped notation "ImportedReplayArg" => Bool
end ImportedScopeNotation

open scoped ImportedScopeNotation

veil module ImportedScopedNotation
param limit : ImportedReplayArg
individual flag : Bool
after_init { flag := false }
action keep (x : ImportedReplayArg) { require x; flag := false }
invariant [off] ¬ flag
#gen_spec

end ImportedScopedNotation
