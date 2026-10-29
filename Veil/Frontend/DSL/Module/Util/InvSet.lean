module

public meta import Veil.Frontend.DSL.Module.Util.Assertions

public meta section

open Lean Elab Command

namespace Veil

def Module.registerInvSet (mod : Module) (group : InvSet) : CommandElabM Module := do
  mod.throwIfSpecAlreadyFinalized
  if mod.invSets.contains group.name then
    throwErrorAt group.userSyntax "invset {group.name} has already been declared"
  return { mod with invSets := mod.invSets.insert group.name group }

private def Module.validateInvSetTargets (mod : Module) (group : InvSet) : CommandElabM Unit := do
  for target in group.targets do
    unless mod.invariants.any (·.name == target) do
      throwErrorAt group.userSyntax "invset {group.name} references unknown invariant clause {target}"

partial def Module.resolveInvSetSupport (mod : Module) (name : Name)
    (seen : Std.HashSet Name := {}) : CommandElabM (Std.HashSet Name) := do
  if seen.contains name then
    throwError "cyclic invset extends chain involving {name}"
  let some group := mod.invSets[name]? | throwError "unknown invset {name}"
  mod.validateInvSetTargets group
  let mut support := group.targets
  for parent in group.parents do
    for target in ← mod.resolveInvSetSupport parent (seen.insert name) do
      support := support.insert target
  return support

def Module.validateInvSets (mod : Module) : CommandElabM Unit := do
  for (_, group) in mod.invSets.toArray.qsort (fun a b => Name.quickLt a.1 b.1) do
    discard <| mod.resolveInvSetSupport group.name

/-- Every isolate's local view has its own invariant targets and the support
of its `with` dependencies. Qualified instance bindings select actual state
locations; this function only selects proof hypotheses. -/
def Module.withInstanceInvSets (mod : Module) : CommandElabM Module := do
  let mut mod := mod
  -- Explicit root groups may name instance properties with their public
  -- qualified spelling, before those properties have been materialized.
  for (name, group) in mod.invSets do
    let targets := group.targets.fold (init := ({} : Std.HashSet Name)) fun acc target =>
      let actual := (mod.instanceNames.find? (·.1 == target)).map (·.2) |>.getD target
      acc.insert actual
    mod := { mod with invSets := mod.invSets.insert name { group with targets } }
  for occurrence in mod.instances do
    if mod.invSets.contains occurrence.name then
      unless mod.invSets[occurrence.name]!.fromInstance do
        throwErrorAt occurrence.userSyntax "isolate {occurrence.name} conflicts with an explicit invset"
      continue
    let targets := mod.instanceNames.foldl (init := ({} : Std.HashSet Name))
      fun acc (qualified, flat) =>
        if occurrence.name.isPrefixOf qualified && mod.invariants.any (·.name == flat) then
          acc.insert flat
        else acc
    mod := { mod with invSets := mod.invSets.insert occurrence.name {
      name := occurrence.name, targets, parents := occurrence.support,
      userSyntax := occurrence.userSyntax, fromInstance := true } }
  mod.validateInvSets
  return mod

/-- All views targeting a clause constrain its support. Intersecting those
sets makes a cached proof valid for every selector, including an isolate's
owner view and a finer explicit invset. No unrestricted fallback is attached. -/
def Module.invSetSupportFor (mod : Module) (target : Name) :
    CommandElabM (Option (Array Name)) := do
  let groups := mod.invSets.toArray.filter (fun (_, group) => group.targets.contains target)
    |>.qsort (fun a b => Name.quickLt a.1 b.1)
  let mut support : Option (Std.HashSet Name) := none
  for (name, _) in groups do
    let allowed ← mod.resolveInvSetSupport name
    support := some <| match support with
      | none => allowed
      | some previous => previous.filter allowed.contains
  return support.map (fun s => s.toArray.qsort Name.quickLt)

/-- Assertion freedom at an external instance entry may use only that
instance's boundary invariant and declared dependency support. -/
def Module.invSetSupportForAction (mod : Module) (actName : Name) :
    CommandElabM (Option (Array Name)) := do
  for occurrence in mod.instances do
    if mod.instanceNames.any (fun (qualified, flat) =>
        occurrence.name.isPrefixOf qualified && flat == actName) then
      return some ((← mod.resolveInvSetSupport occurrence.name).toArray.qsort Name.quickLt)
  return none

end Veil
