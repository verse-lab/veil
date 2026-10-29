module

public meta import Veil.Frontend.DSL.Module.Elaborators.Core
public meta import Veil.Frontend.DSL.Module.Util.InvSet

public meta section

open Lean Elab Command

namespace Veil

private def registerInvSet (name : Name) (parents : Array Name)
    (targets : Std.HashSet Name) (stx : Syntax) : CommandElabM Unit := do
  let mod ← getCurrentModule
  let mod ← mod.registerInvSet { name, parents, targets, userSyntax := stx }
  localEnv.modifyModule (fun _ => mod)

private def templateInvariantName? (stx : Syntax) : Option Name :=
  match stx with
  | `(command| invariant [$id:ident] $_)
  | `(command| safety [$id:ident] $_)
  | `(command| trusted invariant [$id:ident] $_) => some id.getId
  | _ => none

@[command_elab invsetBlock]
def elabInvSetBlock : CommandElab := fun stx => do
  let elaborate (name : Ident) (parents : Array Ident)
      (commands : Array (TSyntax `command)) : CommandElabM Unit := do
    let before ← getCurrentModule
    before.throwIfSpecAlreadyFinalized
    if before.invSets.contains name.getId then
      throwErrorAt name "invset {name} has already been declared"
    for command in commands do elabCommand command
    let after ← getCurrentModule
    let mut targets : Std.HashSet Name := {}
    if after.isReferenceTemplate then
      for command in after.templateCommands[before.templateCommands.size:] do
        if command.isOfKind ``assertionDeclaration &&
            (command[0].isOfKind ``invariantKind || command[0].isOfKind ``safetyKind ||
              command[0].isOfKind ``trustedInvariantKind) then
          if let some target := templateInvariantName? command then
            targets := targets.insert target
          else
            throwErrorAt command "invariants in a module-reference template invset need explicit names"
    else
      for assertion in after.invariants do
        unless before.invariants.any (·.name == assertion.name) do
          targets := targets.insert assertion.name
    registerInvSet name.getId (parents.map (·.getId)) targets stx
  match stx with
  | `(command| invset $name:ident extends $parents:ident* { $commands:command* }) =>
      elaborate name parents commands
  | `(command| invset $name:ident { $commands:command* }) =>
      elaborate name #[] commands
  | _ => throwUnsupportedSyntax

@[command_elab invsetExplicit]
def elabInvSetExplicit : CommandElab := fun stx => do
  match stx with
  | `(command| invset $name:ident extends $parents:ident* := { $targets:ident,* }) =>
      registerInvSet name.getId (parents.map (·.getId))
        (Std.HashSet.ofArray (targets.getElems.map (·.getId))) stx
  | `(command| invset $name:ident := { $targets:ident,* }) =>
      registerInvSet name.getId #[]
        (Std.HashSet.ofArray (targets.getElems.map (·.getId))) stx
  | _ => throwUnsupportedSyntax

end Veil
