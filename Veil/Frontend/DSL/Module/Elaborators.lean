import Lean
import Veil.Frontend.DSL.Module.Syntax
import Veil.Frontend.DSL.StateExtensions
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Action.Elaborators
import Veil.Frontend.DSL.State

open Lean Parser Elab Command

namespace Veil

@[command_elab Veil.moduleDeclaration]
def elabModuleDeclaration : CommandElab := fun stx => do
  match stx with
  | `(veil module $modName:ident) => do
    let genv ← globalEnv.get
    let name := modName.getId
    let lenv ← localEnv.get
    if let some mod := lenv.currentModule then
      throwError s!"Module {mod.name} is already open, but you are now trying to open module {name}. Nested modules are not supported!"
    elabVeilCommand $ ← `(namespace $modName)
    if genv.containsModule name then
      logInfo "Module {name} has been previously defined. Importing it here."
      let mod := genv.modules[name]!
      localEnv.modifyModule (fun _ => mod)
    else
      let mod ← Module.freshWithName name
      localEnv.modifyModule (fun _ => mod)
  | _ => throwUnsupportedSyntax

@[command_elab Veil.typeDeclaration]
def elabTypeDeclaration : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare a type outside of a Veil module!")
  match stx with
  | `(type $id:ident) => do
      let mod ← mod.declareUninterpretedSort id.getId (← getRef)
      localEnv.modifyModule (fun _ => mod)
  | _ => throwUnsupportedSyntax

@[command_elab Veil.declareStateComponent]
def elabStateComponent : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare a state component outside of a Veil module!")
  let new_mod : Module ← match stx with
  | `($mutab:stateMutability ? $kind:stateComponentKind $name:ident $br:bracketedBinder* : $dom:term) =>
    defineStateComponentFromSyntax mod mutab kind name br dom (← getRef)
  | `(command|$mutab:stateMutability ? relation $name:ident $br:bracketedBinder*) => do
    defineStateComponentFromSyntax mod mutab (← `(stateComponentKind|relation)) name br (← `(term|Prop)) (← getRef)
  | _ => throwUnsupportedSyntax
  localEnv.modifyModule (fun _ => new_mod)
where
  defineStateComponentFromSyntax
  (mod : Module) (mutability : Option (TSyntax `stateMutability)) (kind : TSyntax `stateComponentKind)
  (name : Ident) (br : TSyntaxArray ``Term.bracketedBinder) (dom : Term) (userStx : Syntax) : CommandElabM Module := do
    let mutability := Mutability.fromStx mutability
    let kind := StateComponentKind.fromStx kind
    let sctype ← (
      if br.isEmpty then
        return StateComponentType.simple (← `(Command.structSimpleBinder|$name:ident : $dom))
      else
        return StateComponentType.complex br dom)
    let sc : StateComponent := { mutability := mutability, kind := kind, name := name.getId, «type» := sctype, userSyntax := userStx }
    Module.declareStateComponent mod sc

@[command_elab Veil.instanceDeclaration]
def elabInstantiate : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot instantiate a typeclass outside of a Veil module!")
  let new_mod : Module ← match stx with
  | `(instantiate $inst:ident : $tp:term) => do
    -- let tp := StateComponentType.simple (← `(Command.structSimpleBinder|$inst:ident : $tp))
    -- let sc : StateComponent := { mutability := Mutability.immutable, kind := StateComponentKind.individual, name := inst.getId, «type» := tp, userSyntax := stx }
    -- Module.declareStateComponent mod sc
    let param : Parameter := { kind := .typeclass .alwaysRequired, name := inst.getId, «type» := tp, userSyntax := stx }
    pure { mod with parameters := mod.parameters.push param }
  | _ => throwUnsupportedSyntax
  localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.genState]
def elabGenState : CommandElab := fun _stx => do
  let mod ← getCurrentModule (errMsg := "You cannot #gen_state outside of a Veil module!")
  let (mod, stateStx) ← mod.declareStateStructure
  let (mod, theoryStx) ← mod.declareTheoryStructure
  elabVeilCommand stateStx
  elabVeilCommand theoryStx
  localEnv.modifyModule (fun _ => mod)
  generateIgnoreFn mod
where
  /-- Instruct the linter to not mark state variables as unused in our
  `after_init` and `action` definitions. -/
  generateIgnoreFn (mod : Module) : CommandElabM Unit := do
    let cmd ← Command.runTermElabM fun _ => do
      let fnIdents ← mod.mutableComponents.mapM (fun sc => `($(quote sc.name)))
      let namesArrStx ← `(#[$[$fnIdents],*])
      let id := mkIdent `id
      let fnStx ← `(fun $id $(mkIdent `stack) _ => $(mkIdent ``Array.contains) ($namesArrStx) ($(mkIdent ``Lean.Syntax.getId) $id) /-&& isActionSyntax stack-/)
      let nm := mkIdent `ignoreStateFields
      let ignoreFnStx ← `(@[$(mkIdent `unused_variables_ignore_fn):ident] def $nm : $(mkIdent ``Lean.Linter.IgnoreFunction) := $fnStx)
      return ignoreFnStx
    elabVeilCommand cmd

elab_rules : command
  | `(command|action $nm:ident $br:explicitBinders ? = {$l:doSeq}) => elabAction nm br none l
--   | `(command|procedure $nm:ident $br:explicitBinders ? = {$l:doSeq}) => elabProcedure nm br none l
--   | `(command|action $nm:ident $br:explicitBinders ? = $spec:doSeq {$l:doSeq}) => elabAction nm br spec l
--   | `(command|procedure $nm:ident $br:explicitBinders ? = $spec:doSeq {$l:doSeq}) => elabProcedure nm br spec l

end Veil
