import Lean
import Veil.Frontend.DSL.Module.Syntax
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Action.Elaborators
import Veil.Frontend.DSL.Infra.State
import Veil.Frontend.DSL.Module.VCGen
import Veil.Core.Tools.Verifier.Server

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
  mod.throwIfStateAlreadyDefined
  match stx with
  | `(type $id:ident) => do
      let mod ← mod.declareUninterpretedSort id.getId stx
      localEnv.modifyModule (fun _ => mod)
  | _ => throwUnsupportedSyntax

@[command_elab Veil.stateComponentDeclaration]
def elabStateComponent : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "You cannot declare a state component outside of a Veil module!")
  mod.throwIfStateAlreadyDefined
  let new_mod : Module ← match stx with
  | `($mutab:stateMutability ? $kind:stateComponentKind $name:ident $br:bracketedBinder* : $dom:term) =>
    defineStateComponentFromSyntax mod mutab kind name br dom stx
  | `(command|$mutab:stateMutability ? relation $name:ident $br:bracketedBinder*) => do
    defineStateComponentFromSyntax mod mutab (← `(stateComponentKind|relation)) name br (← `(term|$(mkIdent ``Bool))) stx
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
  mod.throwIfStateAlreadyDefined
  let new_mod : Module ← match stx with
  | `(instantiate $inst:ident : $tp:term) => do
    let param : Parameter := { kind := .moduleTypeclass .userDefined, name := inst.getId, «type» := tp, userSyntax := stx }
    pure { mod with parameters := mod.parameters.push param }
  | _ => throwUnsupportedSyntax
  localEnv.modifyModule (fun _ => new_mod)

 /-- Instruct the linter to not mark state variables as unused in our
  `after_init` and `action` definitions. -/
private def generateIgnoreFn (mod : Module) : CommandElabM Unit := do
  let cmd ← Command.runTermElabM fun _ => do
    let fnIdents ← mod.mutableComponents.mapM (fun sc => `($(quote sc.name)))
    let namesArrStx ← `(#[$[$fnIdents],*])
    let id := mkIdent `id
    let fnStx ← `(fun $id $(mkIdent `stack) _ => $(mkIdent ``Array.contains) ($namesArrStx) ($(mkIdent ``Lean.Syntax.getId) $id) /-&& isActionSyntax stack-/)
    let nm := mkIdent `ignoreStateFields
    let ignoreFnStx ← `(@[$(mkIdent `unused_variables_ignore_fn):ident] def $nm : $(mkIdent ``Lean.Linter.IgnoreFunction) := $fnStx)
    return ignoreFnStx
  elabVeilCommand cmd

/-- Crystallizes the state of the module, i.e. it defines it as a Lean
`structure` definition, if that hasn't already happened. -/
private def Module.ensureStateIsDefined (mod : Module) : CommandElabM Module := do
  if mod.isStateDefined then
    return mod
  let (mod, stateStx) ← mod.declareStateStructure
  let (mod, theoryStx) ← mod.declareTheoryStructure
  elabVeilCommand stateStx
  elabVeilCommand theoryStx
  generateIgnoreFn mod
  return { mod with _stateDefined := true }


/-- Crystallizes the specification of the module, i.e. it finalizes the
set of `procedures` and `assertions`. -/
private def Module.ensureSpecIsFinalized (mod : Module) : CommandElabM Module := do
  if mod.isSpecFinalized then
    return mod
  let mod ← mod.ensureStateIsDefined
  let (assumptionCmd, mod) ← mod.assembleAssumptions
  elabVeilCommand assumptionCmd
  let (invariantCmd, mod) ← mod.assembleInvariants
  elabVeilCommand invariantCmd
  let (safetyCmd, mod) ← mod.assembleSafeties
  elabVeilCommand safetyCmd
  let (labelCmds, mod) ← mod.assembleLabel
  for cmd in labelCmds do
    elabVeilCommand cmd
  let (nextCmd, mod) ← mod.assembleNext
  elabVeilCommand nextCmd
  Verifier.runManager
  mod.generateVCs
  Verifier.startAll
  let _waitUntilDone := (← frontendCh.recv).get
  dbg_trace "({← IO.monoMsNow}) [Elaborator] RECV done notification"
  vcManager.atomically (fun res => do
   let mgr ← res.get
   dbg_trace "({← IO.monoMsNow}) [Elaborator] doneWith: {mgr._doneWith.toArray}"
   trace[veil.debug] "({← IO.monoMsNow}) VCManager:\n{mgr}")
  return { mod with _specFinalized := true }

@[command_elab Veil.genState]
def elabGenState : CommandElab := fun _stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot #gen_state outside of a Veil module!")
  mod.throwIfStateAlreadyDefined ; mod.throwIfSpecAlreadyFinalized
  mod ← mod.ensureStateIsDefined
  localEnv.modifyModule (fun _ => mod)

@[command_elab Veil.initializerDefinition]
def elabInitializer : CommandElab := fun stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot elaborate an initializer outside of a Veil module!")
  mod ← mod.ensureStateIsDefined
  mod.throwIfSpecAlreadyFinalized
  let new_mod ← match stx with
  | `(command|after_init {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.initializer) .none .none l stx
  | _ => throwUnsupportedSyntax
  localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.procedureDefinition]
def elabProcedure : CommandElab := fun stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot elaborate an action outside of a Veil module!")
  mod ← mod.ensureStateIsDefined
  mod.throwIfSpecAlreadyFinalized
  let new_mod ← match stx with
  | `(command|action $nm:ident $br:explicitBinders ? {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.action nm.getId) br .none l stx
  | `(command|procedure $nm:ident $br:explicitBinders ? {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.procedure nm.getId) br .none l stx
  | _ => throwUnsupportedSyntax
  localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.procedureDefinitionWithSpec]
def elabProcedureWithSpec : CommandElab := fun stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot elaborate an action outside of a Veil module!")
  mod ← mod.ensureStateIsDefined
  mod.throwIfSpecAlreadyFinalized
  let new_mod ← match stx with
  | `(command|action $nm:ident $br:explicitBinders ? $spec:doSeq {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.action nm.getId) br spec l stx
  | `(command|procedure $nm:ident $br:explicitBinders ? $spec:doSeq {$l:doSeq}) => mod.defineProcedure (ProcedureInfo.procedure nm.getId) br spec l stx
  | _ => throwUnsupportedSyntax
  localEnv.modifyModule (fun _ => new_mod)

@[command_elab Veil.assertionDeclaration]
def elabAssertion : CommandElab := fun stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot declare an assertion outside of a Veil module!")
  mod ← mod.ensureStateIsDefined
  mod.throwIfSpecAlreadyFinalized
  -- TODO: handle assertion sets correctly
  let assertion : StateAssertion ← match stx with
  | `(command|assumption $name:propertyName ? $prop:term) => mod.mkAssertion .assumption name prop stx
  | `(command|invariant $name:propertyName ? $prop:term) => mod.mkAssertion .invariant name prop stx
  | `(command|safety $name:propertyName ? $prop:term) => mod.mkAssertion .safety name prop stx
  | `(command|trusted invariant $name:propertyName ? $prop:term) => mod.mkAssertion .trustedInvariant name prop stx
  | _ => throwUnsupportedSyntax
  -- Elaborate the assertion in the Lean environment
  let (stx, mod') ← mod.defineAssertion assertion
  elabVeilCommand stx
  localEnv.modifyModule (fun _ => mod')

@[command_elab Veil.genSpec]
def elabGenSpec : CommandElab := fun _stx => do
  let mod ← getCurrentModule (errMsg := "You cannot elaborate a specification outside of a Veil module!")
  let mod ← mod.ensureSpecIsFinalized
  localEnv.modifyModule (fun _ => mod)

end Veil
