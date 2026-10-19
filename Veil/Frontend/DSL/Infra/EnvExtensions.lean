module

public meta import Lean
public meta import Veil.Base
public meta import Veil.Frontend.DSL.Module.Representation
public meta import Veil.Frontend.DSL.Infra.Assertions
-- Not needed for compilation, but re-exported
public meta import Veil.Util.EnvExtensions

public meta section
open Lean

namespace Veil

structure LocalEnvironment where
  currentModule : Option Module
deriving Inhabited

structure GlobalEnvironment where
  modules : Std.HashMap Name Module
  assertions : AssertionEnvironment
deriving Inhabited

def GlobalEnvironment.containsModule (genv : GlobalEnvironment) (name : Name) : Bool :=
  genv.modules.contains name

initialize localEnv : SimpleScopedEnvExtension LocalEnvironment LocalEnvironment ←
  registerSimpleScopedEnvExtension {
    initial := { currentModule := none}
    addEntry := fun _ s' => s'
  }

initialize globalEnv : SimpleScopedEnvExtension GlobalEnvironment GlobalEnvironment ←
  registerSimpleScopedEnvExtension {
    initial := default
    addEntry := fun _ s' => s'
  }

def localEnv.modifyModule [Monad m] [MonadEnv m] (f : Option Module → Module) : m Unit :=
  localEnv.modify (fun s => { s with currentModule := f s.currentModule })

def getCurrentModule [Monad m] [MonadEnv m] [MonadError m] (errMsg : MessageData := m!"getCurrentModule called outside of a module") : m Module := do
  if let some mod := (← localEnv.get).currentModule then
    return mod
  else
    throwError errMsg

/-- The role of a binder of `Module.instantiationTemplate`. -/
inductive InstantiationBinder where
  /-- A parameter set by the field of `Instantiation` of this name. -/
  | field (name : Name)
  /-- An `instantiate` constraint. -/
  | constraint
  /-- An auto-generated assumption about a sort, which the constraints may mention. -/
  | sortAssumption
deriving Inhabited

/-- Where a declaration of a module is: its file, as `Lean.Elab.getFileName` gives it where the module
is declared, and its position there, as in LSP (0-based line, UTF-16 character) -/
structure DeclSource where
  /-- The name that model checking results give it -/
  name : String
  file : String
  line : Nat
  character : Nat
deriving Inhabited, Lean.ToJson

/-- What checking a module takes, without the module itself. `#gen_executable` records it, so
that `#model_check_build` can build its model checker in the files importing the one declaring it. -/
structure ExecutableModule where
  name : Name
  /-- The fields of `Instantiation` that set the sorts and parameters, in the order that the
  definitions of the module take them -/
  instantiationFields : Array Name
  /-- `Module.instantiationTemplate`, elaborated where the module is declared. It is missing if
  it was not closed. -/
  instantiationTemplate : Option (Expr × Array InstantiationBinder)
  assumptions : Array Name
  /-- The invariants and safety properties -/
  invariants : Array Name
  terminations : Array Name
  stateConstraints : Array Name
  /-- The labels of the actions without their arguments, e.g. `Paxos.Label.send`, as the model
  checker names the actions it takes, e.g. `Paxos.Label.send 1 2` -/
  actionLabels : Array String
  /-- Where the actions are, by the names that traces give them, e.g. `send` and `after_init` -/
  actionSources : Array DeclSource
  /-- Where the properties are, e.g. the invariants, by the names that violations give them -/
  propertySources : Array DeclSource
deriving Inhabited

initialize executableModuleExt :
    SimplePersistentEnvExtension ExecutableModule (Std.HashMap Name ExecutableModule) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s em => s.insert em.name em
    addImportedFn := fun ems =>
      ems.foldl (init := {}) fun s ems => ems.foldl (init := s) fun s em => s.insert em.name em
  }

/-- What checking module `name` takes, if its executable definitions were generated in this file
or in an imported one. -/
def getExecutableModule? [Monad m] [MonadEnv m] (name : Name) : m (Option ExecutableModule) :=
  return (executableModuleExt.getState (← getEnv))[name]?

def mkNewAssertion [Monad m] [MonadEnv m] [MonadError m] (proc : Name) (stx : Syntax) : m AssertionId := do
  let mod ← getCurrentModule (errMsg := "Cannot have a Veil assertion outside of a module")
  let gctx ← globalEnv.get
  let actx := gctx.assertions
  let assert := { id := actx.maxId, ctx := { module := mod.name, procedure := proc, stx := stx } }
  let actx' := { actx with maxId := actx.maxId + 1, find := actx.find.insert actx.maxId assert }
  globalEnv.modify (fun gctx => { gctx with assertions := actx' })
  return actx.maxId

section DevelopingTools

open Lean Meta Elab Command in
elab "veil_set_option " o:ident v:term : command => do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  let v ← liftTermElabM <| Term.elabTerm v (mkConst ``Bool)
  let b := if v == mkConst ``Bool.true then true else false
  match o.getId with
  | `useLocalRPropTC => localEnv.modifyModule (fun _ => { mod with _useLocalRPropTC := b })
  | _ => throwError s!"Unsupported option {o}"

end DevelopingTools

end Veil
