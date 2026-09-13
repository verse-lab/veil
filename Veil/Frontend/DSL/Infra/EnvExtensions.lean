import Lean
import Veil.Base
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Infra.Assertions
import Veil.Frontend.DSL.Infra.VerificationSupport
-- Not needed for compilation, but re-exported
import Veil.Util.EnvExtensions
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

section ModelCheckCompilationMode

/-! ## Model Check Compilation Mode

This legacy option supports explicitly re-elaborating a source file to export
`modelCheckerResult`. Native `#model_check` now emits C directly from the current
environment and does not enable this option. When enabled, it is used to:
1. Skip verification-only operations (like `doesNotThrow` error reporting)
2. Skip verification commands (`#check_invariants`, `sat trace`, etc.)
3. Prevent `logError` calls from failing the build
-/

/-- Check if we're in model checking compilation mode. -/
def isModelCheckCompileMode [Monad m] [MonadOptions m] : m Bool := do
  return veil.__modelCheckCompileMode.get (← getOptions)

/-- Log an error, but only if not in model check compilation mode.
    In compilation mode, errors would cause lake build to fail. -/
def veilLogError [Monad m] [MonadOptions m] [AddMessageContext m] [MonadLog m]
    (msg : MessageData) : m Unit := do
  unless ← isModelCheckCompileMode do
    logError msg

/-- Log an error at a specific syntax location, but only if not in compilation mode. -/
def veilLogErrorAt [Monad m] [MonadOptions m] [AddMessageContext m] [MonadLog m]
    (stx : Syntax) (msg : MessageData) : m Unit := do
  unless ← isModelCheckCompileMode do
    logErrorAt stx msg

end ModelCheckCompilationMode

end Veil
