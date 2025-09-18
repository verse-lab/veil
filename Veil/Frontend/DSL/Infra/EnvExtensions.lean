import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Infra.Assertions
import Veil.Frontend.DSL.Infra.Metadata
import Veil.Core.Tools.Verifier.Manager
-- Not needed for compilation, but re-exported
import Veil.Util.EnvExtensions
open Lean

namespace Veil

structure LocalEnvironment where
  currentModule : Option Module
deriving Inhabited

structure VCManagerEnvironment where
  mgr : VCManager VCMetadata VeilResult
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

initialize vcManagerEnv : PersistentEnvExtension Unit VCManagerEnvironment VCManagerEnvironment ←
  registerPersistentEnvExtension {
    mkInitial := return { mgr := ← VCManager.new }
    addImportedFn := fun _ => return { mgr := ← VCManager.new }
    addEntryFn := fun _old new => new
    exportEntriesFnEx := fun _ _ _ => #[]
    asyncMode := .mainOnly
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

def getVCManager [Monad m] [MonadEnv m] : m (VCManager VCMetadata VeilResult) := return (← vcManagerEnv.get).mgr

def setVCManager [Monad m] [MonadEnv m] (mgr : VCManager VCMetadata VeilResult) : m Unit := do
  vcManagerEnv.modify (fun _ => { mgr := mgr })

def mkNewAssertion [Monad m] [MonadEnv m] [MonadError m] (proc : Name) (stx : Syntax) : m AssertionId := do
  let mod ← getCurrentModule (errMsg := "Cannot have a Veil assertion outside of a module")
  let gctx ← globalEnv.get
  let actx := gctx.assertions
  let assert := { id := actx.maxId, ctx := { module := mod.name, procedure := proc, stx := stx } }
  let actx' := { actx with maxId := actx.maxId + 1, find := actx.find.insert actx.maxId assert }
  globalEnv.modify (fun gctx => { gctx with assertions := actx' })
  return actx.maxId

end Veil
