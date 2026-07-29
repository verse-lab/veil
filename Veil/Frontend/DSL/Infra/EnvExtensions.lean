import Lean
import Veil.Base
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
  mgr : VCManager VCMetadata SmtResult
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

/-- A channel for communicating with the VCManager. -/
initialize vcManagerCh : Std.Channel (ManagerNotification VCMetadata SmtResult) ← Std.Channel.new

/-- Info for tasks that need to be registered with `logSnapshotTask` on the main thread.
    The manager thread sends task info here, and the frontend task (runFilteredAsync)
    picks them up and registers them. -/
structure TaskRegistrationInfo where
  task : SnapshotTreeTask
  cancelTk : IO.CancelToken

/-- Channel for tasks that need snapshot registration.
    Direction: Manager → Frontend (runFilteredAsync/waitFilteredSync) -/
initialize taskRegistrationCh : Std.Channel TaskRegistrationInfo ← Std.Channel.new

/-- Prompt the frontend to read the VCManager, e.g. to print the VCs. We use a
`Condvar` instead of `Channel` because channels on the frontend thread (which
is cancellable) are subject to potential race conditions. For instance,
multiple `#gen_spec`s can be running in parallel, and one of them will "eat"
the notification from a channel, which causes the other to wait forever. With a
`Condvar`, we can `notifyAll` and check the predicate/condition holds. -/
initialize frontendNotification : Std.Condvar ← Std.Condvar.new

/-- This is to ensure we don't keep spawning server processes when `#gen_spec`
is re-elaborated in the editor. -/
initialize vcServerStarted : Std.Mutex Bool ← Std.Mutex.new false

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

namespace Frontend

open Lean.Elab.Command in
def notify : CommandElabM Unit := do
  frontendNotification.notifyAll

end Frontend

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
  | `useFieldRepTC => localEnv.modifyModule (fun _ => { mod with _useFieldRepTC := b })
  | `useLocalRPropTC => localEnv.modifyModule (fun _ => { mod with _useLocalRPropTC := b })
  | _ => throwError s!"Unsupported option {o}"

end DevelopingTools

section ModelCheckCompilationMode

/-! ## Model Check Compilation Mode

When building a model checker binary (triggered by default `#model_check` behavior
or by background compilation), the source file is re-elaborated. This option is set
to `true` during that compilation to:
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
