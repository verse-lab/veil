module

public meta import Veil.Base
public meta import Veil.Frontend.DSL.Module.Representation

public meta section

open Lean Elab Command
namespace Veil

/-- The optional full frontend's spec-finalization entry point. -/
structure VerificationSupport where
  finalizeSpec : Module → Syntax → CommandElabM Module

-- Initializers register the typed callback, but registration alone must not
-- enable verification in other environments in the same process.
private initialize verificationSupportRef : IO.Ref (Option VerificationSupport) ← IO.mkRef none

/-- Register the full frontend's implementation during initialization. -/
def registerVerificationSupport (support : VerificationSupport) : IO Unit := do
  unless ← Lean.initializing do
    throw <| IO.userError "verification support must be registered during initialization"
  verificationSupportRef.set (some support)

-- Only the presence of support is serialized, not the callback. This marker
-- follows the imports of each environment, independently of loaded initializers.
private initialize verificationSupportExt : SimplePersistentEnvExtension Unit Bool ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ _ => true
    addImportedFn := fun entries => entries.any (!·.isEmpty)
  }

/-- Enable the registered implementation in this module and its importers. -/
def enableVerificationSupport : CommandElabM Unit :=
  modifyEnv (verificationSupportExt.addEntry · ())

/-- Whether this environment imports the full verification frontend. -/
def hasVerificationSupport [Monad m] [MonadEnv m] : m Bool := do
  return verificationSupportExt.getState (← getEnv)

/-- Get the typed implementation only when this environment enables it. -/
def getVerificationSupport? : CommandElabM (Option VerificationSupport) := do
  unless ← hasVerificationSupport do return none
  let some support ← verificationSupportRef.get
    | throwError "full verification support was enabled but not initialized"
  return some support

end Veil
