import Veil.Base
import Veil.Frontend.DSL.Module.Representation

open Lean Elab Command
namespace Veil

/-- The optional full frontend's spec-finalization entry point. -/
structure VerificationSupport where
  finalizeSpec : Module → Syntax → CommandElabM Module

/-- Import-scoped capability: full Veil provides this declaration, Core does not. -/
def hasVerificationSupport [Monad m] [MonadEnv m] : m Bool := do
  return (← getEnv).contains `Veil.fullVerificationSupport

def shouldGenerateVerification [Monad m] [MonadEnv m] [MonadOptions m] : m Bool := do
  return (← hasVerificationSupport) && !veil.__modelCheckCompileMode.get (← getOptions)

def getVerificationSupport? : CommandElabM (Option VerificationSupport) := do
  unless ← hasVerificationSupport do return none
  return some (← IO.ofExcept <| unsafe (← getEnv).evalConstCheck VerificationSupport
    (← getOptions) ``VerificationSupport `Veil.fullVerificationSupport)

end Veil
