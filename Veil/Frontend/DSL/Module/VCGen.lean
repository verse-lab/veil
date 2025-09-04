import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Util.Meta

open Lean Elab

namespace Veil

private def mkDoesNotThrowVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (act : ProcedureSpecification) : m (VCData VCMetadata) := do
  let actBinders ← act.binders
  let actArgs ← bracketedBindersToTerms actBinders
  return {
    name := Name.mkSimple s!"{act.name}_doesNotThrow",
    params := ← mod.parameters.mapM (·.binder),
    statement := ← expandTermMacro $ ← `(term|
      forall? $(← act.binders)*,
        $(mkIdent ``VeilM.doesNotThrowAssuming)
          (@$(mkIdent act.name) $(← mod.actionParamsMapFn (·.argInferred) act.name)* $actArgs*)
          (@$assembledAssumptions $(← mod.derivedDefinitionParamsMapFn (·.argInferred) assembledAssumptionsName)*)
          (@$assembledInvariants $(← mod.derivedDefinitionParamsMapFn (·.argInferred) assembledInvariantsName)*)
    ),
    meta := default
  }

def Module.generateVCs [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m] (mod : Module) : m (VCManager VCMetadata) := do
  let mut vcManager := default
  let mut vc := default
  -- We need to build the VCs "bottom-up", i.e. from the "smallest"
  -- statements to the "largest".
  let actsToCheck := mod.procedures.filter (fun s => match s.info with
    | .action _ | .initializer => true
    | .procedure _ => false)
  for act in actsToCheck do
    (vcManager, vc) := vcManager.addVC ( ← mkDoesNotThrowVC mod act) {}
    trace[veil.debug] "(VC {vc.uid})\n{← vc.theoremStx}"
  return vcManager

end Veil
