import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Util.Meta

open Lean Elab

namespace Veil

private def mkDoesNotThrowVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (act : ProcedureSpecification) : m (VCData VCMetadata) := do
  let dependsOn : Std.HashSet Name := {act.name, assembledAssumptionsName, assembledInvariantsName}
  let (thmBaseParams, thmExtraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) .theoremLike dependsOn
  let actBinders ← act.binders
  let actArgs ← bracketedBindersToTerms actBinders
  return {
    name := Name.mkSimple s!"{act.name}_doesNotThrow",
    params := ← (thmBaseParams ++ thmExtraParams).mapM (·.binder),
    statement := ← expandTermMacro $ ← `(term|
      forall? $actBinders*,
        $(mkIdent ``VeilM.doesNotThrowAssuming)
          (@$(mkIdent act.name) $(← mod.actionParamsMapFn (·.arg) act.name)* $actArgs*)
          (@$assembledAssumptions $(← mod.derivedDefinitionParamsMapFn (·.arg) assembledAssumptionsName)*)
          (@$assembledInvariants $(← mod.derivedDefinitionParamsMapFn (·.arg) assembledInvariantsName)*)
    ),
    meta := {
      baseParams := thmBaseParams,
      extraParams := thmExtraParams,
      stmtDerivedFrom := dependsOn
    }
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
