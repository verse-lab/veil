import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Util.Meta

open Lean Elab

namespace Veil

private def mkVCForSpecTheorem [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (act : ProcedureSpecification) (specName : Name) (vcName : Name) (vcKind : VCKind) (extraDeps : Std.HashSet Name := {}) (extraTerms : Array Term := #[]): m (VCData VCMetadata) := do
  let dependsOn := extraDeps.insertMany #[act.name, assembledAssumptionsName, assembledInvariantsName]
  let (thmBaseParams, thmExtraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .theoremLike dependsOn)
  let actBinders ← act.binders
  return {
    name := vcName,
    params := ← (thmBaseParams ++ thmExtraParams).mapM (·.binder),
    statement := ← expandTermMacro $ ← `(term|
      forall? $actBinders*,
        $(mkIdent specName)
          (@$(mkIdent act.name) $(← mod.declarationAllParamsMapFn (·.arg) act.name (.procedure act.info))* $(← bracketedBindersToTerms actBinders)*)
          (@$assembledAssumptions $(← mod.declarationAllParamsMapFn (·.arg) assembledAssumptionsName (.derivedDefinition .assumptionLike dependsOn))*)
          (@$assembledInvariants $(← mod.declarationAllParamsMapFn (·.arg) assembledInvariantsName (.derivedDefinition .invariantLike dependsOn))*)
          $extraTerms:term*
    ),
    meta := {
      kind := vcKind,
      baseParams := thmBaseParams,
      extraParams := thmExtraParams,
      stmtDerivedFrom := dependsOn
    }
  }

private def mkDoesNotThrowVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (act : ProcedureSpecification) : m (VCData VCMetadata) :=
  mkVCForSpecTheorem mod act ``VeilM.doesNotThrowAssuming (Name.mkSimple s!"{act.name}_doesNotThrow") .primary

private def mkMeetsSpecificationIfSuccessfulClauseVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (act : ProcedureSpecification) (invariantClause : Name) : m (VCData VCMetadata) := do
  let extraDeps := {invariantClause}
  let extraTerms := #[← `(term| (@$(mkIdent invariantClause) $(← mod.declarationAllParamsMapFn (·.arg) invariantClause (.stateAssertion .invariant))*) )]
  mkVCForSpecTheorem mod act ``VeilM.meetsSpecificationIfSuccessfulAssuming (Name.mkSimple s!"{act.name}_{invariantClause}") .primary extraDeps extraTerms

private def mkPreservesInvariantsIfSuccessfulVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (act : ProcedureSpecification) : m (VCData VCMetadata) :=
  mkVCForSpecTheorem mod act ``VeilM.preservesInvariantsIfSuccessfulAssuming (Name.mkSimple s!"{act.name}_preservesInvariants") .derived

private def mkSucceedsAndInvariantsIfSuccessfulVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (act : ProcedureSpecification) : m (VCData VCMetadata) :=
  mkVCForSpecTheorem mod act ``VeilM.succeedsAndPreservesInvariantsAssuming (Name.mkSimple s!"{act.name}_succeedsAndPreservesInvariants") .derived


def Module.generateVCs [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m] (mod : Module) : m (VCManager VCMetadata) := do
  let mut vcManager := default
  -- We need to build the VCs "bottom-up", i.e. from the "smallest"
  -- statements to the "largest".
  let actsToCheck := mod.procedures.filter (fun s => match s.info with
    | .action _ | .initializer => true
    | .procedure _ => false)
  let mut succeedsAndPreservesInvariantsVCs : Std.HashSet VCId := {}
  -- Per-action checks
  for act in actsToCheck do
    -- The action does not throw any exceptions, assuming the `Invariants`
    let mut doesNotThrowVC := default
    (vcManager, doesNotThrowVC) := vcManager.addVC ( ← mkDoesNotThrowVC mod act) {}
    -- Assuming the `Invariants`, this action preserves every invariant clause
    let mut clausesVCs : Std.HashSet VCId := {}
    for invariantClause in mod.checkableInvariants do
      let mut clauseVC := default
      (vcManager, clauseVC) := vcManager.addVC ( ← mkMeetsSpecificationIfSuccessfulClauseVC mod act invariantClause.name) {}
      clausesVCs := clausesVCs.insert clauseVC
    -- Per-action overall invariant preservation VC
    let mut preservesInvariantsVC := default
    (vcManager, preservesInvariantsVC) := vcManager.addVC ( ← mkPreservesInvariantsIfSuccessfulVC mod act) clausesVCs

    let mut succeedsAndPreservesInvariantsVC := default
    (vcManager, succeedsAndPreservesInvariantsVC) := vcManager.addVC ( ← mkSucceedsAndInvariantsIfSuccessfulVC mod act) {doesNotThrowVC, preservesInvariantsVC}
    succeedsAndPreservesInvariantsVCs := succeedsAndPreservesInvariantsVCs.insert succeedsAndPreservesInvariantsVC
  -- TODO: `NextAct` theorem
  return vcManager

end Veil
