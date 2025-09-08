import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Util.Meta

open Lean Elab

namespace Veil

private def mkVCForSpecTheorem [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (actBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder) (specName : Name) (vcName : Name) (vcKind : VCKind) (extraDeps : Std.HashSet Name := {}) (extraTerms : Array Term := #[]): m (VCData VCMetadata) := do
  let dependsOn := extraDeps.insertMany #[actName, assembledAssumptionsName, assembledInvariantsName]
  let (thmBaseParams, thmExtraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .theoremLike dependsOn)
  return {
    name := vcName,
    params := ← (thmBaseParams ++ thmExtraParams).mapM (·.binder),
    statement := ← expandTermMacro $ ← `(term|
      forall? $actBinders*,
        $(mkIdent specName)
          (@$(mkIdent actName) $(← mod.declarationAllParamsMapFn (·.arg) actName actKind)* $(← bracketedBindersToTerms actBinders)*)
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
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (actBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder) (vcKind : VCKind) : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind actBinders ``VeilM.doesNotThrowAssuming (Name.mkSimple s!"{actName}_doesNotThrow") vcKind

private def mkMeetsSpecificationIfSuccessfulClauseVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (actBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder) (invariantClause : Name) (vcKind : VCKind) : m (VCData VCMetadata) := do
  let extraDeps := {invariantClause}
  let extraTerms := #[← `(term| (@$(mkIdent invariantClause) $(← mod.declarationAllParamsMapFn (·.arg) invariantClause (.stateAssertion .invariant))*) )]
  mkVCForSpecTheorem mod actName actKind actBinders ``VeilM.meetsSpecificationIfSuccessfulAssuming (Name.mkSimple s!"{actName}_{invariantClause}") vcKind extraDeps extraTerms

private def mkPreservesInvariantsIfSuccessfulVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (actBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder) (vcKind : VCKind) : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind actBinders ``VeilM.preservesInvariantsIfSuccessfulAssuming (Name.mkSimple s!"{actName}_preservesInvariants") vcKind

private def mkSucceedsAndInvariantsIfSuccessfulVC [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
  (mod : Module) (actName : Name) (actKind : DeclarationKind) (actBinders : TSyntaxArray `Lean.Parser.Term.bracketedBinder) (vcKind : VCKind) : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind actBinders ``VeilM.succeedsAndPreservesInvariantsAssuming (Name.mkSimple s!"{actName}_succeedsAndPreservesInvariants") vcKind


def Module.generateVCs [Monad m] [MonadQuotation m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m] (mod : Module) : m (VCManager VCMetadata) := do
  let mut vcManager := default
  -- We need to build the VCs "bottom-up", i.e. from the "smallest"
  -- statements to the "largest".
  let actsToCheck := mod.procedures.filter (fun s => match s.info with
    | .action _ | .initializer => true
    | .procedure _ => false)
  let mut doesNotThrowVCs : Std.HashSet VCId := {}
  let mut clausesVCsByInv : Std.HashMap Name (Std.HashSet VCId) := {}
  let mut preservesInvariantsVCs : Std.HashSet VCId := {}
  let mut succeedsAndPreservesInvariantsVCs : Std.HashSet VCId := {}
  -- Per-action checks
  for act in actsToCheck do
    -- The action does not throw any exceptions, assuming the `Invariants`
    let mut doesNotThrowVC := default
    (vcManager, doesNotThrowVC) := vcManager.addVC ( ← mkDoesNotThrowVC mod act.name act.declarationKind (← act.binders) .primary) {}
    doesNotThrowVCs := doesNotThrowVCs.insert doesNotThrowVC

    -- Assuming the `Invariants`, this action preserves every invariant clause
    let mut clauseVCsForAct : Std.HashSet VCId := {}
    for invariantClause in mod.checkableInvariants do
      let mut clauseVC := default
      (vcManager, clauseVC) := vcManager.addVC ( ← mkMeetsSpecificationIfSuccessfulClauseVC mod act.name act.declarationKind (← act.binders) invariantClause.name .primary) {}
      clausesVCsByInv := clausesVCsByInv.insert invariantClause.name ((clausesVCsByInv.getD invariantClause.name {}).insert clauseVC)
      clauseVCsForAct := clauseVCsForAct.insert clauseVC

    -- Per-action overall invariant preservation VC
    let mut preservesInvariantsVC := default
    (vcManager, preservesInvariantsVC) := vcManager.addVC ( ← mkPreservesInvariantsIfSuccessfulVC mod act.name act.declarationKind (← act.binders) .derived) clauseVCsForAct
    preservesInvariantsVCs := preservesInvariantsVCs.insert preservesInvariantsVC

    let mut succeedsAndPreservesInvariantsVC := default
    (vcManager, succeedsAndPreservesInvariantsVC) := vcManager.addVC ( ← mkSucceedsAndInvariantsIfSuccessfulVC mod act.name act.declarationKind (← act.binders) .derived) {doesNotThrowVC, preservesInvariantsVC}
    succeedsAndPreservesInvariantsVCs := succeedsAndPreservesInvariantsVCs.insert succeedsAndPreservesInvariantsVC

  -- `NextAct` theorems
  let .some dd := mod._derivedDefinitions[assembledNextActName]?
    | throwError s!"[Module.generateVCs] derived definition {assembledNextActName} not found"
  (vcManager, _) := vcManager.addVC ( ← mkDoesNotThrowVC mod assembledNextActName dd.declarationKind (← dd.binders) .derived) doesNotThrowVCs
  for invariantClause in mod.checkableInvariants do
    (vcManager, _) := vcManager.addVC ( ← mkMeetsSpecificationIfSuccessfulClauseVC mod assembledNextActName dd.declarationKind (← dd.binders) invariantClause.name .derived) (clausesVCsByInv[invariantClause.name]!)
  (vcManager, _) := vcManager.addVC ( ← mkPreservesInvariantsIfSuccessfulVC mod assembledNextActName dd.declarationKind (← dd.binders) .derived) preservesInvariantsVCs
  (vcManager, _) := vcManager.addVC ( ← mkSucceedsAndInvariantsIfSuccessfulVC mod assembledNextActName dd.declarationKind (← dd.binders) .derived) succeedsAndPreservesInvariantsVCs

  return vcManager

end Veil
