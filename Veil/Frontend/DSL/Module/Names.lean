module

public meta import Lean
public meta import Veil.Util.Meta

public meta section
open Lean

namespace Veil

/-- Mode shared by the action wrapper and the `veil_do` elaborator. -/
def veilModeVar : Ident := mkIdent (privateBinderName (mkVeilImplementationDetailName `mode))

/-- Name of the generic/environment background theory (i.e. `Reader` monad state)
variable. -/
def environmentTheoryName : Name := publicBinderName `ρ
def environmentTheory : Ident := mkIdent environmentTheoryName
def environmentSubTheoryName : Name := publicBinderName `ρ_sub
def environmentSubTheory : Ident := mkIdent environmentSubTheoryName

/-- Name of the environment state (for the `State` monad) variable. -/
def environmentStateName : Name := publicBinderName `σ
def environmentState : Ident := mkIdent environmentStateName

def environmentSubStateName : Name := publicBinderName `σ_sub
def environmentSubState : Ident := mkIdent environmentSubStateName

def stateName : Name := `State
def stateIdent : Ident := mkIdent stateName
def theoryName : Name := `Theory
def theoryIdent : Ident := mkIdent theoryName

def subStateInstIdent (id : Ident): Ident := mkIdent $ Name.mkSimple s!"{id.getId}_substate"
def environmentSubStateIdent : Ident := subStateInstIdent environmentState

def subReaderInstIdent (id : Ident): Ident := mkIdent $ Name.mkSimple s!"{id.getId}_reader"
def environmentSubReaderIdent : Ident := subReaderInstIdent environmentTheory

def assembledAssumptionsName : Name := `Assumptions
/-- The conjunction of all assumption clauses. -/
def assembledAssumptions : Ident := mkIdent assembledAssumptionsName

def assembledInvariantsName : Name := `Invariants
/-- The conjunction of all `invariant`, `safety`, and `trusted
invariant` clauses. -/
def assembledInvariants : Ident := mkIdent assembledInvariantsName

def assembledSafetiesName : Name := `Safeties
/-- The conjunction of all `safety` clauses. -/
def assembledSafeties : Ident := mkIdent assembledSafetiesName

def labelTypeName : Name := `Label
def labelType : Ident := mkIdent labelTypeName
def labelCasesName : Name := Name.append labelTypeName `cases
def labelCases: Ident := mkIdent labelCasesName

def actionTagTypeName : Name := `ActionTag
def actionTagType : Ident := mkIdent actionTagTypeName
def actionTagLabelEquivName : Name := Name.append actionTagTypeName `label_equiv
def actionTagLabelEquiv : Ident := mkIdent actionTagLabelEquivName

def instantiationTypeName : Name := `Instantiation
def instantiationType : Ident := mkIdent instantiationTypeName

def assembledNextActName : Name := `NextAct
def assembledNextAct : Ident := mkIdent assembledNextActName

def assembledNextName : Name := `Next
def assembledNext : Ident := mkIdent assembledNextName

/-- Direct transition relation assembled by case-splitting over action transitions.
This is distinct from `Next`, which is derived via `NextAct`. -/
def assembledNextTrName : Name := `NextTr
def assembledNextTr : Ident := mkIdent assembledNextTrName

/-- Unlabelled TLA action predicate (label becomes `∃`-quantified) assembled from `NextTr`. -/
def assembledNextStepName : Name := `NextStep
def assembledNextStep : Ident := mkIdent assembledNextStepName

def nextActSimplifiedName : Name := `NextAct'
def nextActSimplified : Ident := mkIdent nextActSimplifiedName

def fieldConcreteTypeName : Name := publicBinderName `χ
def fieldConcreteType : Ident := mkIdent fieldConcreteTypeName

def fieldConcreteDispatcherName : Name := `FieldConcreteType
def fieldConcreteDispatcher : Ident := mkIdent fieldConcreteDispatcherName

def fieldAbstractDispatcherName : Name := `FieldAbstractType
def fieldAbstractDispatcher : Ident := mkIdent fieldAbstractDispatcherName

def fieldRepresentationName : Name := publicBinderName `χ_rep
def fieldRepresentation : Ident := mkIdent fieldRepresentationName
def lawfulFieldRepresentationName : Name := publicBinderName `χ_rep_lawful
def lawfulFieldRepresentation : Ident := mkIdent lawfulFieldRepresentationName

def instEnumerationForIteratedProdName : Name := `instEnumerationForIteratedProd
def instEnumerationForIteratedProd : Ident := mkIdent instEnumerationForIteratedProdName

def instEnumerationForIteratedProdAllSomeCheckName : Name := `instEnumerationForIteratedProdAllSomeCheck
def instEnumerationForIteratedProdAllSomeCheck : Ident := mkIdent instEnumerationForIteratedProdAllSomeCheckName

def instFieldRepresentationName : Name := `instFieldRepresentation
def instFieldRepresentation : Ident := mkIdent instFieldRepresentationName

def instLawfulFieldRepresentationName : Name := `instLawfulFieldRepresentation
def instLawfulFieldRepresentation : Ident := mkIdent instLawfulFieldRepresentationName

def instAbstractFieldRepresentationName : Name := `instAbstractFieldRepresentation
def instAbstractFieldRepresentation : Ident := mkIdent instAbstractFieldRepresentationName

def instLawfulAbstractFieldRepresentationName : Name := `instLawfulAbstractFieldRepresentation
def instLawfulAbstractFieldRepresentation : Ident := mkIdent instLawfulAbstractFieldRepresentationName

def instInhabitedStateFieldConcreteTypeName : Name := `instInhabitedStateFieldConcreteType
def instInhabitedStateFieldConcreteType : Ident := mkIdent instInhabitedStateFieldConcreteTypeName

def structureFieldLabelTypeName (base : Name) : Name := base ++ labelTypeName
def structureFieldLabelType (base : Name) : Ident := mkIdent <| structureFieldLabelTypeName base
def fieldLabelToDomainName (base : Name) : Name := structureFieldLabelTypeName base ++ `toDomain
def fieldLabelToDomain (base : Name) : Ident := mkIdent <| fieldLabelToDomainName base
def fieldLabelToCodomainName (base : Name) : Name := structureFieldLabelTypeName base ++ `toCodomain
def fieldLabelToCodomain (base : Name) : Ident := mkIdent <| fieldLabelToCodomainName base
def stateIteEtaFieldsName : Name := stateName ++ `ite_eta_fields

def localRPropTCName : Name := `LocalRProp
def localRPropTC : Ident := mkIdent localRPropTCName
def localTheoryPropTCName : Name := `LocalTheoryProp
def localTheoryPropTC : Ident := mkIdent localTheoryPropTCName

/-- `t_EnumClass` is a type class. -/
def Name.toEnumClass (name : Name) : Name := name.appendAfter "_EnumClass"
def Ident.toEnumClass (id : Ident) : Ident := mkIdent $ Name.toEnumClass id.getId

/-- `t_Enum` is an instance, where `t` is declared as an `enum` type. -/
def Name.toEnumInst (name : Name) : Name := name.appendAfter "_Enum"
def Ident.toEnumInst (id : Ident) : Ident := mkIdent $ Name.toEnumInst id.getId

def Name.toEnumConcreteTypeName (name : Name) : Name := name.appendAfter "_IndT"
def Ident.toEnumConcreteType (id : Ident) : Ident := mkIdent $ Name.toEnumConcreteTypeName id.getId

def enumDistinctName : Name := `distinct
def enumDistinct : Ident := mkIdent enumDistinctName

def enumCompleteName : Name := `complete
def enumComplete : Ident := mkIdent enumCompleteName

def enumerableTransitionSystemName : Name := `enumerableTransitionSystem
def enumerableTransitionSystem : Ident := mkIdent enumerableTransitionSystemName

def pickSourceName : Name := `pickSource
def pickSource : Ident := mkIdent pickSourceName

def assembledInitName : Name := `Init
def assembledInit : Ident := mkIdent assembledInitName

def assembledRTSName : Name := `relationalTransitionSystem
def assembledRTS : Ident := mkIdent assembledRTSName

def exceptionName : Name := privateBinderName (mkVeilImplementationDetailName `ex)
def exception : Ident := mkIdent exceptionName

/-- A numeric name component keeps model binders distinct from source identifiers,
even when Lean exposes shadowed names or appends structure projections. -/
private def modelParameterPrefix : Name := .num `__veil_model_param 0

def modelParameterName (source : Name) : Name :=
  modelParameterPrefix ++ source

def isModelParameterName (name : Name) : Bool :=
  modelParameterPrefix.isPrefixOf name

def modelParameterDisplayName (name : Name) : Name :=
  name.replacePrefix modelParameterPrefix `param

/-- Tactics such as `expose_names` can remove scopes before SMT sees a binder.
Keep the model role in a numeric name component too, including on projections. -/
private def modelBinderPrefix : Name := .num `__veil_model 0

def modelValueName (name : Name) : Name := modelBinderPrefix ++ name

def modelBinderName (name : Name) : Name :=
  addMacroScope `Veil.model name reservedMacroScope

/-- Encode the role in the elaborated VC, where binder names need no longer be atomic. -/
def persistModelBinderName (name : Name) : Name :=
  let scope := extractMacroScopes name
  if scope.ctx == `Veil.model then modelValueName scope.name else name

def modelBinderKey? (name : Name) : Option Name := do
  let key := name.eraseMacroScopes
  guard (modelBinderPrefix.isPrefixOf key)
  return key.replacePrefix modelBinderPrefix .anonymous

/-- Preserve the dictionary binder as well as its projection path in the model. -/
def modelInstanceName (source : Name) : Name := modelValueName (`inst ++ source)

def modelInstanceKey? (name : Name) : Option Name := do
  let key ← modelBinderKey? name
  guard (key.getRoot == `inst)
  return key.replacePrefix `inst .anonymous

def traceStateName (i : Nat) : Name := .mkSimple s!"st{i}"
def traceTagName (i : Nat) : Name := .mkSimple s!"_tr{i}_tag"
def traceArgumentName (step action argument : Nat) : Name :=
  .mkSimple s!"_tr{step}_act{action}_arg{argument}"

/-- Name of the ActionTag_Enum instance binder -/
def actionTagEnumInstName : Name := mkVeilImplementationDetailName `tag
def actionTagEnumInst : Ident := mkIdent (modelBinderName actionTagEnumInstName)

def transitionWeakeningLemmaName : Name := `_transitionWeakeningLemma
def transitionWeakeningLemma : Ident := mkIdent transitionWeakeningLemmaName

def localMeetsSpecificationIfSuccessfulAssumingName : Name :=
  mkVeilImplementationDetailName `meetsSpecificationIfSuccessfulAssuming_local
def localMeetsSpecificationIfSuccessfulAssuming : Ident :=
  mkIdent localMeetsSpecificationIfSuccessfulAssumingName

def localTransitionMeetsSpecificationIfSuccessfulAssumingName : Name :=
  mkVeilImplementationDetailName `transition_meetsSpecificationIfSuccessfulAssuming_local
def localTransitionMeetsSpecificationIfSuccessfulAssuming : Ident :=
  mkIdent localTransitionMeetsSpecificationIfSuccessfulAssumingName

/-- The name under which every statement of a Veil action binds, with a fresh
`get`, the state it executes in (see `Veil.Action.DoElab.openStateAround`).
Each statement's binding shadows the previous one, so the newest binding of
this name in a local context is the current state. -/
def currentStateBindingName : Name := mkVeilImplementationDetailName `state

end Veil
