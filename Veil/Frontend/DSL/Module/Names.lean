import Lean
import Veil.Util.Meta
open Lean

namespace Veil

/-- The name used to parametrise the `mode` of the `VeilM` monad. This
is intentionally a non-hygienic name, since we bind it when we
elaborate the syntax expanded by `elabVeilDo`. -/
def veilModeVar : Ident := mkIdent $ mkVeilImplementationDetailName `mode


/-- Name of the generic/environment background theory (i.e. `Reader` monad state)
variable. -/
def environmentTheoryName : Name := `ρ
def environmentTheory : Ident := mkIdent environmentTheoryName
def environmentSubTheoryName : Name := `ρ_sub
def environmentSubTheory : Ident := mkIdent environmentSubTheoryName

/-- Name of the environment state (for the `State` monad) variable. -/
def environmentStateName : Name := `σ
def environmentState : Ident := mkIdent environmentStateName
def environmentSubStateName : Name := `σ_sub
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

def assembledNextActName : Name := `NextAct
def assembledNextAct : Ident := mkIdent assembledNextActName

def nextActSimplifiedName : Name := `NextAct'
def nextActSimplified : Ident := mkIdent nextActSimplifiedName

def fieldConcreteTypeName : Name := `χ
def fieldConcreteType : Ident := mkIdent fieldConcreteTypeName

def fieldConcreteDispatcherName : Name := `FieldConcreteType
def fieldConcreteDispatcher : Ident := mkIdent fieldConcreteDispatcherName

def fieldRepresentationName : Name := `χ_rep
def fieldRepresentation : Ident := mkIdent fieldRepresentationName
def lawfulFieldRepresentationName : Name := `χ_rep_lawful
def lawfulFieldRepresentation : Ident := mkIdent lawfulFieldRepresentationName

def instEnumerationForIteratedProdName : Name := `instEnumerationForIteratedProd
def instEnumerationForIteratedProd : Ident := mkIdent instEnumerationForIteratedProdName

def instFieldRepresentationName : Name := `instFieldRepresentation
def instFieldRepresentation : Ident := mkIdent instFieldRepresentationName

def instLawfulFieldRepresentationName : Name := `instLawfulFieldRepresentation
def instLawfulFieldRepresentation : Ident := mkIdent instLawfulFieldRepresentationName

def structureFieldLabelTypeName (base : Name) : Name := base ++ labelTypeName
def structureFieldLabelType (base : Name) : Ident := mkIdent <| structureFieldLabelTypeName base
def fieldLabelToDomainName (base : Name) : Name := structureFieldLabelTypeName base ++ `toDomain
def fieldLabelToDomain (base : Name) : Ident := mkIdent <| fieldLabelToDomainName base
def fieldLabelToCodomainName (base : Name) : Name := structureFieldLabelTypeName base ++ `toCodomain
def fieldLabelToCodomain (base : Name) : Ident := mkIdent <| fieldLabelToCodomainName base

def localRPropTCName : Name := `LocalRProp
def localRPropTC : Ident := mkIdent localRPropTCName

/-- `t_Enum` is a type class. -/
def Name.toEnumClass (name : Name) : Name := name.appendAfter "_Enum"
def Ident.toEnumClass (id : Ident) : Ident := mkIdent $ Name.toEnumClass id.getId

/-- `t_isEnum` is an instance, where `t` is declared as an `enum` type. -/
def Name.toEnumInst (name : Name) : Name := name.appendAfter "_isEnum"
def Ident.toEnumInst (id : Ident) : Ident := mkIdent $ Name.toEnumInst id.getId

def Name.toEnumConcreteTypeName (name : Name) : Name := name.appendAfter "_IndT"
def Ident.toEnumConcreteType (id : Ident) : Ident := mkIdent $ Name.toEnumConcreteTypeName id.getId

def enumDistinctName : Name := `distinct
def enumDistinct : Ident := mkIdent enumDistinctName

def enumCompleteName : Name := `complete
def enumComplete : Ident := mkIdent enumCompleteName

end Veil
