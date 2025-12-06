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
def theoryName : Name := `Theory

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

def fieldConcreteTypeName : Name := `χ
def fieldConcreteType : Ident := mkIdent fieldConcreteTypeName

def fieldConcreteDispatcherName : Name := `_FieldConcreteType
def fieldConcreteDispatcher : Ident := mkIdent fieldConcreteDispatcherName

def fieldRepresentationName : Name := `χ_rep
def fieldRepresentation : Ident := mkIdent fieldRepresentationName
def lawfulFieldRepresentationName : Name := `χ_rep_lawful
def lawfulFieldRepresentation : Ident := mkIdent lawfulFieldRepresentationName

def structureFieldLabelTypeName (base : Name) : Name := base ++ labelTypeName
def structureFieldLabelType (base : Name) : Ident := mkIdent <| structureFieldLabelTypeName base
def fieldLabelToDomainName (base : Name) : Name := structureFieldLabelTypeName base ++ `toDomain
def fieldLabelToDomain (base : Name) : Ident := mkIdent <| fieldLabelToDomainName base
def fieldLabelToCodomainName (base : Name) : Name := structureFieldLabelTypeName base ++ `toCodomain
def fieldLabelToCodomain (base : Name) : Ident := mkIdent <| fieldLabelToCodomainName base

def localRPropTCName : Name := `LocalRProp
def localRPropTC : Ident := mkIdent localRPropTCName

end Veil
