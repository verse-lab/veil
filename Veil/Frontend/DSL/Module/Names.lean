import Lean
open Lean

namespace Veil

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


end Veil
