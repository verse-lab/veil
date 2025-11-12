import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main
import ProofWidgets.Component.HtmlDisplay

veil module DieHard

individual big : Nat
-- individual tmp : Nat
individual small : Nat

#gen_state

after_init {
  big := 0
  small := 0
}


action FillSmallJug {
  -- (small : Nat) := 3
  small := 3
  big := big
}


action FillBigJug  {
  big := 5
  small := small
}


action EmptySmallJug {
  -- (small : Nat) := 0
  small := 0
  big := big
}


action EmptyBigJug {
  -- (big : Nat) := 0w
  big := 0
  small := small
}


action SmallToBig {
  let tmp := big
  big := if big + small < 5 then big + small else 5
  small := small - (big - tmp)
}



action BigToSmall {
  let tmp := small
  small := if big + small < 3 then big + small else 3
  big := big - (small - tmp)
}


invariant [typeOK] small≤ 3 ∧ big ≤ 5


invariant [not_solved] big ≠ 4

#gen_spec


#time #check_invariants
section


veil_variables

omit χ χ_rep χ_rep_lawful

deriving_FinOrdToJson_Domain

specify_FieldConcreteType

deriving_BEq_FieldConcreteType

deriving_Repr_FieldConcreteType

deriving_Hashable_FieldConcreteType

deriving_rep_FieldRepresentation

deriving_lawful_FieldRepresentation

deriving_Inhabited_State

end

gen_NextAct
gen_executable_NextAct


#Concretize

deriving_BEqHashable_ConcreteState
simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory
deriving_toJson_for_state
deriving_DecidableProps_state


def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => not_solved ρ σ) ((fun ρ σ => true)) {} hash).snd
def statesJson : Lean.Json :=
  Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM {} (collectTrace' modelCheckerResult'))

open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />



end DieHard
