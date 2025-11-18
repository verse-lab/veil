import Veil
import Veil.Core.Tools.Checker.Concrete.Main


veil module DieHard

individual big : Nat
individual small : Nat

#gen_state

after_init {
  big := 0
  small := 0
}


action FillSmallJug {
  small := 3
  big := big
}


action FillBigJug  {
  big := 5
  small := small
}


action EmptySmallJug {
  small := 0
  big := big
}


action EmptyBigJug {
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


#gen_exec

#finitizeTypes


def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => not_solved ρ σ) ((fun ρ σ => true)) {} hash).snd
def statesJson : Lean.Json :=Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM {} (collectTrace' modelCheckerResult'))
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />



end DieHard
