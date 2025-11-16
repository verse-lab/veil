import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main
import ProofWidgets.Component.HtmlDisplay

veil module RiverCrossing

enum position = {near, far}
individual wolf_pos : position
individual goat_pos : position
individual cabbage_pos : position
individual farmer_pos : position

#print position_Enum
-- enum act = {Init, FarmerAndWolf, FarmerAndGoat, FarmerAndCabbage, FarmerAlone}
-- individual lastAction : act

#gen_state

/-
Puzzle Rules:
 * If goat and wolf are on the same bank p, the farmer must also be on p.
 * If goat and cabbage are on the same bank p, the farmer must also be on p.
-/
ghost relation safety_constraint :=
     (goat_pos = wolf_pos → farmer_pos = goat_pos) ∧
     (goat_pos = cabbage_pos → farmer_pos = goat_pos)

after_init {
  wolf_pos := near
  goat_pos := near
  cabbage_pos := near
  farmer_pos := near
  -- lastAction := Init
}

action FarmerAndWolf {
  require (goat_pos = wolf_pos → farmer_pos = goat_pos) ∧ (goat_pos = cabbage_pos → farmer_pos = goat_pos)
  require farmer_pos = wolf_pos

  if farmer_pos = far then
    farmer_pos := near
    wolf_pos := near
  else
    farmer_pos := far
    wolf_pos := far
  -- lastAction := FarmerAndWolf
}

action FarmerAndGoat {
  require (goat_pos = wolf_pos → farmer_pos = goat_pos) ∧ (goat_pos = cabbage_pos → farmer_pos = goat_pos)
  require farmer_pos = goat_pos
  if farmer_pos = far then
    farmer_pos := near
    goat_pos := near
  else
    farmer_pos := far
    goat_pos := far
  -- lastAction := FarmerAndGoat
}


action FarmerAndCabbage {
  require (goat_pos = wolf_pos → farmer_pos = goat_pos) ∧ (goat_pos = cabbage_pos → farmer_pos = goat_pos)
  require farmer_pos = cabbage_pos
  if farmer_pos = far then
    farmer_pos := near
    cabbage_pos := near
  else
    farmer_pos := far
    cabbage_pos := far
  -- lastAction := FarmerAndCabbage
}

action FarmerAlone {
  require (goat_pos = wolf_pos → farmer_pos = goat_pos) ∧ (goat_pos = cabbage_pos → farmer_pos = goat_pos)
  if farmer_pos = far then
    farmer_pos := near
  else
    farmer_pos := far
  -- lastAction := FarmerAlone
}


invariant [unsolved] ¬ (goat_pos = far ∧ wolf_pos = far ∧ cabbage_pos = far ∧ farmer_pos = far)

#gen_spec


#gen_exec
#finitizeTypes position


def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => unsolved ρ σ) ((fun ρ σ => true)) {} hash).snd
def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM {} (collectTrace' modelCheckerResult'))
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />



end RiverCrossing
