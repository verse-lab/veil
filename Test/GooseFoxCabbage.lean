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

-- section

-- veil_variables

-- omit χ χ_rep χ_rep_lawful

open Veil Extract

#check position

-- deriving_FinOrdToJson_Domain
-- specify_FieldConcreteType


instance instFinEnumForToDomain (position : Type) [FinEnum position] (f : State.Label) :
    (Veil.IteratedProd <| (List.map FinEnum <| (State.Label.toDomain position) f)) := by
  cases f <;> infer_instance_for_iterated_prod
instance instOrdForToDomain' (position : Type) [Ord position] (f : State.Label) :
    (Ord (Veil.IteratedProd' <| (State.Label.toDomain position) f)) := by
  cases f <;> dsimp only [Veil.IteratedProd', List.foldr, State.Label.toDomain, State.Label.toCodomain] <;>
    infer_instance
instance instToJsonForToDomain' (position : Type) [Lean.ToJson position] (f : State.Label) :
    (Lean.ToJson (Veil.IteratedProd' <| (State.Label.toDomain position) f)) := by
  cases f <;> dsimp only [Veil.IteratedProd', List.foldr, State.Label.toDomain, State.Label.toCodomain] <;>
    infer_instance
instance instToJsonForToCodomain [Lean.ToJson position] (f : State.Label) :
    (Lean.ToJson ((State.Label.toCodomain position) f)) := by
  cases f <;> dsimp only [Veil.IteratedProd', List.foldr, State.Label.toDomain, State.Label.toCodomain] <;>
    infer_instance


abbrev FieldConcreteType (position : Type) [Ord position] (f : State.Label) : Type :=
  match f with
  | State.Label.wolf_pos => (State.Label.toCodomain position) State.Label.wolf_pos
  | State.Label.goat_pos => (State.Label.toCodomain position) State.Label.goat_pos
  | State.Label.cabbage_pos => (State.Label.toCodomain position) State.Label.cabbage_pos
  | State.Label.farmer_pos => (State.Label.toCodomain position) State.Label.farmer_pos

#check FieldConcreteType

instance
{ρ σ position : Type}
[position_dec_eq : DecidableEq position]
[position_inhabited : Inhabited position]
[position_isEnum : position_Enum position]
-- (χ : State.Label → Type)
-- [χ_rep : (f : State.Label) → FieldRepresentation (State.Label.toDomain position f) (State.Label.toCodomain position f) (χ f)]
-- [χ_rep_lawful : ∀ (f : State.Label), LawfulFieldRepresentation (State.Label.toDomain position f) (State.Label.toCodomain position f) (χ f) (χ_rep f)]
-- [σ_sub : IsSubStateOf (State position χ) σ]
-- [ρ_sub : IsSubReaderOf (Theory position) ρ]
[Ord position]:
    (BEq (FieldConcreteType position State.Label.wolf_pos)) :=
  by
  dsimp only [FieldConcreteType, Veil.IteratedProd', State.Label.toDomain, State.Label.toCodomain]
  repeat'
    (first
      | infer_instance
      | constructor)


#exit
deriving_BEq_FieldConcreteType

deriving_Hashable_FieldConcreteType

deriving_rep_FieldRepresentation

deriving_lawful_FieldRepresentation

deriving_Inhabited_State

deriving_Decidable_Props


gen_NextAct

gen_executable_NextAct

deriving_Enum_Insts
-- deriving_enum_instance_for position
-- deriving_ord_hashable_for_enum position
-- deriving_propCmp_for_enum position

#Concretize position


deriving_BEqHashable_ConcreteState
simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory
deriving_toJson_for_state
deriving_DecidableProps_state


def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => unsolved ρ σ) ((fun ρ σ => true)) {} hash).snd


def statesJson : Lean.Json :=
  Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM {} (collectTrace' modelCheckerResult'))
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />



end RiverCrossing
