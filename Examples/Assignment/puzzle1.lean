import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main

veil module RiverCrossing
-- --------------------- MODULE RiverCrossing ---------------------
-- EXTENDS TLC, FiniteSets

-- Passenger == {"wolf","goat","cabbage"}
-- position == {"near","far"}

-- enum Passenger = {wolf, goat, cabbage}
enum position = {near, far}

individual wolf_pos : position
individual goat_pos : position
individual cabbage_pos : position
individual farmer_pos : position
-- VARIABLES passengers, farmer

#gen_state


-- \* Initially, all entities reside at the near bank
-- Init == /\ passengers = [p \in Passenger |-> "near"]
--         /\ farmer = "near"
after_init {
  wolf_pos := near
  goat_pos := near
  cabbage_pos := near
  farmer_pos := near
}

-- \* Farmer can only bring wolf if and only if goat and cabbage are separated
-- FarmerAndWolf == /\ passengers["goat"] /= passengers["cabbage"]
--                  /\ farmer = passengers["wolf"]
--                  /\ IF farmer = "far" THEN /\ farmer' = "near"
--                                            /\ passengers' = [passengers EXCEPT !["wolf"] = "near"]
--                                       ELSE /\ farmer' = "far"
--                                            /\ passengers' = [passengers EXCEPT !["wolf"] = "far"]
action FarmerAndWolf {
  require ¬(goat_pos == cabbage_pos)
  require farmer_pos == wolf_pos
  if farmer_pos == far then
    farmer_pos := near
    wolf_pos := near
  else
    farmer_pos := far
    wolf_pos := far

}
-- \* Farmer can freely bring goat since there is no problem when cabbage and wolf are together
-- FarmerAndGoat == IF farmer = "far" THEN /\ farmer' = "near"
--                                         /\ passengers' = [passengers EXCEPT !["goat"] = "near"]
--                                       ELSE /\ farmer' = "far"
--                                            /\ passengers' = [passengers EXCEPT !["goat"] = "far"]
action FarmerAndGoat {
  require farmer_pos = goat_pos
  if farmer_pos == far then
    farmer_pos := near
    goat_pos := near
  else
    farmer_pos := far
    goat_pos := far
}


-- \* Farmer can only bring cabbage if and only if goat and wolf are separated
-- FarmerAndCabbage == /\ passengers["goat"] /= passengers["wolf"]
--                     /\ farmer = passengers["cabbage"]
--                     /\ IF farmer = "far" THEN /\ farmer' = "near"
--                                            /\ passengers' = [passengers EXCEPT !["cabbage"] = "near"]
--                                       ELSE /\ farmer' = "far"
--                                            /\ passengers' = [passengers EXCEPT !["cabbage"] = "far"]
action FarmerAndCabbage {
  require ¬(goat_pos == wolf_pos)
  require farmer_pos == cabbage_pos
  if farmer_pos == far then
    farmer_pos := near
    cabbage_pos := near
  else
    farmer_pos := far
    cabbage_pos := far
}

-- \* Farmer can also drive across the river alone
-- FarmerAlone == /\ IF farmer = "far" THEN farmer' = "near" ELSE farmer' = "far"
--                /\ UNCHANGED passengers
action FarmerAlone {
  if farmer_pos == far then
    farmer_pos := near
  else
    farmer_pos := far
}
-- Next == \/ FarmerAndWolf
--         \/ FarmerAndGoat
--         \/ FarmerAndCabbage
--         \/ FarmerAlone

-- \* Since the goal is to find the way relocating passengers to the far bank,
-- \* we need to catch the trace where farmer and all passengers are at the far bank.
-- \* To make TLC reports this as an error, we can put invariants in all situations, BUT
-- \* a condition where they are all located at the far bank.
-- NotAllFar == \/ /\ \E p \in DOMAIN passengers : passengers[p] = "far"
--                 /\ farmer = "near"
--              \/ /\ \E p \in DOMAIN passengers : passengers[p] = "near"
--                 /\ farmer = "far"
--              \/ /\ \A p \in DOMAIN passengers : passengers[p] = "near"
--                 /\ farmer = "near"
invariant [NotAllFar] ¬ ((wolf_pos == far) ∧ (goat_pos == far) ∧ (cabbage_pos == far) ∧ (farmer_pos == far))

#gen_spec
#check_invariants



-- #exit
-- a syntax for filling sort arguments
open Lean Meta Elab Command Veil in
scoped elab "⌞? " t:term " ⌟" : term => do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  Term.elabTerm (← `(term| $t $(← mod.sortIdents)*)) none

section

veil_variables

omit χ χ_rep χ_rep_lawful

open Veil

variable [FinEnum position] [Hashable position]

def instFinEnumForComponents (f : State.Label)
  : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    infer_instance_for_iterated_prod

instance instDecidableEqForComponents' (f : State.Label)
  : DecidableEq (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
    infer_instance

instance instDecidableEqForComponents'' (f : State.Label)
  : DecidableEq (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance

instance instHashableForComponents (f : State.Label)
  : Hashable (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
    infer_instance

instance instHashableForComponents' (f : State.Label)
  : Hashable (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance


abbrev FieldConcreteType (f : State.Label) : Type :=
  match f with
  | State.Label.wolf_pos => ((⌞? State.Label.toCodomain ⌟) State.Label.wolf_pos)
  | State.Label.goat_pos => ((⌞? State.Label.toCodomain ⌟) State.Label.goat_pos)
  | State.Label.cabbage_pos => ((⌞? State.Label.toCodomain ⌟) State.Label.cabbage_pos)
  | State.Label.farmer_pos => ((⌞? State.Label.toCodomain ⌟) State.Label.farmer_pos)


instance instReprForComponents [Repr position] (f : State.Label)
  : Repr ((⌞? FieldConcreteType ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', FieldConcreteType, State.Label.toDomain, State.Label.toCodomain] <;>
    infer_instance

instance : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟)) := by
  constructor ; constructor <;>
  dsimp only [FieldConcreteType, State.Label.toCodomain] <;>
  exact default

instance rep (f : State.Label) : FieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f) :=
  by cases f <;>
    dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] <;>
    infer_instance

instance lawful (f : State.Label) : LawfulFieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f)
  ((⌞? rep ⌟) f) :=
  by cases f <;>
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id] <;>
  infer_instance

end

attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet]
  instFinEnumForComponents in
#specialize_nextact with FieldConcreteType
  injection_begin
  [FinEnum position] [Hashable position]
  injection_end => NextAct'

#gen_executable_list! log_entry_being Std.Format
  targeting NextAct'
  injection_begin
  [FinEnum position] [Hashable position]
  injection_end


-- simple_deriving_repr_for' State
-- deriving instance Repr for Label
-- deriving instance Inhabited for Theory


-- inductive position where
--       | near
--       | far
--       deriving DecidableEq, Repr, Inhabited, Nonempty

-- instance : RiverCrossing.position_Enum position
--         where
--       near := position.near
--       far := position.far
--       position_distinct := (by
--         (first | decide | grind))
--       position_complete := (by
--       intro x
--       cases x <;>
--       (first | decide | grind))


-- instance :FinEnum position :=
--     FinEnum.ofList [position.near, position.far]
--     (by simp; exact RiverCrossing.position_Enum.position_complete)


deriving_enum_instance_for position


instance : Hashable position where
  hash c := hash c.toCtorIdx

#Concretize position


instance : BEq (FieldConcreteType position State.Label.wolf_pos) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  infer_instance

instance : Hashable (FieldConcreteType position State.Label.wolf_pos) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  infer_instance

instance : BEq (FieldConcreteType position State.Label.cabbage_pos) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  infer_instance

instance : Hashable (FieldConcreteType position State.Label.cabbage_pos) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  infer_instance

instance : BEq (FieldConcreteType position State.Label.goat_pos) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  infer_instance

instance : Hashable (FieldConcreteType position State.Label.goat_pos) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  infer_instance

instance : BEq (FieldConcreteType position State.Label.farmer_pos) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  infer_instance

instance : Hashable (FieldConcreteType position State.Label.farmer_pos) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  infer_instance

#assembleInsts

instance : (rd : TheoryConcrete) → (st : StateConcrete) → Decidable ((fun ρ σ => NotAllFar ρ σ) rd st) := by
  intro rd st
  dsimp [NotAllFar, FieldConcreteType, State.Label.toDomain, State.Label.toCodomain]
  infer_instance

simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory


def view := fun (st : StateConcrete) => hash st

def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => NotAllFar ρ σ) {} id).snd
#time #eval modelCheckerResult'
#html createExpandedGraphDisplay (collectTrace modelCheckerResult').1 (collectTrace modelCheckerResult').2


end RiverCrossing
