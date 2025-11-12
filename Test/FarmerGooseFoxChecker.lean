import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main

import Veil.Core.Tools.Checker.Concrete.modelCheckerView
import ProofWidgets.Component.HtmlDisplay
-- -------------------------- MODULE FarmerGooseFox  --------------------------
-- Source: https://gitlab.com/hhan31/rivercrossing-tla/-/blob/main/FarmerGooseFox.tla?ref_type=heads

veil module FarmerGooseFox



individual Here : Bool
individual There : Bool
individual farmer : Bool
individual beans : Bool
individual goose : Bool
individual fox : Bool

#gen_state

ghost relation Safe :=
  (goose == farmer) || (goose ≠ fox && goose ≠ beans)

after_init {
  Here := false
  There := true
  farmer := Here
  beans := Here
  goose := Here
  fox := Here
}

action Alone  {
  require (goose == farmer) || (goose ≠ fox && goose ≠ beans)
  -- require Safe
  farmer := !farmer
}

action Withbeans {
  require (goose == farmer) || (goose ≠ fox && goose ≠ beans)
  require farmer = beans
  farmer := !farmer
  beans := !beans
}

action Withgoose {
  require (goose == farmer) || (goose ≠ fox && goose ≠ beans)
  require farmer == goose
  farmer := !farmer
  goose := !goose
}

action Withfox {
  require (goose == farmer) || (goose ≠ fox && goose ≠ beans)
  require farmer = fox
  farmer := !farmer
  fox := !fox
}

invariant [Unsolved] ¬ (farmer = There ∧ beans = There ∧ goose = There ∧ fox = There)
termination [test] ¬ (farmer = There ∧ beans = There ∧ goose = There ∧ fox = There)

#gen_spec


section

veil_variables

omit χ χ_rep χ_rep_lawful

open Veil Extract

deriving_FinOrdToJson_Domain

specify_FieldConcreteType

deriving_BEq_FieldConcreteType

deriving_Hashable_FieldConcreteType

deriving_rep_FieldRepresentation

deriving_lawful_FieldRepresentation

deriving_Inhabited_State

deriving_Decidable_Props

end

gen_NextAct

gen_executable_NextAct


#Concretize

deriving_BEqHashable_ConcreteState
-- deriving instance Inhabited for Theory

-- a syntax for filling sort arguments
-- open Lean Meta Elab Command Veil in
-- scoped elab "⌞? " t:term " ⌟" : term => do
--   let lenv ← localEnv.get
--   let some mod := lenv.currentModule | throwError s!"Not in a module"
--   Term.elabTerm (← `(term| $t $(← mod.sortIdents)*)) none


-- @[derivedInvSimp, invSimp, reducible]
-- def Invariants (ρ : Type) (σ : Type) (χ : State.Label → Type)
--     [χ_rep : ∀ f, Veil.FieldRepresentation (State.Label.toDomain f) (State.Label.toCodomain f) (χ f)]
--     [χ_rep_lawful :
--       ∀ f, Veil.LawfulFieldRepresentation (State.Label.toDomain f) (State.Label.toCodomain f) (χ f) (χ_rep f)]
--     [σ_sub : IsSubStateOf @State χ σ] [ρ_sub : IsSubReaderOf @Theory ρ] (rd : ρ) (st : σ) : Prop :=
--   @Unsolved ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub rd st

-- #time #check_invariants
-- #exit
-- section
-- veil_variables

-- omit χ χ_rep χ_rep_lawful

-- open Veil

-- variable [FinEnum node] [Hashable node]
-- -- variable [insta : DecidableRel tot.le] -- [∀ a b c, Decidable (btwn.btw a b c)]

-- def instFinEnumForComponents (f : State.Label)
--   : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     infer_instance_for_iterated_prod

-- instance instDecidableEqForComponents' (f : State.Label)
--   : DecidableEq (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
--     infer_instance

-- instance instDecidableEqForComponents'' (f : State.Label)
--   : DecidableEq (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd', State.Label.toDomain] <;>
--     infer_instance

-- instance instHashableForComponents (f : State.Label)
--   : Hashable (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
--     infer_instance

-- instance instHashableForComponents' (f : State.Label)
--   : Hashable (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd', State.Label.toDomain] <;>
--     infer_instance


-- -- need to use `abbrev` to allow typeclass inference
-- abbrev FieldConcreteType (f : State.Label) : Type :=
--   match f with
--   | State.Label.Here => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.Here)
--   | State.Label.There => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.There)
--   | State.Label.farmer => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.farmer)
--   | State.Label.beans => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.beans)
--   | State.Label.goose => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.goose)
--   | State.Label.fox => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.fox)

-- instance instReprForComponents (f : State.Label)
--   : Repr ((⌞? FieldConcreteType ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd, IteratedProd', List.foldr, FieldConcreteType, State.Label.toDomain] <;>
--     infer_instance

-- -- #simp [FieldConcreteType, State.Label.toDomain, State.Label.toCodomain] FieldConcreteType Nat .leader
--   -- Veil.CanonicalField (State.Label.toDomain Nat .pending) (State.Label.toCodomain Nat .pending)

-- instance : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟)) := by
--   constructor ; constructor <;> exact default

-- instance rep (f : State.Label) : FieldRepresentation
--   ((⌞? State.Label.toDomain ⌟) f)
--   ((⌞? State.Label.toCodomain ⌟) f)
--   ((⌞? FieldConcreteType ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
--   match f with
--   | State.Label.Here =>
--     instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.Here)
--   | State.Label.There =>
--     instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.There)
--   | State.Label.farmer =>
--     instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.farmer)
--   | State.Label.beans =>
--     instFinsetLikeAsFieldRep (IteratedProd'.equiv) (( ⌞? instFinEnumForComponents ⌟) State.Label.beans)
--   | State.Label.goose =>
--     instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.goose)
--   | State.Label.fox =>
--     instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.fox)

-- instance lawful (f : State.Label) : LawfulFieldRepresentation
--   ((⌞? State.Label.toDomain ⌟) f)
--   ((⌞? State.Label.toCodomain ⌟) f)
--   ((⌞? FieldConcreteType ⌟) f)
--   ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
--   match f with
--   | State.Label.Here =>
--     instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.Here)
--   | State.Label.There =>
--     instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.There)
--   | State.Label.farmer =>
--     instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.farmer)
--   | State.Label.beans =>
--     instFinsetLikeLawfulFieldRep (IteratedProd'.equiv   ) ((⌞? instFinEnumForComponents ⌟) State.Label.beans)
--   | State.Label.goose =>
--     instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.goose)
--   | State.Label.fox =>
--     instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.fox)

-- end

-- -- code optimization by controlled `dsimp`
-- -- set_option trace.Compiler.result true in
-- attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet]
--   instFinEnumForComponents in
-- -- attribute [local dsimpFieldRepresentationGet] FourNodes.equiv_IteratedProd in
-- #specialize_nextact with FieldConcreteType
--   injection_begin injection_end => NextAct'

-- #gen_executable_list! log_entry_being Std.Format
--   targeting NextAct'
--   injection_begin  injection_end


-- simple_deriving_repr_for' State
-- deriving instance Repr for Label
-- deriving instance Inhabited for Theory

-- instance [Hashable α] [BEq α] : Hashable (Std.HashSet α) where
--   hash s :=
--     /- `Hash collision `-/
--     s.fold (init := 0) fun acc a => acc + (hash a)

-- #Concretize
-- #assembleInsts

-- instance : (rd : TheoryConcrete) → (st : StateConcrete) → Decidable ((fun ρ σ => Unsolved ρ σ) rd st) :=
--   by
--   intro rd st
--   dsimp [Unsolved]
--   dsimp [FieldConcreteType, State.Label.toDomain, State.Label.toCodomain]
--   infer_instance



-- def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => Unsolved ρ σ) ((fun ρ σ => true)) {} id).snd
-- #time #eval modelCheckerResult'
-- #html createExpandedGraphDisplay (collectTrace modelCheckerResult').1 (collectTrace modelCheckerResult').2

-- simple_deriving_repr_for' State
deriving instance Repr for Label
-- deriving instance Inhabited for Theory

deriving_toJson_for_state


def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => Unsolved ρ σ) ((fun ρ σ => true)) {} hash).snd


def statesJson : Lean.Json :=
  Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM {} (collectTrace' modelCheckerResult'))
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />




end FarmerGooseFox
