import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main
-- -------------------------- MODULE FarmerGooseFox  --------------------------
-- Source: https://gitlab.com/hhan31/rivercrossing-tla/-/blob/main/FarmerGooseFox.tla?ref_type=heads

veil module FarmerGooseFox

-- type a

relation Here : Bool
relation There : Bool
relation farmer : Bool
relation beans : Bool
relation goose : Bool
relation fox : Bool

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
#gen_spec

-- a syntax for filling sort arguments
open Lean Meta Elab Command Veil in
scoped elab "⌞? " t:term " ⌟" : term => do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  Term.elabTerm (← `(term| $t $(← mod.sortIdents)*)) none

-- #time #check_invariants
section

veil_variables

omit χ χ_rep χ_rep_lawful

open Veil

variable [FinEnum node] [Hashable node]
-- variable [insta : DecidableRel tot.le] -- [∀ a b c, Decidable (btwn.btw a b c)]

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


-- need to use `abbrev` to allow typeclass inference
abbrev FieldConcreteType (f : State.Label) : Type :=
  match f with
  | State.Label.Here => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.Here)
  | State.Label.There => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.There)
  | State.Label.farmer => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.farmer)
  | State.Label.beans => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.beans)
  | State.Label.goose => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.goose)
  | State.Label.fox => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.fox)

instance instReprForComponents (f : State.Label)
  : Repr ((⌞? FieldConcreteType ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, IteratedProd', List.foldr, FieldConcreteType, State.Label.toDomain] <;>
    infer_instance

-- #simp [FieldConcreteType, State.Label.toDomain, State.Label.toCodomain] FieldConcreteType Nat .leader
  -- Veil.CanonicalField (State.Label.toDomain Nat .pending) (State.Label.toCodomain Nat .pending)

instance : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟)) := by
  constructor ; constructor <;> exact default

instance rep (f : State.Label) : FieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.Here =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.Here)
  | State.Label.There =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.There)
  | State.Label.farmer =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.farmer)
  | State.Label.beans =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) (( ⌞? instFinEnumForComponents ⌟) State.Label.beans)
  | State.Label.goose =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.goose)
  | State.Label.fox =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.fox)

instance lawful (f : State.Label) : LawfulFieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f)
  ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.Here =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.Here)
  | State.Label.There =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.There)
  | State.Label.farmer =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.farmer)
  | State.Label.beans =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv   ) ((⌞? instFinEnumForComponents ⌟) State.Label.beans)
  | State.Label.goose =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.goose)
  | State.Label.fox =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.fox)

end

-- code optimization by controlled `dsimp`
-- set_option trace.Compiler.result true in
attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet]
  instFinEnumForComponents in
-- attribute [local dsimpFieldRepresentationGet] FourNodes.equiv_IteratedProd in
#specialize_nextact with FieldConcreteType
  injection_begin injection_end => NextAct'

#gen_executable_list! log_entry_being Std.Format
  targeting NextAct'
  injection_begin  injection_end


simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory

instance [Hashable α] [BEq α] : Hashable (Std.HashSet α) where
  hash s :=
    /- `Hash collision `-/
    s.fold (init := 0) fun acc a => acc + (hash a)

#Concretize
#assembleInsts

instance : (rd : TheoryConcrete) → (st : StateConcrete) → Decidable ((fun ρ σ => Unsolved ρ σ) rd st) :=
  by
  intro rd st
  dsimp [Unsolved]
  dsimp [FieldConcreteType, State.Label.toDomain, State.Label.toCodomain]
  infer_instance


def modelCheckerResult' := (runModelCheckerx {} labelList initVeilMultiExecM nextVeilMultiExecM (fun ρ σ => Unsolved ρ σ)).snd
#eval modelCheckerResult'
#html createExpandedGraphDisplay (collectTrace modelCheckerResult').1 (collectTrace modelCheckerResult').2

end FarmerGooseFox
