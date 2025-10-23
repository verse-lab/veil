import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main

veil module DieHard

-- ------------------------------ MODULE DieHard -------------------------------
-- (***************************************************************************)
-- (* In the movie Die Hard 3, the heroes must obtain exactly 4 gallons of     *)
-- (* water using a 5 gallon jug, a 3 gallon jug, and a water faucet.  Our    *)
-- (* goal: to get TLC to solve the problem for us.                           *)
-- (*                                                                         *)
-- (* First, we write a spec that describes all allowable behaviors of our    *)
-- (* heroes.                                                                  *)
-- (***************************************************************************)
-- EXTENDS Naturals
--   (*************************************************************************)
--   (* This statement imports the definitions of the ordinary operators on   *)
--   (* Natural numbers, such as +.                                           *)
--   (*************************************************************************)

-- (***************************************************************************)
-- (* We next declare the specification's variables.                          *)
-- (***************************************************************************)
-- VARIABLES big,   \* The number of gallons of water in the 5 gallon jug.
--           small  \* The number of gallons of water in the 3 gallon jug.

individual big : Nat
individual tmp : Nat
individual small : Nat
-- (***************************************************************************)
-- (* We now define TypeOK to be the type invariant, asserting that the value *)
-- (* of each variable is an element of the appropriate set.  A type          *)
-- (* invariant like this is not part of the specification, but it's          *)
-- (* generally a good idea to include it because it helps the reader         *)
-- (* understand the spec.  Moreover, having TLC check that it is an          *)
-- (* invariant of the spec catches errors that, in a typed language, are     *)
-- (* caught by type checking.                                                *)
-- (*                                                                         *)
-- (* Note: TLA+ uses the convention that a list of formulas bulleted by /\   *)
-- (* or \/ denotes the conjunction or disjunction of those formulas.         *)
-- (* Indentation of subitems is significant, allowing one to elimiNate lots  *)
-- (* of parentheses.  This makes a large formula much easier to read.        *)
-- (* However, it does mean that you have to be careful with your indentation.*)
-- (***************************************************************************)
#gen_state

after_init {
  -- (big : Nat) := 0
  -- (small : Nat) := 0
  -- (tmp : Nat) := 0
  big := 0
  small := 0
  tmp := 0
}
-- (***************************************************************************)
-- (* Now we define the actions that our hero can perform.  There are three    *)
-- (* things they can do:                                                     *)
-- (*                                                                         *)
-- (*   - Pour water from the faucet into a jug.                              *)
-- (*                                                                         *)
-- (*   - Pour water from a jug onto the ground.                              *)
-- (*                                                                         *)
-- (*   - Pour water from one jug into another                                *)
-- (*                                                                         *)
-- (* We now consider the first two.  Since the jugs are not calibrated,       *)
-- (* partially filling or partially emptying a jug accomplishes nothing.      *)
-- (* So, the first two possibilities yield the following four possible        *)
-- (* actions.                                                                *)
-- (***************************************************************************)

-- FillSmallJug  == /\ small' = 3
--                  /\ big' = big
set_option trace.veil.debug true
action FillSmallJug {
  -- (small : Nat) := 3
  small := 3
  big := big
}

-- FillBigJug    == /\ big' = 5
--                  /\ small' = small
action FillBigJug  {
  -- (big : Nat) := 5
  -- (small : Nat) := small
  big := 5
  small := small
}

-- EmptySmallJug == /\ small' = 0
--                  /\ big' = big
action EmptySmallJug {
  -- (small : Nat) := 0
  small := 0
  big := big
}

-- EmptyBigJug   == /\ big' = 0
--                  /\ small' = small
action EmptyBigJug {
  -- (big : Nat) := 0
  big := 0
  small := small
}

-- SmallToBig == /\ big'   = Min(big + small, 5)
--               /\ small' = small - (big' - big)
action SmallToBig {
  -- (tmp : Nat) := big
  -- (big : Nat) := if big + small  < 5 then big + small else 5
  -- (small : Nat) := small - (big - tmp)
  tmp := big
  big := if big + small < 5 then big + small else 5
  small := small - (big - tmp)
}

-- BigToSmall == /\ small' = Min(big + small, 3)
--               /\ big'   = big - (small' - small)
action BigToSmall {
  -- (tmp : Nat) := small
  -- (small : Nat) := if big + small < 3 then big + small else 3
  -- (big : Nat) := big - (small - tmp)
  tmp := small
  small := if big + small < 3 then big + small else 3
  big := big - (small - tmp)
}


-- TypeOK == /\ small \in 0..3
--           /\ big   \in 0..5
invariant [typeOK] small≤ 3 ∧ big ≤ 5

-- NotSolved == big # 4
invariant [not_solved] big ≠ 4

#gen_spec

-- a syntax for filling sort arguments
open Lean Meta Elab Command Veil in
scoped elab "⌞? " t:term " ⌟" : term => do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  Term.elabTerm (← `(term| $t $(← mod.sortIdents)*)) none

#time #check_invariants
section

veil_variables

omit χ χ_rep χ_rep_lawful

open Veil


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
  | State.Label.big => ((⌞? State.Label.toCodomain ⌟) State.Label.big)
  | State.Label.tmp => ((⌞? State.Label.toCodomain ⌟) State.Label.tmp)
  | State.Label.small => ((⌞? State.Label.toCodomain ⌟) State.Label.small)

instance instReprForComponents (f : State.Label)
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
  ((⌞? FieldConcreteType ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.big => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.tmp => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.small => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance


instance lawful (f : State.Label) : LawfulFieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f)
  ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.big => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.tmp => by
    dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
    infer_instance
  | State.Label.small => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance

end

attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet]
  instFinEnumForComponents in
#specialize_nextact with FieldConcreteType
  injection_begin
  injection_end => NextAct'

#gen_executable_list! log_entry_being Std.Format
  targeting NextAct'
  injection_begin
  injection_end

#Concretize

instance : BEq (FieldConcreteType State.Label.big) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  infer_instance

instance : Hashable (FieldConcreteType State.Label.big) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  infer_instance

instance : BEq (FieldConcreteType State.Label.tmp) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  infer_instance

instance : Hashable (FieldConcreteType State.Label.tmp) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  infer_instance

instance : BEq (FieldConcreteType State.Label.small) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  infer_instance

instance : Hashable (FieldConcreteType State.Label.small) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
  infer_instance

#assembleInsts

instance : (rd : TheoryConcrete) → (st : StateConcrete) → Decidable ((fun ρ σ => not_solved ρ σ) rd st) := by
  intro rd st
  dsimp [not_solved, FieldConcreteType, State.Label.toDomain, State.Label.toCodomain]
  infer_instance

simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory

def modelCheckerResult' := (runModelCheckerx {} labelList initVeilMultiExecM nextVeilMultiExecM (fun ρ σ => not_solved ρ σ)).snd
#eval modelCheckerResult'


def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => not_solved ρ σ) { }).snd
#eval modelCheckerResult'.seen.length
#html createExpandedGraphDisplay (collectTrace modelCheckerResult').1 (collectTrace modelCheckerResult').2


end DieHard
