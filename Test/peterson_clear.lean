import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main

import Veil.Core.Tools.Checker.Concrete.modelCheckerView
import ProofWidgets.Component.HtmlDisplay
veil module Peterson
-- ------------------------------- MODULE Peterson -------------------------------
-- (*****************************************************************************)
-- (* This module contains the specification for Peterson's Algorithm, taken    *)
-- (* from the "Parallel Programming" course taught at ULiège.                  *)
-- (* The invariant `Inv` is the one presented in the course augmented by a     *)
-- (* clause representing mutual exclusion of the critical section              *)
-- (* A proof is given to show that `Inv` is inductive.                         *)
-- (* Moreover the refinement from Peterson to the abstract lock is also proven.*)
-- (*****************************************************************************)

-- EXTENDS Integers, TLAPS

-- Other(p) == IF p = 1 THEN 2 ELSE 1

-- (*
-- --algorithm Peterson{
--     variables
--       c = [self \in ProcSet |-> FALSE],
--       turn = 1;

--     process(proc \in 1..2){
-- a0:   while(TRUE){
--         skip;
-- a1:     c[self] := TRUE;
-- a2:     turn := Other(self);
-- a3:     await ~c[Other(self)] \/ turn = self;
-- cs:     skip;
-- a4:     c[self] := FALSE;
--       }
--     }
-- }
-- *)
enum pc_state = { a0, a1, a2, a3, cs, a4 }
enum process = { P1, P2 }

individual turn : process
relation c : process → Bool
relation pc : process → pc_state → Bool
#gen_state


after_init  {
  c P := false
  turn := *
  pc P S := decide $ S = a0

}

action evtA0 (self : process)  {
  require pc self a0
  pc self S := decide $ S = a1
}

#print evtA0.do

action evtA1 (self : process)  {
  require pc self a1
  c self := true
  pc self S := decide $ S = a2
}

action evtA2 (self : process)  {
  require pc self a2
  turn := if self = P1 then P2 else P1
  pc self S := decide $ S = a3
}


action evtA3 (self : process)  {
  require pc self a3
  require ¬ c (if self = P1 then P2 else P1) ∨ turn = self
  pc self S := decide $ S = cs
}


action evtCS (self : process) {
  require pc self cs
  pc self S := decide $ S = a4
}

action evtA4 (self : process) {
  require pc self a4
  c self := false
  -- pc self S := decide $ S = a0
  pc self S := decide $ S = a4   -- Introduce an error here
}


invariant [pc_total] pc P a0 ∨ pc P a1 ∨ pc P a2 ∨ pc P a3 ∨ pc P cs ∨ pc P a4
invariant [unique_pc] pc P S ∧ pc P T → S = T

invariant [Inv_P1]
  ∀p, c p ↔ (pc p a2 ∨ pc p a3 ∨ pc p cs ∨ pc p a4)

ghost relation lockcs (i : process) := pc i cs ∨ pc i a4

invariant [Inv_P2]
  ∀p, (pc p cs ∨ pc p a4) →
  (turn = p ∨
    (pc (if p = P1 then P2 else P1) a0 ∨
     pc (if p = P1 then P2 else P1) a1 ∨
     pc (if p = P1 then P2 else P1) a2))

invariant [Inv_P3]
  ∀ i j, i ≠ j → ¬((pc i cs ∨ pc i a4) ∧ (pc j cs ∨ pc j a4))


#gen_spec


section

veil_variables

-- omit χ χ_rep χ_rep_lawful

deriving_FinOrdToJson_Domain

specify_FieldConcreteType

deriving_BEq_FieldConcreteType

deriving_Hashable_FieldConcreteType

deriving_rep_FieldRepresentation

deriving_lawful_FieldRepresentation

deriving_Inhabited_State

deriving_Decidable_Props

end

gen_nextAct

gen_executable_NextAct

deriving_enum_instance_for process

deriving_enum_instance_for pc_state

instance : Ord process where
  compare s1 s2 :=
    compare (s1.toCtorIdx) (s2.toCtorIdx)

instance : Ord pc_state where
  compare s1 s2 :=
    compare (s1.toCtorIdx) (s2.toCtorIdx)


instance : Hashable pc_state where
  hash s := hash s.toCtorIdx

instance : Hashable process where
  hash s := hash s.toCtorIdx



instance : Std.ReflCmp (Ord.compare (self := inferInstanceAs (Ord pc_state))) := by
  apply Std.ReflCmp.mk
  unfold compare
  intro a; cases a <;> rfl

instance : Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord pc_state))):= by
  apply Std.LawfulEqCmp.mk
  unfold compare inferInstanceAs instOrdPc_state
  intro a b; cases a <;>
    cases b <;> simp

instance : Std.ReflCmp (Ord.compare (self := inferInstanceAs (Ord process))) := by
  apply Std.ReflCmp.mk
  unfold compare
  intro a; cases a <;> rfl

instance : Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process))):= by
  apply Std.LawfulEqCmp.mk
  unfold compare inferInstanceAs instOrdProcess
  intro a b; cases a <;>
    cases b <;> simp


instance :  Std.OrientedCmp (Ord.compare (self := inferInstanceAs (Ord pc_state))) := by
  apply Std.OrientedCmp.mk
  unfold compare inferInstanceAs instOrdPc_state
  intro a b; cases a <;>
    cases b <;> rfl


instance : Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord pc_state))) := by
  apply Std.TransCmp.mk
  unfold compare inferInstanceAs instOrdPc_state pc_state.toCtorIdx
  decide

instance : Std.OrientedCmp (Ord.compare (self := inferInstanceAs (Ord process))) := by
  apply Std.OrientedCmp.mk
  unfold compare inferInstanceAs instOrdProcess
  intro a b; cases a <;>
    cases b <;> rfl

instance : Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process))) := by
  apply Std.TransCmp.mk
  unfold compare inferInstanceAs instOrdProcess
  decide

#Concretize pc_state, process


#assembleInsts


simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory


def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => Inv_P2 ρ σ) ((fun ρ σ => true)) {} hash).snd

deriving_toJson_for_state

open Lean

def statesJson : Json :=
  toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM {} (collectTrace' modelCheckerResult'))

#check statesJson

#eval statesJson
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />


end Peterson
