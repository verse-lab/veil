import Veil
import Veil.Core.Tools.Checker.Concrete.Main
-- ------------------------------ MODULE Prisoners -----------------------------
veil module Prisoners
-- (***************************************************************************)
-- (* This module specifies the solution to the following puzzle, given on    *)
-- (* the Car Guys NPR radio show:                                            *)
-- (*                                                                         *)
-- (*    The warden of a prison gives his prisoners the following problem.    *)
-- (*    There is a room in the prison with two switches, labeled A and B.    *)
-- (*    Each switch can be either up or down.  Every so often, the warden    *)
-- (*    will select a prisoner at random and take him into the room, where   *)
-- (*    he must flip (change the position of) exactly one of the switches.   *)
-- (*    The only guarantee he makes is that every prisoner will eventually   *)
-- (*    be brought into the room multiple times.  (More precisely, there     *)
-- (*    will never be a time after which some prisoner is never again        *)
-- (*    brought into the room.)                                              *)
-- (*                                                                         *)
-- (*    At any time, any prisoner may declare that all the prisoners have    *)
-- (*    been in the room at least once.  If that prisoner is right, then     *)
-- (*    all the prisoners go free.  If he is wrong, all the prisoners are    *)
-- (*    immediately executed.                                                *)
-- (*                                                                         *)
-- (*    The prisoners are allowed to decide upon a strategy, after which     *)
-- (*    they will not be allowed to communicate with one another.  And, of   *)
-- (*    course, they cannot see the room or who is being brought into it.    *)
-- (*    What do they do?                                                     *)
-- (*                                                                         *)
-- (* The solution presented by the Car Guys is specified below.              *)
-- (***************************************************************************)
-- EXTENDS Naturals, FiniteSets

-- CONSTANTS
--   Prisoner,
--     (***********************************************************************)
--     (* The set of all prisoners.                                           *)
--     (***********************************************************************)
-- enum prisoner = {P1, P2, P3, P4, P5, P6}
type prisoner

immutable individual cardPrisoner : Nat

individual switchAUp : Bool
individual switchBUp : Bool

function timesSwitched : prisoner → Nat

individual count : Nat

veil_set_option useFieldRepTC false
#gen_state


after_init {
  switchAUp := false;
  switchBUp := false;
  timesSwitched P := 0;
  count := 0
}

action NonCounterStep (i : prisoner) {
  -- require i == P1; -- Assume P1 is the Counter
  if  (!switchAUp) ∧ (timesSwitched i < 2) then
    switchAUp := true;
    timesSwitched i := timesSwitched i + 1
  else
    switchBUp := !switchBUp
}


action CounterStep {
  -- require i == P1; -- Assume P1 is the Counter
  if switchAUp then
    switchAUp := false;
    count := count + 1
  else
    switchBUp := !switchBUp
}


invariant [timesSwitchedlessEqual2] timesSwitched P ≤ 2
invariant [countBounded] count ≤ 2 * (cardPrisoner - 1)


#gen_spec

-- #gen_exec

-- -- #finitizeTypes prisoner
-- #finitizeTypes (Fin 7)

/-
1: TwoPhaseCommit
number (N) | states   | time(functional State)   | time(Concrete State)
-----------|----------|-------------------------------------------------
 2         | 116      | 617                      | 922
 3         | 1064     | 6146                     | 1477
 4         | 10256    | 464044                   | 8328
 5         | 101024   | > 20mins                 | 83139


2: Prisoner
number (N) | states   | time(functional State)  | time(Concrete State)
-----------|----------|-------------------------------------------------
 3         | 106      | 135                     | 330
 4         | 322      | 322                     | 198
 5         | 970      | 1552                    | 468
 6         | 2954     | 21092                   | 753
 7         | 8746     | 232457                  | 2292
-/


simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory

#print NextAct

#gen_executable_list!log_entry_being Std.Format targeting NextAct
injection_begin
injection_end


deriving_Enum_Insts
#Concretize_without_FieldTy (Fin 7)
deriving_BEq_ConcreteState
deriving_DecidableProps_state
/-
number (N) | states   | time(ms)
-----------|----------|----------
 3         | 106      | 135
 4         | 322      | 322
 5         | 970      | 1552
 6         | 2954     | 21092
 7         | 8746     | 232457
-/

instance : Hashable StateConcrete where
  hash s := hash ""

def view (st : StateConcrete) := st
@[reducible]
def detect_prop : TheoryConcrete → StateConcrete → Prop := (fun ρ σ => timesSwitchedlessEqual2 ρ σ)
@[reducible]
def terminationC : TheoryConcrete → StateConcrete → Prop := (fun ρ σ => true)
def cfg : TheoryConcrete := {cardPrisoner := 7}


def modelCheckerResult' :=(runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (detect_prop) (terminationC) cfg view).snd
-- #time #eval modelCheckerResult'.seen.size
#exit
def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM cfg (collectTrace' modelCheckerResult'))
-- #eval statesJson
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />

end Prisoners
