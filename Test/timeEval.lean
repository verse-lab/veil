import Veil
import Veil.Core.Tools.Checker.Concrete.Main

-- https://github.com/aman-goel/ivybench/blob/master/i4/ivy/two_phase_commit.ivy

veil module TwoPhaseCommit


type node

relation vote_yes : node -> Bool
relation vote_no : node -> Bool
relation alive : node -> Bool
relation go_commit : node -> Bool
relation go_abort : node -> Bool
relation decide_commit : node -> Bool
relation decide_abort : node -> Bool
individual abort_flag : Bool

veil_set_option useFieldRepTC false
#gen_state


after_init {
  vote_yes N := false;
  vote_no N := false;
  alive N := true;
  go_commit N := false;
  go_abort N := false;
  decide_commit N := false;
  decide_abort N := false;
  abort_flag := false
}

action vote1 (n : node) {
  require alive n;
  require ¬vote_no n;
  require ¬decide_commit n;
  require ¬decide_abort n;
  vote_yes n := true
}

action vote2(n: node) {
  require alive n;
  require ¬vote_yes n;
  require ¬decide_commit n;
  require ¬decide_abort n;
  vote_no n := true;
  abort_flag := true;
  decide_abort n := true
}

action fail(n: node) {
  require alive n;
  alive n := false;
  abort_flag := true
}

action go1 {
  require ∀ N, ¬go_commit N;
  require ∀ N, ¬go_abort N;
  require ∀ N, vote_yes N;
  go_commit N := true
}

action go2 {
  require ∀ N, ¬go_commit N;
  require ∀ N, ¬go_abort N;
  require exists n, vote_no n ∨ ¬alive n;
  go_abort N := true
}

action commit(n: node) {
  require alive n;
  require go_commit n;
  decide_commit n := true
}

action abort(n: node) {
  require alive n;
  require go_abort n;
  decide_abort n := true
}


safety (decide_commit N → ¬decide_abort N2) ∧ (decide_commit N -> vote_yes N2) ∧ (decide_abort N → abort_flag)
invariant [manual_1] ¬((¬(alive N) ∧ ¬(abort_flag)))
invariant [manual_2] ¬((¬(abort_flag) ∧ vote_no N))
invariant [manual_3] ¬((¬(abort_flag) ∧ go_abort N))
invariant [manual_4] ¬((¬(go_abort N) ∧ decide_abort N ∧ vote_yes N))
invariant [manual_5] ¬((¬(go_commit N) ∧ decide_commit N))
invariant [manual_6] (N0 ≠ N1) -> ¬((¬(go_commit N0) ∧ go_commit N1))
invariant [manual_7] ¬((¬(vote_yes N) ∧ go_commit N))
invariant [manual_8] ¬((go_commit N ∧ go_abort N))

#gen_spec

-- #check_invariants

simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory

#print NextAct

#gen_executable_list!log_entry_being Std.Format targeting NextAct
injection_begin
injection_end


deriving_Enum_Insts
#Concretize_without_FieldTy (Fin 3)
/-
Store the whole state during checking:

number (N) | states   | time(ms)
-----------|----------|----------
 2         | 116      | 617
 3         | 1064     | 6146
 4         | 10256    | 464044
 5         | 101024   | > 20mins

number (N) | states   | time(ms)
-----------|----------|----------
 2         | 116      | 922
 3         | 1064     | 1477
 4         | 10256    | 8328
 5         | 101024   | 83139
-/
set_option trace.veil.debug true
deriving_BEq_ConcreteState
deriving_DecidableProps_state


instance : Hashable StateConcrete where
  hash s := hash ""

def view (st : StateConcrete) := st
@[reducible]
def detect_prop : TheoryConcrete → StateConcrete → Prop := (fun ρ σ => safety_0 ρ σ)
@[reducible]
def terminationC : TheoryConcrete → StateConcrete → Prop := (fun ρ σ => true)
def cfg : TheoryConcrete := {}


def modelCheckerResult' :=(runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (detect_prop) (terminationC) cfg view).snd
#time #eval modelCheckerResult'.seen.size
#exit
def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM cfg (collectTrace' modelCheckerResult'))
-- #eval statesJson
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />



end TwoPhaseCommit
