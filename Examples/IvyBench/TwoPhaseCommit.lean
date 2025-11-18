import Veil
-- import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main
-- https://github.com/aman-goel/ivybench/blob/master/i4/ivy/two_phase_commit.ivy

veil module TwoPhaseCommit


type node
enum thread = {T1, T2, T3}

relation vote_yes : node -> Bool
relation vote_no : node -> Bool
relation alive : node -> Bool
relation go_commit : node -> Bool
relation go_abort : node -> Bool
relation decide_commit : node -> Bool
relation decide_abort : node -> Bool

individual abort_flag : Bool

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
  -- require go_commit n;
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

-- set_option veil.smt.solver "cvc5" in
#check_invariants

-- sat trace [initial_state] {} by { bmc_sat }

-- sat trace { } by { bmc_sat }

-- sat trace {
--   vote1
--   vote1
--   go1
--   commit
-- } by { bmc_sat }

-- unsat trace {
--   any 6 actions
--   assert ¬ ((decide_commit N → ¬decide_abort N2) ∧ (decide_commit N -> vote_yes N2) ∧ (decide_abort N → abort_flag))
-- } by { bmc }

#gen_exec
#finitizeTypes thread, thread
def view (st : StateConcrete) := hash st
def detect_prop : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => safety_0 ρ σ)
def terminationC : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => true)
def cfg : TheoryConcrete := {}

def modelCheckerResult' :=(runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (detect_prop) (terminationC) cfg view).snd
-- #eval modelCheckerResult'.seen.size
def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM cfg (collectTrace' modelCheckerResult'))
#eval statesJson
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />




end TwoPhaseCommit
