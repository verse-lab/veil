import Veil.DSL

-- https://github.com/aman-goel/ivybench/blob/master/i4/ivy/two_phase_commit.ivy

namespace TwoPhaseCommit
open Classical

type node

relation vote_yes : node -> Prop
relation vote_no : node -> Prop
relation alive : node -> Prop
relation go_commit : node -> Prop
relation go_abort : node -> Prop
relation decide_commit : node -> Prop
relation decide_abort : node -> Prop

individual abort_flag : Prop

#gen_state

after_init {
  vote_yes N := False;
  vote_no N := False;
  alive N := True;
  go_commit N := False;
  go_abort N := False;
  decide_commit N := False;
  decide_abort N := False;
  abort_flag := False
}

action vote1 (n : node) = {
  require alive n;
  require ¬vote_no n;
  require ¬decide_commit n;
  require ¬decide_abort n;
  vote_yes n := True
}

action vote2(n: node) = {
  require alive n;
  require ¬vote_yes n;
  require ¬decide_commit n;
  require ¬decide_abort n;
  vote_no n := True;
  abort_flag := True;
  decide_abort n := True
}

action fail(n: node) = {
  require alive n;
  alive n := False;
  abort_flag := True
}

action go1 = {
  require ∀ N, ¬go_commit N;
  require ∀ N, ¬go_abort N;
  require ∀ N, vote_yes N;
  go_commit N := True
}

action go2 = {
  require ∀ N, ¬go_commit N;
  require ∀ N, ¬go_abort N;
  require exists n, vote_no n ∨ ¬alive n;
  go_abort N := True
}

action commit(n: node) = {
  require alive n;
  require go_commit n;
  decide_commit n := True
}

action abort(n: node) = {
  require alive n;
  require go_abort n;
  decide_abort n := True
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

set_option sauto.smt.solver "cvc5" in
#time #check_invariants_wlp

sat trace [initial_state] {} by { bmc_sat }

sat trace { } by { bmc_sat }

sat trace {
  vote1
  vote1
  go1
  commit
} by { bmc_sat }

set_option maxHeartbeats 2000000 in
unsat trace {
  any 6 actions
  assert ¬ ((decide_commit N → ¬decide_abort N2) ∧ (decide_commit N -> vote_yes N2) ∧ (decide_abort N → abort_flag))
} by { bmc }

end TwoPhaseCommit
