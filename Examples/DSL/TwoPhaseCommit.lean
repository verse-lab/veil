import LeanSts.DSL

-- https://github.com/aman-goel/ivybench/blob/master/i4/ivy/two_phase_commit.ivy

section TwoPhaseCommit

type node
instantiate dec : DecidableEq node

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
  vote_yes _ := False;
  vote_no _ := False;
  alive _ := True;
  go_commit _ := False;
  go_abort _ := False;
  decide_commit _ := False;
  decide_abort _ := False;
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
  require ¬go_commit N;
  require ¬go_abort N;
  require vote_yes N;
  go_commit N := True
}

action go2 = {
  require ¬go_commit N;
  require ¬go_abort N;
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

#gen_spec TPC

sat trace [initial_state] {} by { simp [initSimp, actSimp] }

unsat trace {
  any 6 actions
  assert ¬ ((decide_commit N → ¬decide_abort N2) ∧ (decide_commit N -> vote_yes N2) ∧ (decide_abort N → abort_flag))
} by { bmc }

end TwoPhaseCommit
