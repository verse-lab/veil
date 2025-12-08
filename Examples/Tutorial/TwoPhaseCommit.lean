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
  -- require ∃n, vote_yes n
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


safety (decide_commit N → ¬decide_abort N2)
      ∧ (decide_commit N -> vote_yes N2)
      ∧ (decide_abort N → abort_flag)
invariant [manual_1] ¬alive N → abort_flag
invariant [manual_2] vote_no N → abort_flag
invariant [manual_3] go_abort N → abort_flag
invariant [manual_4] (decide_abort N ∧ vote_yes N) → go_abort N
invariant [manual_5] decide_commit N → go_commit N
invariant [manual_6] (N0 ≠ N1) -> ¬((¬(go_commit N0) ∧ go_commit N1))
invariant [manual_7] go_commit N → vote_yes N
invariant [manual_8] go_abort N → ¬go_commit N

#gen_spec

#check_invariants

#gen_exec

/- Concretize the abstract types using finite concrete types.
Here we concretize the `node` type using `Fin 2`

Here, `< 5` is safe. Otherwise you can not get the result immediately
when show this case.
-/
#finitize_types (Fin 6)

/- Set the immutable declarations for the model checker, here we do not have any.-/
#set_theory {}


/- How can we introduce bugs? Possible way:
1. Replace line 60 `require ∀ N, vote_yes N;` with line 61 `require ∃n, vote_yes n`.
Then the property `manual_7` will be violated.

2. Comment out line 68 `∃n, vote_yes n`, `manual_3` will be violated.

3. Comment out `manual_1`, `maunual_2`, `manual_3` invariants, suppose we do not
have these lemma invariants currently.
Then the safety property can not be verified successfully.
`#check_invariants` will report the violated of `manual_7` and `safety`.
But after checking these two props, we find that they are valid, which may
indicate that we are missing some necessary invariants.

-/

#run_checker (fun a b => true)
-- #eval modelCheckerResult.seen.size
#eval spaceSize modelCheckerResult
-- #eval statesJson
-- open ProofWidgets
-- open scoped ProofWidgets.Jsx
-- #html <ModelCheckerView trace={statesJson} layout={"vertical"} />


end TwoPhaseCommit
