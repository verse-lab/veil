module

public import Veil

open Lean Elab Tactic Meta Veil
elab "check_solver_outcome " label:str : tactic => withMainContext do
  let start ← IO.monoMsNow
  try
    let hs := (← getFVarIds (← Veil.getPropsInContext)).map Expr.fvar
    let original ← getMainGoal
    let mut mv := (← Meta.mkFreshExprMVar (← original.getType)).mvarId!
    mv ← mv.cleanup (← hs.foldlM (fun s h => return (← (Expr.collectFVars h).run s).snd) {}).fvarIds
    let steps := #[Smt.Preprocess.pushHintsToCtx, Smt.Preprocess.intros, Smt.Preprocess.negateGoal,
      Smt.Preprocess.normalize, Smt.Preprocess.embeddingWithConfig { embedBool := false }]
    let ⟨_, hs, normalizedGoal⟩ ← mv.withContext <| Smt.Preprocess.applySteps mv hs steps
    let cmds ← normalizedGoal.withContext do
      let (fvNames, _) ← Smt.genUniqueFVarNames
      Smt.prepareSmtQuery hs.toList fvNames
    let cmds := Smt.Translate.Command.setLogic "ALL" :: cmds
    let query := Smt.Translate.Command.cmdsAsQuery cmds
    let path := "/tmp/veil-early-intro-multi/" ++ label.getString ++ ".smt2"
    IO.FS.writeFile path (Smt.Translate.Command.cmdsAsQuery (cmds ++ [.checkSat]))
    let prepared ← IO.monoMsNow
    let options := Smt.defaultSolverOptions ++ [("finite-model-find", "true"),
      ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
    let result ← Smt.solve query (some 10) false options
    let status := match result with
      | .ok (.sat _) => "sat"
      | .ok (.unsat _ _) => "unsat"
      | .ok (.unknown reason) => "unknown:" ++ reason.toString
      | .error err => "error:" ++ err.toString
    IO.println s!"SOLVER_RESULT {label.getString} status={status} solver_ms={(← IO.monoMsNow)-prepared} smt_prep_ms={prepared-start} bytes={query.utf8ByteSize}"
  catch ex =>
    IO.println s!"SOLVER_FAILURE {label.getString}: {← ex.toMessageData.toString}"
    throw ex


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
invariant [manual_1] ¬((¬(alive N) ∧ ¬(abort_flag)))
invariant [manual_2] ¬((¬(abort_flag) ∧ vote_no N))
invariant [manual_3] ¬((¬(abort_flag) ∧ go_abort N))
invariant [manual_4] ¬((¬(go_abort N) ∧ decide_abort N ∧ vote_yes N))
invariant [manual_5] ¬((¬(go_commit N) ∧ decide_commit N))
invariant [manual_6] (N0 ≠ N1) -> ¬((¬(go_commit N0) ∧ go_commit N1))
invariant [manual_7] ¬((¬(vote_yes N) ∧ go_commit N))
invariant [manual_8] ¬((go_commit N ∧ go_abort N))

#gen_spec

set_option maxHeartbeats 0
set_option maxRecDepth 10000

unsat trace [solver_old_4] {
  any 4 actions
  assert (∃ n, decide_commit n)
} by
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "TwoPhaseCommit_old_4"
  sorry

unsat trace [solver_early_4] {
  any 4 actions
  assert (∃ n, decide_commit n)
} by
  veil_intros
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "TwoPhaseCommit_early_4"
  sorry

unsat trace [solver_old_8] {
  any 8 actions
  assert (∃ n, decide_commit n)
} by
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "TwoPhaseCommit_old_8"
  sorry

unsat trace [solver_early_8] {
  any 8 actions
  assert (∃ n, decide_commit n)
} by
  veil_intros
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "TwoPhaseCommit_early_8"
  sorry

end TwoPhaseCommit
