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


-- https://github.com/aman-goel/ivybench/blob/d2c9298fdd099001c71a34bc2e118db6f07d8404/distai/ivy/Ricart-Agrawala.ivy


veil module RicartAgrawala

type node

relation requested (n1 : node) (n2 : node)
relation replied (n1 : node) (n2 : node)
relation holds (n : node)

#gen_state

after_init {
  requested N1 N2 := false;
  replied N1 N2 := false;
  holds N := false
}

action request (requester: node) (responder : node) {
  require ¬ requested requester responder;
  require requester ≠ responder;
  requested requester responder := true
}

action reply (requester: node) (responder: node) {
    require ¬ replied requester responder;
    require ¬ holds responder;
    require ¬ replied responder requester;
    require requested requester responder;
    require requester ≠ responder;
    requested requester responder := false;
    replied requester responder := true
}

action enter (requester: node) {
  require ∀ N, (N ≠ requester) → replied requester N;
  holds requester := true
}

action leave (requester : node) {
  require holds requester;
  holds requester := false;
  replied requester N := false
}

safety [mutual_exclusion] (holds N1 ∧ holds N2) → N1 = N2
invariant N1 ≠ N2 → ¬(replied N1 N2 ∧ replied N2 N1)
invariant (N1 ≠ N2 ∧  holds N1) → replied N1 N2

#gen_spec

set_option maxHeartbeats 0
set_option maxRecDepth 10000

unsat trace [solver_old_4] {
  any 4 actions
  assert (∃ n, holds n)
} by
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "RicartAgrawala_old_4"
  sorry

unsat trace [solver_early_4] {
  any 4 actions
  assert (∃ n, holds n)
} by
  veil_intros
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "RicartAgrawala_early_4"
  sorry

unsat trace [solver_old_8] {
  any 8 actions
  assert (∃ n, holds n)
} by
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "RicartAgrawala_old_8"
  sorry

unsat trace [solver_early_8] {
  any 8 actions
  assert (∃ n, holds n)
} by
  veil_intros
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "RicartAgrawala_early_8"
  sorry

end RicartAgrawala
