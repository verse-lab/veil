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


-- https://github.com/aman-goel/ivybench/blob/d2c9298fdd099001c71a34bc2e118db6f07d8404/multisig/ivy/multisig-all.ivy


veil module MultiSigAll

type validator
type destination
type value
type deadline
type signature

relation holding : validator → Bool
relation collect : validator → destination → value → deadline → Bool

relation sig : validator → destination → value → deadline → signature → Bool
relation sig_auth : signature → Bool

relation proposed : validator → destination → value → deadline → Bool
relation paid : validator → destination → value → deadline → Bool
relation cancelled : validator → destination → value → deadline → Bool

relation expired : deadline → Bool

#gen_state

after_init {
  holding N := true;
  collect N K V D := false;

  proposed N K V D := false;
  paid N K V D := false;
  cancelled N K V D := false;

  sig N K V D S := false
}

action propose (n: validator) (k: destination) (v: value) (d: deadline) {
  require holding n;
  require ¬ collect n k v d;
  require ¬ paid n k v d;
  holding n := false;
  collect n k v d := true;
  sig n k v d S := false;
  proposed n k v d := true
}

action add_sig (n: validator) (k: destination) (v: value) (d: deadline) (s: signature) {
  require ¬ expired d;
  require sig_auth s;
  sig n k v d s := true
}

action pay (n: validator) (k: destination) (v: value) (d: deadline) {
  require collect n k v d;
  require ¬ expired d;
  require ∀ S, sig n k v d S;
  paid n k v d := true;
  holding n := true;
  collect n k v d := false
}

action cancel (n: validator) (k: destination) (v: value) (d: deadline) {
  require collect n k v d;
  require expired d;
  cancelled n k v d := true;
  holding n := true;
  collect n k v d := false
}

action expire (d: deadline) {
  expired d := true
}

safety [cancelled_after_deadline] cancelled N K V D → expired D
safety [paid_if_enough_sigs] paid N K V D → (∀ s, sig N K V D s ∧ sig_auth s)
safety [paid_imp_proposed] paid N K V D → proposed N K V D

invariant [ic3po_global2] collect V1 D1 V2 D2 → proposed V1 D1 V2 D2
invariant [ic3po_global3] sig V1 D1 V2 D2 S1 → sig_auth S1

#gen_spec

set_option maxHeartbeats 0
set_option maxRecDepth 10000

unsat trace [solver_old_4] {
  any 4 actions
  assert (∃ n k v d, paid n k v d)
} by
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "MultiSigAll_old_4"
  sorry

unsat trace [solver_early_4] {
  any 4 actions
  assert (∃ n k v d, paid n k v d)
} by
  veil_intros
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "MultiSigAll_early_4"
  sorry

unsat trace [solver_old_8] {
  any 8 actions
  assert (∃ n k v d, paid n k v d)
} by
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "MultiSigAll_old_8"
  sorry

unsat trace [solver_early_8] {
  any 8 actions
  assert (∃ n k v d, paid n k v d)
} by
  veil_intros
  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  check_solver_outcome "MultiSigAll_early_8"
  sorry

end MultiSigAll
