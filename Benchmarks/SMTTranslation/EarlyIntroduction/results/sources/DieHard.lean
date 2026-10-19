module

public import Veil

open Lean Elab Tactic Meta Veil

meta partial def introDataPrefix (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let .forallE _ domain _ _ := target.consumeMData | return goal
  if ← isProp domain then return goal
  let (_, goal') ← withOptions (fun opts => opts.setBool `tactic.hygienic false) goal.intro1
  introDataPrefix goal'

elab "intro_data_prefix" : tactic => do
  liftMetaTactic1 fun goal => return some (← introDataPrefix goal)


meta def benchPrint (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

elab "bench_stage " key:str label:str t:tactic : tactic => do
  let start ← IO.monoMsNow
  try
    evalTactic t
    benchPrint s!"STAGE {key.getString} {label.getString} ms={(← IO.monoMsNow)-start}"
  catch ex =>
    benchPrint s!"FAILED {key.getString} {label.getString} ms={(← IO.monoMsNow)-start}: {← ex.toMessageData.toString}"
    throw ex

elab "bench_run " label:str marker:str t:tactic : tactic => do
  if ← System.FilePath.pathExists marker.getString then
    benchPrint s!"RUN_SKIPPED {label.getString} prior_failure"
    evalTactic (← `(tactic| sorry))
  else
    benchPrint s!"RUN_BEGIN {label.getString}"
    let saved ← saveState
    try
      evalTactic t
      benchPrint s!"RUN_COMPLETE {label.getString}"
    catch _ =>
      saved.restore
      IO.FS.writeFile marker.getString "failed"
      benchPrint s!"RUN_FAILED {label.getString}"
    evalTactic (← `(tactic| sorry))

elab "bench_smt_pipeline " key:str path:str : tactic => do
  let saved ← saveState
  try
    withMainContext do
      let hs := (← getFVarIds (← Veil.getPropsInContext)).map Expr.fvar
      let goal ← getMainGoal
      let mut mv := (← Meta.mkFreshExprMVar (← goal.getType)).mvarId!
      mv ← mv.cleanup (← hs.foldlM (fun s h => return (← (Expr.collectFVars h).run s).snd) {}).fvarIds
      let mut hs := hs
      let steps : Array (String × (MVarId → Array Expr → MetaM Smt.Preprocess.Result)) := #[
        ("pushHints", Smt.Preprocess.pushHintsToCtx),
        ("smt-intros", Smt.Preprocess.intros),
        ("negateGoal", Smt.Preprocess.negateGoal),
        ("normalize", Smt.Preprocess.normalize),
        ("embedding", Smt.Preprocess.embeddingWithConfig { embedBool := false })]
      for (name, step) in steps do
        let start ← IO.monoMsNow
        let r ← mv.withContext <| step mv hs
        mv := r.mv
        hs := r.hs
        benchPrint s!"SMT_STAGE {key.getString} {name} ms={(← IO.monoMsNow)-start}"
      let start ← IO.monoMsNow
      let cmds ← mv.withContext do
        let (fvNames, _) ← Smt.genUniqueFVarNames
        Smt.prepareSmtQuery hs.toList fvNames
      benchPrint s!"SMT_STAGE {key.getString} translate ms={(← IO.monoMsNow)-start} commands={cmds.length}"
      let start ← IO.monoMsNow
      let query := Smt.Translate.Command.cmdsAsQuery (.setLogic "ALL" :: cmds ++ [.checkSat])
      IO.FS.writeFile path.getString query
      benchPrint s!"SMT_STAGE {key.getString} serialize ms={(← IO.monoMsNow)-start} bytes={query.utf8ByteSize}"
      benchPrint s!"PIPELINE_COMPLETE {key.getString}"
  catch ex =>
    benchPrint s!"PIPELINE_FAILED {key.getString}: {← ex.toMessageData.toString}"
  saved.restore



veil module DieHard

individual big : Nat
individual small : Nat

#gen_state

after_init {
  big := 0
  small := 0
}


action FillSmallJug {
  small := 3
  big := big
}


action FillBigJug  {
  big := 5
  small := small
}


action EmptySmallJug {
  small := 0
  big := big
}


action EmptyBigJug {
  big := 0
  small := small
}


action SmallToBig {
  let tmp := big
  big := if big + small < 5 then big + small else 5
  small := small - (big - tmp)
}



action BigToSmall {
  let tmp := small
  small := if big + small < 3 then big + small else 3
  big := big - (small - tmp)
}


invariant [typeOK] small≤ 3 ∧ big ≤ 5
invariant [not_solved] big ≠ 4
termination big > 0

#gen_spec
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

unsat trace [bench_current_2_1] {
  any 2 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_2_1" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_2_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_2_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_2_1" "intros" veil_intros
    bench_stage "DieHard_current_2_1" "destruct" veil_destruct
    bench_stage "DieHard_current_2_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_2_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_2_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "DieHard_current_2_1" "/tmp/veil-early-intro-multi/results/queries/DieHard_current_2_1.smt2"
  )

unsat trace [bench_early_2_1] {
  any 2 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_2_1" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_2_1" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_2_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_2_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_2_1" "intros" veil_intros
    bench_stage "DieHard_early_2_1" "destruct" veil_destruct
    bench_stage "DieHard_early_2_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_2_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_2_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "DieHard_early_2_1" "/tmp/veil-early-intro-multi/results/queries/DieHard_early_2_1.smt2"
  )

unsat trace [bench_early_2_2] {
  any 2 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_2_2" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_2_2" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_2_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_2_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_2_2" "intros" veil_intros
    bench_stage "DieHard_early_2_2" "destruct" veil_destruct
    bench_stage "DieHard_early_2_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_2_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_2_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_2_2] {
  any 2 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_2_2" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_2_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_2_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_2_2" "intros" veil_intros
    bench_stage "DieHard_current_2_2" "destruct" veil_destruct
    bench_stage "DieHard_current_2_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_2_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_2_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_2_3] {
  any 2 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_2_3" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_2_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_2_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_2_3" "intros" veil_intros
    bench_stage "DieHard_current_2_3" "destruct" veil_destruct
    bench_stage "DieHard_current_2_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_2_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_2_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_2_3] {
  any 2 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_2_3" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_2_3" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_2_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_2_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_2_3" "intros" veil_intros
    bench_stage "DieHard_early_2_3" "destruct" veil_destruct
    bench_stage "DieHard_early_2_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_2_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_2_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_4_1] {
  any 4 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_4_1" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_4_1" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_4_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_4_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_4_1" "intros" veil_intros
    bench_stage "DieHard_early_4_1" "destruct" veil_destruct
    bench_stage "DieHard_early_4_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_4_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_4_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "DieHard_early_4_1" "/tmp/veil-early-intro-multi/results/queries/DieHard_early_4_1.smt2"
  )

unsat trace [bench_current_4_1] {
  any 4 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_4_1" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_4_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_4_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_4_1" "intros" veil_intros
    bench_stage "DieHard_current_4_1" "destruct" veil_destruct
    bench_stage "DieHard_current_4_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_4_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_4_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "DieHard_current_4_1" "/tmp/veil-early-intro-multi/results/queries/DieHard_current_4_1.smt2"
  )

unsat trace [bench_current_4_2] {
  any 4 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_4_2" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_4_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_4_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_4_2" "intros" veil_intros
    bench_stage "DieHard_current_4_2" "destruct" veil_destruct
    bench_stage "DieHard_current_4_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_4_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_4_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_4_2] {
  any 4 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_4_2" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_4_2" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_4_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_4_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_4_2" "intros" veil_intros
    bench_stage "DieHard_early_4_2" "destruct" veil_destruct
    bench_stage "DieHard_early_4_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_4_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_4_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_4_3] {
  any 4 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_4_3" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_4_3" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_4_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_4_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_4_3" "intros" veil_intros
    bench_stage "DieHard_early_4_3" "destruct" veil_destruct
    bench_stage "DieHard_early_4_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_4_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_4_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_4_3] {
  any 4 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_4_3" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_4_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_4_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_4_3" "intros" veil_intros
    bench_stage "DieHard_current_4_3" "destruct" veil_destruct
    bench_stage "DieHard_current_4_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_4_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_4_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_8_1] {
  any 8 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_8_1" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_8_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_8_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_8_1" "intros" veil_intros
    bench_stage "DieHard_current_8_1" "destruct" veil_destruct
    bench_stage "DieHard_current_8_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_8_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_8_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "DieHard_current_8_1" "/tmp/veil-early-intro-multi/results/queries/DieHard_current_8_1.smt2"
  )

unsat trace [bench_early_8_1] {
  any 8 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_8_1" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_8_1" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_8_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_8_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_8_1" "intros" veil_intros
    bench_stage "DieHard_early_8_1" "destruct" veil_destruct
    bench_stage "DieHard_early_8_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_8_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_8_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "DieHard_early_8_1" "/tmp/veil-early-intro-multi/results/queries/DieHard_early_8_1.smt2"
  )

unsat trace [bench_early_8_2] {
  any 8 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_8_2" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_8_2" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_8_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_8_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_8_2" "intros" veil_intros
    bench_stage "DieHard_early_8_2" "destruct" veil_destruct
    bench_stage "DieHard_early_8_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_8_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_8_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_8_2] {
  any 8 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_8_2" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_8_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_8_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_8_2" "intros" veil_intros
    bench_stage "DieHard_current_8_2" "destruct" veil_destruct
    bench_stage "DieHard_current_8_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_8_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_8_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_8_3] {
  any 8 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_8_3" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_8_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_8_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_8_3" "intros" veil_intros
    bench_stage "DieHard_current_8_3" "destruct" veil_destruct
    bench_stage "DieHard_current_8_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_8_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_8_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_8_3] {
  any 8 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_8_3" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_8_3" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_8_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_8_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_8_3" "intros" veil_intros
    bench_stage "DieHard_early_8_3" "destruct" veil_destruct
    bench_stage "DieHard_early_8_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_8_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_8_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_16_1] {
  any 16 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_16_1" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_16_1" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_16_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_16_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_16_1" "intros" veil_intros
    bench_stage "DieHard_early_16_1" "destruct" veil_destruct
    bench_stage "DieHard_early_16_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_16_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_16_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "DieHard_early_16_1" "/tmp/veil-early-intro-multi/results/queries/DieHard_early_16_1.smt2"
  )

unsat trace [bench_current_16_1] {
  any 16 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_16_1" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_16_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_16_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_16_1" "intros" veil_intros
    bench_stage "DieHard_current_16_1" "destruct" veil_destruct
    bench_stage "DieHard_current_16_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_16_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_16_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "DieHard_current_16_1" "/tmp/veil-early-intro-multi/results/queries/DieHard_current_16_1.smt2"
  )

unsat trace [bench_current_16_2] {
  any 16 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_16_2" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_16_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_16_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_16_2" "intros" veil_intros
    bench_stage "DieHard_current_16_2" "destruct" veil_destruct
    bench_stage "DieHard_current_16_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_16_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_16_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_16_2] {
  any 16 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_16_2" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_16_2" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_16_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_16_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_16_2" "intros" veil_intros
    bench_stage "DieHard_early_16_2" "destruct" veil_destruct
    bench_stage "DieHard_early_16_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_16_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_16_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_16_3] {
  any 16 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_16_3" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_16_3" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_16_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_16_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_16_3" "intros" veil_intros
    bench_stage "DieHard_early_16_3" "destruct" veil_destruct
    bench_stage "DieHard_early_16_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_16_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_16_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_16_3] {
  any 16 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_16_3" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_16_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_16_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_16_3" "intros" veil_intros
    bench_stage "DieHard_current_16_3" "destruct" veil_destruct
    bench_stage "DieHard_current_16_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_16_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_16_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_32_1] {
  any 32 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_32_1" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_32_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_32_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_32_1" "intros" veil_intros
    bench_stage "DieHard_current_32_1" "destruct" veil_destruct
    bench_stage "DieHard_current_32_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_32_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_32_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "DieHard_current_32_1" "/tmp/veil-early-intro-multi/results/queries/DieHard_current_32_1.smt2"
  )

unsat trace [bench_early_32_1] {
  any 32 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_32_1" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_32_1" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_32_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_32_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_32_1" "intros" veil_intros
    bench_stage "DieHard_early_32_1" "destruct" veil_destruct
    bench_stage "DieHard_early_32_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_32_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_32_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_smt_pipeline "DieHard_early_32_1" "/tmp/veil-early-intro-multi/results/queries/DieHard_early_32_1.smt2"
  )

unsat trace [bench_early_32_2] {
  any 32 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_32_2" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_32_2" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_32_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_32_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_32_2" "intros" veil_intros
    bench_stage "DieHard_early_32_2" "destruct" veil_destruct
    bench_stage "DieHard_early_32_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_32_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_32_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_32_2] {
  any 32 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_32_2" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_32_2" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_32_2" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_32_2" "intros" veil_intros
    bench_stage "DieHard_current_32_2" "destruct" veil_destruct
    bench_stage "DieHard_current_32_2" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_32_2" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_32_2" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_current_32_3] {
  any 32 actions
  assert (big = 4)
} by
  bench_run "DieHard_current_32_3" "/tmp/veil-early-intro-multi/results/markers/DieHard_current" (
    bench_stage "DieHard_current_32_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_current_32_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_current_32_3" "intros" veil_intros
    bench_stage "DieHard_current_32_3" "destruct" veil_destruct
    bench_stage "DieHard_current_32_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_current_32_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_current_32_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

unsat trace [bench_early_32_3] {
  any 32 actions
  assert (big = 4)
} by
  bench_run "DieHard_early_32_3" "/tmp/veil-early-intro-multi/results/markers/DieHard_early" (
    bench_stage "DieHard_early_32_3" "early_intros" intro_data_prefix
    bench_stage "DieHard_early_32_3" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "DieHard_early_32_3" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "DieHard_early_32_3" "intros" veil_intros
    bench_stage "DieHard_early_32_3" "destruct" veil_destruct
    bench_stage "DieHard_early_32_3" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "DieHard_early_32_3" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "DieHard_early_32_3" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )

end DieHard
