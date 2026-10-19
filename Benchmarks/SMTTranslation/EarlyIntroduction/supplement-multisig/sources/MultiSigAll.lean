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
  IO.FS.withFile "/tmp/veil-early-intro-multi/supplement-multisig/events/MultiSigAll.log" .append fun h => h.putStrLn s

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

elab "bench_preproc_complete " key:str : tactic => benchPrint s!"PREPROCESS_COMPLETE {key.getString}"

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
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

unsat trace [bench_early_16_1] {
  any 16 actions
  assert (∃ n k v d, paid n k v d)
} by
  bench_run "MultiSigAll_early_16_1" "/tmp/veil-early-intro-multi/supplement-multisig/markers/MultiSigAll_early" (
    bench_stage "MultiSigAll_early_16_1" "early_intros" intro_data_prefix
    bench_stage "MultiSigAll_early_16_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "MultiSigAll_early_16_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "MultiSigAll_early_16_1" "intros" veil_intros
    bench_stage "MultiSigAll_early_16_1" "destruct" veil_destruct
    bench_stage "MultiSigAll_early_16_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "MultiSigAll_early_16_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "MultiSigAll_early_16_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_preproc_complete "MultiSigAll_early_16_1"
    bench_smt_pipeline "MultiSigAll_early_16_1" "/tmp/veil-early-intro-multi/supplement-multisig/queries/MultiSigAll_early_16_1.smt2"
  )

unsat trace [bench_early_32_1] {
  any 32 actions
  assert (∃ n k v d, paid n k v d)
} by
  bench_run "MultiSigAll_early_32_1" "/tmp/veil-early-intro-multi/supplement-multisig/markers/MultiSigAll_early" (
    bench_stage "MultiSigAll_early_32_1" "early_intros" intro_data_prefix
    bench_stage "MultiSigAll_early_32_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "MultiSigAll_early_32_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "MultiSigAll_early_32_1" "intros" veil_intros
    bench_stage "MultiSigAll_early_32_1" "destruct" veil_destruct
    bench_stage "MultiSigAll_early_32_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "MultiSigAll_early_32_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "MultiSigAll_early_32_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_preproc_complete "MultiSigAll_early_32_1"
    bench_smt_pipeline "MultiSigAll_early_32_1" "/tmp/veil-early-intro-multi/supplement-multisig/queries/MultiSigAll_early_32_1.smt2"
  )

end MultiSigAll
