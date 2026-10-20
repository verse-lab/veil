module

public import Veil

set_option Elab.async false
section

open Lean Elab Tactic Meta Veil

meta def symbolicBenchEvent (event phase status : String) (elapsed : Nat := 0)
    (extra : List (String × Json) := []) : CoreM Unit := do
  let j := Json.mkObj ([
    ("event", toJson event), ("phase", toJson phase), ("status", toJson status),
    ("elapsed_ms", toJson elapsed), ("mono_ms", toJson (← IO.monoMsNow))] ++ extra)
  IO.FS.withFile (System.FilePath.mk ((← getOptions).get `symbolicBench.eventPath "")) .append fun h => h.putStrLn j.compress

meta partial def symbolicBenchIntroData (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let .forallE _ domain _ _ := target.consumeMData | return goal
  if ← isProp domain then return goal
  let (_, next) ← withOptions (fun opts => opts.setBool `tactic.hygienic false) goal.intro1
  symbolicBenchIntroData next

elab "symbolic_bench_intro_data" : tactic => do
  liftMetaTactic1 fun goal => return some (← symbolicBenchIntroData goal)

elab "symbolic_bench_phase " label:str t:tactic : tactic => do
  if (← getGoals).isEmpty then
    symbolicBenchEvent "stage" label.getString "skipped_goal_closed"
  else
    symbolicBenchEvent "stage" label.getString "begin"
    let start ← IO.monoMsNow
    let hbStart ← IO.getNumHeartbeats
    try
      withoutRecover <| evalTactic t
      symbolicBenchEvent "stage" label.getString "complete" ((← IO.monoMsNow) - start)
        [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart))]
    catch ex =>
      symbolicBenchEvent "stage" label.getString "failed" ((← IO.monoMsNow) - start)
        [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart)), ("error", toJson (← ex.toMessageData.toString))]
      throw ex

meta def symbolicBenchMetaPhase {α : Type} (label : String) (computation : MetaM α) : MetaM α := do
  symbolicBenchEvent "stage" label "begin"
  let start ← IO.monoMsNow
  let hbStart ← IO.getNumHeartbeats
  try
    let value ← computation
    symbolicBenchEvent "stage" label "complete" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart))]
    return value
  catch ex =>
    symbolicBenchEvent "stage" label "failed" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart)), ("error", toJson (← ex.toMessageData.toString))]
    throw ex

meta def symbolicBenchTacticPhase {α : Type} (label : String) (computation : TacticM α) : TacticM α := do
  symbolicBenchEvent "stage" label "begin"
  let start ← IO.monoMsNow
  let hbStart ← IO.getNumHeartbeats
  try
    let value ← computation
    symbolicBenchEvent "stage" label "complete" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart))]
    return value
  catch ex =>
    symbolicBenchEvent "stage" label "failed" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart)), ("error", toJson (← ex.toMessageData.toString))]
    throw ex

elab "symbolic_bench_extract " eventPath:str path:str t:tactic : tactic => do
  withOptions (fun opts => opts.set `symbolicBench.eventPath eventPath.getString) do
    symbolicBenchEvent "pipeline" "pipeline" "begin" 0 [
      ("maxHeartbeats", toJson (maxHeartbeats.get (← getOptions))),
      ("maxRecDepth", toJson (maxRecDepth.get (← getOptions)))]
    let start ← IO.monoMsNow
    withoutRecover <| evalTactic t
    symbolicBenchEvent "milestone" "preprocessing" "complete" ((← IO.monoMsNow) - start)
    if (← getGoals).isEmpty then
      symbolicBenchEvent "pipeline" "pipeline" "discharged" ((← IO.monoMsNow) - start)
    else
      Veil.withBackwardsCompatibility <| withMainContext do
        let (mv, hs) ← symbolicBenchTacticPhase "cleanup" do
          let hs := (← getFVarIds (← Veil.getPropsInContext)).map Expr.fvar
          let goal ← getMainGoal
          let mv := (← Meta.mkFreshExprMVar (← goal.getType)).mvarId!
          let mv ← mv.cleanup (← hs.foldlM (fun s h => return (← (Expr.collectFVars h).run s).snd) {}).fvarIds
          return (mv, hs)
        let mut mv := mv
        let mut hs := hs
        let steps : Array (String × (MVarId → Array Expr → MetaM Smt.Preprocess.Result)) := #[
          ("pushHints", Smt.Preprocess.pushHintsToCtx),
          ("smt-intros", Smt.Preprocess.intros),
          ("negateGoal", Smt.Preprocess.negateGoal),
          ("normalize", Smt.Preprocess.normalize),
          ("embedding", Smt.Preprocess.embeddingWithConfig { embedBool := false })]
        for (label, step) in steps do
          let result ← symbolicBenchMetaPhase label <| mv.withContext <| step mv hs
          mv := result.mv
          hs := result.hs
        let cmds ← symbolicBenchMetaPhase "translate" <| mv.withContext do
          let (fvNames, _) ← Smt.genUniqueFVarNames
          Smt.prepareSmtQuery hs.toList fvNames
        let query ← symbolicBenchMetaPhase "serialize" do
          let query := Smt.Translate.Command.cmdsAsQuery (.setLogic "ALL" :: cmds ++ [.checkSat])
          IO.FS.writeFile path.getString query
          return query
        symbolicBenchEvent "pipeline" "pipeline" "complete" ((← IO.monoMsNow) - start)
          [("bytes", toJson query.utf8ByteSize), ("commands", toJson cmds.length)]
    -- Deliberately abandon the measurement declaration; no theorem is admitted.
    throwError "SYMBOLIC_BMC_EXTRACTION_COMPLETE: query extraction only; no proof claimed"

end

-- https://github.com/aman-goel/ivybench/blob/master/distai/ivy/blockchain.ivy

veil module Blockchain

type node
type block
type transaction
type time

instantiate tot : TotalOrder time

immutable relation leader : node → time → Bool

relation honest : node → Bool
relation broadcastable : node → block → time → Bool
relation broadcasted : node → Bool

relation block_found : node → block → time → Bool
relation block_confirmed : node → block → time → Bool

immutable relation transaction_time : transaction → time → Bool

relation transaction_in_block : transaction → block → Bool
relation transaction_confirmed : transaction → node → Bool

#gen_state

assumption leader N1 T ∧ leader N2 T → N1 = N2
assumption leader N T1 ∧ leader N T2 → T1 = T2
assumption transaction_time TR T1 ∧ transaction_time TR T2 → T1 = T2

after_init {
    block_found N B T := false;
    block_confirmed N B T := false;
    transaction_in_block TR B := false;
    transaction_confirmed TR N := false;
    broadcasted N := false;
    broadcastable N B T := false
}

action find_block (n : node) (b : block) (t: time) {
  require leader n t;
  block_found n b t := true
}

action add_transaction (tr : transaction) (b : block) {
  transaction_in_block tr b := true
}

action begin_broadcast (n : node) (b : block) (t : time) {
  require leader n t ∧ block_found n b t ∧ ¬ broadcasted n;
  broadcastable n b t := true
}

action begin_broadcast_adversary (n : node) (b : block) (t : time) {
  require ¬ honest n;
  broadcastable n b t := true
}

action byzantine_broadcast (n : node) (b : block) (t : time) {
  require broadcastable n b t;
  require ∀ TR T, honest n ∧ transaction_time TR T ∧ tot.le T t ∧ ¬ transaction_confirmed TR n → transaction_in_block TR b;
  require ∀ TR T, honest n ∧ transaction_in_block TR b → transaction_time TR T ∧ tot.le T t ∧ ¬ transaction_confirmed TR n;
  --  why doesn't `block_confirmed N B t := *` work here?
  -- let havoc <- pick
  block_confirmed N B t := *
  broadcasted n := true;
  broadcastable n b t := false;
  transaction_confirmed TR N := decide $ transaction_confirmed TR N ∨ ((transaction_in_block TR b ∧ honest n) ∨ (¬ honest n ∧ transaction_confirmed TR N))
  --
  assume ∀ N B1 B2, honest N → ¬ (B1 ≠ B2 ∧ block_confirmed N B1 t ∧ block_confirmed N B2 t);
  assume ∀ N1 N2 B, honest N1 ∧ honest N2 → (block_confirmed N1 b t ∧ block_confirmed N2 b t) ∨ (¬ block_confirmed N1 B t ∧ ¬ block_confirmed N2 B t);
  assume ∀ N, honest n ∧ honest N → block_confirmed N b t

}

action sabotage (n: node) {
    require ¬ honest n;
    block_confirmed n B T := *;
    transaction_confirmed TR n := *
}

safety
      ((honest N1 ∧ honest N2) → (block_confirmed N1 B T ∧ block_confirmed N2 B T) ∨ (¬ block_confirmed N1 B T ∧ ¬ block_confirmed N2 B T))
    ∧ ((honest N1 ∧ honest N2) → (transaction_confirmed TR N1 ∧ transaction_confirmed TR N2) ∨ (¬ transaction_confirmed TR N1 ∧ ¬ transaction_confirmed TR N2))
    ∧ ((honest N ∧ leader N T2 ∧ transaction_time TR T1 ∧ tot.le T1 T2 ∧ broadcasted N ∧ honest N1) → transaction_confirmed TR N1)


invariant block_found N1 B1 TI1  ∨ ¬ honest N1  ∨ ¬ broadcastable N1 B1 TI1
invariant leader N1 TI1  ∨ ¬ honest N1  ∨ ¬ broadcastable N1 B1 TI1
invariant leader N1 TI1  ∨ ¬ block_found N1 B1 TI1
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ honest N1  ∨ ¬ broadcastable N1 B1 TI2  ∨ ¬ block_found N1 B1 TI1)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ honest N1  ∨ ¬ broadcastable N1 B1 TI1  ∨ ¬ block_found N1 B1 TI2)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ honest N1  ∨ ¬ broadcastable N1 B1 TI1  ∨ ¬ broadcastable N1 B1 TI2)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ leader N1 TI2  ∨ ¬ honest N1  ∨ ¬ broadcastable N1 B1 TI1)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ leader N1 TI1  ∨ ¬ block_found N1 B1 TI2)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ leader N1 TI2  ∨ ¬ block_found N1 B1 TI1)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ block_found N1 B1 TI1  ∨ ¬ block_found N1 B1 TI2)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ leader N1 TI1  ∨ ¬ honest N1  ∨ ¬ broadcastable N1 B1 TI2)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ leader N1 TI1  ∨ ¬ leader N1 TI2)
invariant (tot.le TI1 TI2  ∧ TI1 ≠ TI2) -> (¬ transaction_time TR1 TI1  ∨ ¬ transaction_time TR1 TI2)


#gen_spec

run_cmd Lean.Elab.Command.liftTermElabM do
  IO.FS.writeFile "/tmp/veil-transition-local/results/batch-events/Ivy_Blockchain__default__batch1.ready" (toString (← IO.monoMsNow))

set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.finiteModelFind true

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d1__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_0] {
  any action
  assert (¬ (∀ n1 n2 n b t tr t1 t2, (((honest n1 ∧ honest n2) → ((block_confirmed n1 b t ∧ block_confirmed n2 b t) ∨ (¬ block_confirmed n1 b t ∧ ¬ block_confirmed n2 b t))) ∧ ((honest n1 ∧ honest n2) → ((transaction_confirmed tr n1 ∧ transaction_confirmed tr n2) ∨ (¬ transaction_confirmed tr n1 ∧ ¬ transaction_confirmed tr n2))) ∧ ((honest n ∧ leader n t2 ∧ transaction_time tr t1 ∧ tot.le t1 t2 ∧ broadcasted n ∧ honest n1) → transaction_confirmed tr n1))))
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d1__early__default.jsonl" "/tmp/veil-transition-local/results/queries/Ivy_Blockchain__d1__early__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d1__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_1] {
  any action
  assert (¬ (∀ n1 n2 n b t tr t1 t2, (((honest n1 ∧ honest n2) → ((block_confirmed n1 b t ∧ block_confirmed n2 b t) ∨ (¬ block_confirmed n1 b t ∧ ¬ block_confirmed n2 b t))) ∧ ((honest n1 ∧ honest n2) → ((transaction_confirmed tr n1 ∧ transaction_confirmed tr n2) ∨ (¬ transaction_confirmed tr n1 ∧ ¬ transaction_confirmed tr n2))) ∧ ((honest n ∧ leader n t2 ∧ transaction_time tr t1 ∧ tot.le t1 t2 ∧ broadcasted n ∧ honest n1) → transaction_confirmed tr n1))))
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d1__local__default.jsonl" "/tmp/veil-transition-local/results/queries/Ivy_Blockchain__d1__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_2] {
  any 2 actions
  assert (¬ (∀ n1 n2 n b t tr t1 t2, (((honest n1 ∧ honest n2) → ((block_confirmed n1 b t ∧ block_confirmed n2 b t) ∨ (¬ block_confirmed n1 b t ∧ ¬ block_confirmed n2 b t))) ∧ ((honest n1 ∧ honest n2) → ((transaction_confirmed tr n1 ∧ transaction_confirmed tr n2) ∨ (¬ transaction_confirmed tr n1 ∧ ¬ transaction_confirmed tr n2))) ∧ ((honest n ∧ leader n t2 ∧ transaction_time tr t1 ∧ tot.le t1 t2 ∧ broadcasted n ∧ honest n1) → transaction_confirmed tr n1))))
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d2__local__default.jsonl" "/tmp/veil-transition-local/results/queries/Ivy_Blockchain__d2__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d2__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_3] {
  any 2 actions
  assert (¬ (∀ n1 n2 n b t tr t1 t2, (((honest n1 ∧ honest n2) → ((block_confirmed n1 b t ∧ block_confirmed n2 b t) ∨ (¬ block_confirmed n1 b t ∧ ¬ block_confirmed n2 b t))) ∧ ((honest n1 ∧ honest n2) → ((transaction_confirmed tr n1 ∧ transaction_confirmed tr n2) ∨ (¬ transaction_confirmed tr n1 ∧ ¬ transaction_confirmed tr n2))) ∧ ((honest n ∧ leader n t2 ∧ transaction_time tr t1 ∧ tot.le t1 t2 ∧ broadcasted n ∧ honest n1) → transaction_confirmed tr n1))))
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d2__early__default.jsonl" "/tmp/veil-transition-local/results/queries/Ivy_Blockchain__d2__early__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d2__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d4__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_4] {
  any 4 actions
  assert (¬ (∀ n1 n2 n b t tr t1 t2, (((honest n1 ∧ honest n2) → ((block_confirmed n1 b t ∧ block_confirmed n2 b t) ∨ (¬ block_confirmed n1 b t ∧ ¬ block_confirmed n2 b t))) ∧ ((honest n1 ∧ honest n2) → ((transaction_confirmed tr n1 ∧ transaction_confirmed tr n2) ∨ (¬ transaction_confirmed tr n1 ∧ ¬ transaction_confirmed tr n2))) ∧ ((honest n ∧ leader n t2 ∧ transaction_time tr t1 ∧ tot.le t1 t2 ∧ broadcasted n ∧ honest n1) → transaction_confirmed tr n1))))
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d4__early__default.jsonl" "/tmp/veil-transition-local/results/queries/Ivy_Blockchain__d4__early__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d4__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_5] {
  any 4 actions
  assert (¬ (∀ n1 n2 n b t tr t1 t2, (((honest n1 ∧ honest n2) → ((block_confirmed n1 b t ∧ block_confirmed n2 b t) ∨ (¬ block_confirmed n1 b t ∧ ¬ block_confirmed n2 b t))) ∧ ((honest n1 ∧ honest n2) → ((transaction_confirmed tr n1 ∧ transaction_confirmed tr n2) ∨ (¬ transaction_confirmed tr n1 ∧ ¬ transaction_confirmed tr n2))) ∧ ((honest n ∧ leader n t2 ∧ transaction_time tr t1 ∧ tot.le t1 t2 ∧ broadcasted n ∧ honest n1) → transaction_confirmed tr n1))))
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d4__local__default.jsonl" "/tmp/veil-transition-local/results/queries/Ivy_Blockchain__d4__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_6] {
  any 8 actions
  assert (¬ (∀ n1 n2 n b t tr t1 t2, (((honest n1 ∧ honest n2) → ((block_confirmed n1 b t ∧ block_confirmed n2 b t) ∨ (¬ block_confirmed n1 b t ∧ ¬ block_confirmed n2 b t))) ∧ ((honest n1 ∧ honest n2) → ((transaction_confirmed tr n1 ∧ transaction_confirmed tr n2) ∨ (¬ transaction_confirmed tr n1 ∧ ¬ transaction_confirmed tr n2))) ∧ ((honest n ∧ leader n t2 ∧ transaction_time tr t1 ∧ tot.le t1 t2 ∧ broadcasted n ∧ honest n1) → transaction_confirmed tr n1))))
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d8__local__default.jsonl" "/tmp/veil-transition-local/results/queries/Ivy_Blockchain__d8__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d8__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_7] {
  any 8 actions
  assert (¬ (∀ n1 n2 n b t tr t1 t2, (((honest n1 ∧ honest n2) → ((block_confirmed n1 b t ∧ block_confirmed n2 b t) ∨ (¬ block_confirmed n1 b t ∧ ¬ block_confirmed n2 b t))) ∧ ((honest n1 ∧ honest n2) → ((transaction_confirmed tr n1 ∧ transaction_confirmed tr n2) ∨ (¬ transaction_confirmed tr n1 ∧ ¬ transaction_confirmed tr n2))) ∧ ((honest n ∧ leader n t2 ∧ transaction_time tr t1 ∧ tot.le t1 t2 ∧ broadcasted n ∧ honest n1) → transaction_confirmed tr n1))))
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d8__early__default.jsonl" "/tmp/veil-transition-local/results/queries/Ivy_Blockchain__d8__early__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d8__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d16__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_8] {
  any 16 actions
  assert (¬ (∀ n1 n2 n b t tr t1 t2, (((honest n1 ∧ honest n2) → ((block_confirmed n1 b t ∧ block_confirmed n2 b t) ∨ (¬ block_confirmed n1 b t ∧ ¬ block_confirmed n2 b t))) ∧ ((honest n1 ∧ honest n2) → ((transaction_confirmed tr n1 ∧ transaction_confirmed tr n2) ∨ (¬ transaction_confirmed tr n1 ∧ ¬ transaction_confirmed tr n2))) ∧ ((honest n ∧ leader n t2 ∧ transaction_time tr t1 ∧ tot.le t1 t2 ∧ broadcasted n ∧ honest n1) → transaction_confirmed tr n1))))
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d16__early__default.jsonl" "/tmp/veil-transition-local/results/queries/Ivy_Blockchain__d16__early__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d16__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_9] {
  any 16 actions
  assert (¬ (∀ n1 n2 n b t tr t1 t2, (((honest n1 ∧ honest n2) → ((block_confirmed n1 b t ∧ block_confirmed n2 b t) ∨ (¬ block_confirmed n1 b t ∧ ¬ block_confirmed n2 b t))) ∧ ((honest n1 ∧ honest n2) → ((transaction_confirmed tr n1 ∧ transaction_confirmed tr n2) ∨ (¬ transaction_confirmed tr n1 ∧ ¬ transaction_confirmed tr n2))) ∧ ((honest n ∧ leader n t2 ∧ transaction_time tr t1 ∧ tot.le t1 t2 ∧ broadcasted n ∧ honest n1) → transaction_confirmed tr n1))))
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d16__local__default.jsonl" "/tmp/veil-transition-local/results/queries/Ivy_Blockchain__d16__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_10] {
  any 32 actions
  assert (¬ (∀ n1 n2 n b t tr t1 t2, (((honest n1 ∧ honest n2) → ((block_confirmed n1 b t ∧ block_confirmed n2 b t) ∨ (¬ block_confirmed n1 b t ∧ ¬ block_confirmed n2 b t))) ∧ ((honest n1 ∧ honest n2) → ((transaction_confirmed tr n1 ∧ transaction_confirmed tr n2) ∨ (¬ transaction_confirmed tr n1 ∧ ¬ transaction_confirmed tr n2))) ∧ ((honest n ∧ leader n t2 ∧ transaction_time tr t1 ∧ tot.le t1 t2 ∧ broadcasted n ∧ honest n1) → transaction_confirmed tr n1))))
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d32__local__default.jsonl" "/tmp/veil-transition-local/results/queries/Ivy_Blockchain__d32__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d32__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_11] {
  any 32 actions
  assert (¬ (∀ n1 n2 n b t tr t1 t2, (((honest n1 ∧ honest n2) → ((block_confirmed n1 b t ∧ block_confirmed n2 b t) ∨ (¬ block_confirmed n1 b t ∧ ¬ block_confirmed n2 b t))) ∧ ((honest n1 ∧ honest n2) → ((transaction_confirmed tr n1 ∧ transaction_confirmed tr n2) ∨ (¬ transaction_confirmed tr n1 ∧ ¬ transaction_confirmed tr n2))) ∧ ((honest n ∧ leader n t2 ∧ transaction_time tr t1 ∧ tot.le t1 t2 ∧ broadcasted n ∧ honest n1) → transaction_confirmed tr n1))))
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d32__early__default.jsonl" "/tmp/veil-transition-local/results/queries/Ivy_Blockchain__d32__early__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Ivy_Blockchain__d32__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

end Blockchain
