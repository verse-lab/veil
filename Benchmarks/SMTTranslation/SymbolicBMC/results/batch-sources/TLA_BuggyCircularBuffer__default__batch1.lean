module

public import Veil

set_option Elab.async false

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
    try
      withoutRecover <| evalTactic t
      symbolicBenchEvent "stage" label.getString "complete" ((← IO.monoMsNow) - start)
    catch ex =>
      symbolicBenchEvent "stage" label.getString "failed" ((← IO.monoMsNow) - start)
        [("error", toJson (← ex.toMessageData.toString))]
      throw ex

meta def symbolicBenchMetaPhase {α : Type} (label : String) (computation : MetaM α) : MetaM α := do
  symbolicBenchEvent "stage" label "begin"
  let start ← IO.monoMsNow
  try
    let value ← computation
    symbolicBenchEvent "stage" label "complete" ((← IO.monoMsNow) - start)
    return value
  catch ex =>
    symbolicBenchEvent "stage" label "failed" ((← IO.monoMsNow) - start)
      [("error", toJson (← ex.toMessageData.toString))]
    throw ex

meta def symbolicBenchTacticPhase {α : Type} (label : String) (computation : TacticM α) : TacticM α := do
  symbolicBenchEvent "stage" label "begin"
  let start ← IO.monoMsNow
  try
    let value ← computation
    symbolicBenchEvent "stage" label "complete" ((← IO.monoMsNow) - start)
    return value
  catch ex =>
    symbolicBenchEvent "stage" label "failed" ((← IO.monoMsNow) - start)
      [("error", toJson (← ex.toMessageData.toString))]
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

-- Original TLA+ file, Copyright: Igor Konnov
-- https://github.com/konnov/cyclic-buffer-challenge/blob/1e499eeb2923d70f5269aca877dc3180f3baccf9/tla/BuggyCircularBuffer.tla


public instance [NeZero N] : Inhabited { n : Nat // n ∈ List.range N } where
  default := ⟨0, by
    simp only [List.mem_range]
    have : N ≠ 0 := NeZero.ne N
    omega⟩

public instance (n : Nat) (N : Nat) [NeZero N] :  Inhabited (Std.TreeMap (Fin n) { t // t ∈ List.range N } compare) := by
  infer_instance

public instance :  Inhabited (Std.TreeMap (Fin 2) { n // n ∈ List.range 2 } compare) := by
  infer_instance

veil module BuggyCircularBuffer

abbrev BUFFER_ELEMS := (List.range 2 : List Nat)
abbrev ExtTreeElem := { n : Nat // n ∈ BUFFER_ELEMS }
abbrev BUFFER_SIZE := 2

function buffer : Fin BUFFER_SIZE → ExtTreeElem
individual head : Nat
individual tail : Fin BUFFER_SIZE
individual count : Nat

#gen_state

after_init {
  buffer := fun _ => ⟨0, by simp⟩
  head := (0 : Nat)
  tail := (0 : Fin BUFFER_SIZE)
  count := (0 : Nat)
}

/- There is not any high-bound guard condition
for this action, so it can be executed infinite times.-/
action Put {
  let x ← pick ExtTreeElem
  buffer tail := x
  head := head
  tail := Fin.mk ((tail.val + 1) % BUFFER_SIZE) (by grind)
  count := count + 1
}

action Get {
  require count > 0
  head := (head + 1) % BUFFER_SIZE
  tail := tail
  count := count - 1
}

safety count ≤ BUFFER_SIZE


#gen_spec

run_cmd Lean.Elab.Command.liftTermElabM do
  IO.FS.writeFile "/tmp/veil-symbolic-bmc/results/batch-events/TLA_BuggyCircularBuffer__default__batch1.ready" (toString (← IO.monoMsNow))

set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.finiteModelFind true

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d1__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_0] {
  any action
  assert (count > BUFFER_SIZE)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d1__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_BuggyCircularBuffer__d1__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d1__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d1__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_1] {
  any action
  assert (count > BUFFER_SIZE)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d1__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_BuggyCircularBuffer__d1__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d1__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d2__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_2] {
  any 2 actions
  assert (count > BUFFER_SIZE)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d2__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_BuggyCircularBuffer__d2__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d2__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d2__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_3] {
  any 2 actions
  assert (count > BUFFER_SIZE)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d2__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_BuggyCircularBuffer__d2__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d2__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d4__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_4] {
  any 4 actions
  assert (count > BUFFER_SIZE)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d4__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_BuggyCircularBuffer__d4__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d4__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d4__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_5] {
  any 4 actions
  assert (count > BUFFER_SIZE)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d4__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_BuggyCircularBuffer__d4__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d4__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d8__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_6] {
  any 8 actions
  assert (count > BUFFER_SIZE)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d8__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_BuggyCircularBuffer__d8__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d8__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d8__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_7] {
  any 8 actions
  assert (count > BUFFER_SIZE)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d8__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_BuggyCircularBuffer__d8__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d8__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d16__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_8] {
  any 16 actions
  assert (count > BUFFER_SIZE)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d16__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_BuggyCircularBuffer__d16__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d16__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d16__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_9] {
  any 16 actions
  assert (count > BUFFER_SIZE)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d16__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_BuggyCircularBuffer__d16__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d16__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d32__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_10] {
  any 32 actions
  assert (count > BUFFER_SIZE)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d32__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_BuggyCircularBuffer__d32__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d32__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d32__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_11] {
  any 32 actions
  assert (count > BUFFER_SIZE)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d32__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_BuggyCircularBuffer__d32__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_BuggyCircularBuffer__d32__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

end BuggyCircularBuffer
