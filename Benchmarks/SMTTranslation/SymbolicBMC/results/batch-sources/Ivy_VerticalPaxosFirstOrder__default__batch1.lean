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

-- https://www.wisdom.weizmann.ac.il/~padon/paxos-made-epr-examples.zip /vertical_paxos/vertical_paxos_fol.ivy

veil module VerticalPaxosFirstOrder

type node
type value
type quorum
type round
type config

individual none : value
instantiate tot : TotalOrder round

immutable relation member (N : node) (Q : quorum)
immutable relation quorumin (Q : quorum) (C : config)

relation one_a (R1 : round) (R2 : round)
relation join_ack_msg (N : node) (R1 : round) (R2 : round) (V : value)
relation proposal (R : round) (V : value)
relation vote (N : node) (R : round) (V : value)
relation decision (N : node) (R : round) (V : value)
relation configure_round_msg (R : round) (C : config)
relation complete_msg (R : round)
function complete_of (C : config) : round
function quorum_of_round (R : round) : quorum
individual master_complete : round

#gen_state

assumption ∀ (c : config) (q1 : quorum) (q2 : quorum),
  quorumin q1 c ∧ quorumin q2 c → ∃ (n : node), member n q1 ∧ member n q2

after_init {
  one_a R1 R2 := false
  join_ack_msg N R1 R2 V := false
  proposal R V := false
  vote N R V := false
  decision N R V := false
  configure_round_msg R C := false
  complete_msg R := false
  require ∀ R, tot.le master_complete R
}

-- Master actions.
action configure_round (r : round) (c : config) {
  require ∀ C, ¬ configure_round_msg r C
  require tot.le master_complete r
  require complete_of c = master_complete

  configure_round_msg r c := true
}

action mark_complete (r : round) {
  require complete_msg r
  if ¬ tot.le r master_complete then
    master_complete := r
}

-- Node actions.
action send_1a (r : round) (c : config) (cr : round) {
  require configure_round_msg r c
  require cr = complete_of c
  one_a r R := decide $ one_a r R ∨ (tot.le cr R ∧ ¬ tot.le r R)
}

action join_round (n : node) (r : round) (rp : round) {
  require one_a r rp
  require ¬ (∃ (r' : round) (rp' : round) (v : value),
    join_ack_msg n r' rp' v ∧ ¬ tot.le r' r)
  let mut v : value ← pick
  if ∀ V, ¬ vote n rp V then
    v := none
  else
    require vote n rp v
  join_ack_msg n r rp v := true
}

action propose (r : round) (c : config) (cr : round) {
  quorum_of_round R := *
  require configure_round_msg r c
  require complete_of c = cr
  require ∀ V, ¬ proposal r V
  require ∀ R, tot.le cr R ∧ ¬ tot.le r R → ∃ c, configure_round_msg R c
  require ∀ R C, tot.le cr R ∧ ¬ tot.le r R ∧ configure_round_msg R C →
    quorumin (quorum_of_round R) C
  require ∀ R N, tot.le cr R ∧ ¬ tot.le r R ∧ member N (quorum_of_round R) →
    ∃ v, join_ack_msg N r R v
  let v : value ← pick
  let maxr : round ← pick
  assume
    (v = none ∧
        ∀ (N : node) (MAXR : round) (V : value),
          ¬ (tot.le cr MAXR ∧ ¬ tot.le r MAXR ∧ member N (quorum_of_round MAXR)) ∧
            join_ack_msg N r MAXR V ∧ V ≠ none) ∨
      (v ≠ none ∧
        (∃ (N : node),
          tot.le cr maxr ∧ ¬ tot.le r maxr ∧ member N (quorum_of_round maxr) ∧
            join_ack_msg N r maxr v ∧ v ≠ none) ∧
        (∀ (N : node) (MAXR : round) (V : value),
          (tot.le cr MAXR ∧ ¬ tot.le r MAXR ∧ member N (quorum_of_round MAXR) ∧
            join_ack_msg N r MAXR V ∧ V ≠ none) → tot.le MAXR maxr))
  if v = none then
    let proposedValue : value ← pick
    require proposedValue ≠ none
    complete_msg r := true
    proposal r proposedValue := true
  else
    proposal r v := true
}

action cast_vote (n : node) (v : value) (r : round) {
  require v ≠ none
  require ¬ (∃ (r' : round) (rp : round) (v' : value),
    join_ack_msg n r' rp v' ∧ ¬ tot.le r' r)
  require proposal r v
  vote n r v := true
}

action decide (n : node) (r : round) (c : config) (v : value) (q : quorum) {
  require v ≠ none
  require configure_round_msg r c
  require quorumin q c
  require ∀ N, member N q → vote N r v
  decision n r v := true
  complete_msg r := true
}

safety [coherence] decision N1 R1 V1 ∧ decision N2 R2 V2 → V1 = V2

invariant [proposal_unique] proposal R V1 ∧ proposal R V2 → V1 = V2

invariant [unique_config] configure_round_msg R C1 ∧ configure_round_msg R C2 → C1 = C2

invariant [property1_one_a] one_a R RP → ¬ tot.le R RP
invariant [property2_one_a] one_a R RP → ∃ c, configure_round_msg R c

invariant [only_vote_proposed] vote N R V → proposal R V

invariant [propose_if_lower_configured] proposal R2 V ∧ tot.le R1 R2 → ∃ c, configure_round_msg R1 c

invariant [master_complete_zero_or_holds]
  (R2 = master_complete ∨ (configure_round_msg R3 C ∧ complete_of C = R2)) ∧ ¬ tot.le R2 R1 →
    complete_msg R2

invariant [complete_prev_configured] complete_msg R2 ∧ tot.le R1 R2 → ∃ c, configure_round_msg R1 c

-- conjecture forall R:round, V:value. (exists N:node. decision(N,R,V)) -> exists C:config, Q:quorum. configure_round_msg(R,C) & quorumin(Q,C) & (forall N:node. member(N, Q) -> vote(N,R,V))
invariant [decisions_from_quorums]
  (∃ n, decision n R V) →
    ∃ c q, configure_round_msg R c ∧ quorumin q c ∧ (∀ n, member n q → vote n R V)

invariant [choosable_proposal]
  ¬ tot.le R2 R1 ∧ proposal R2 V2 ∧ V1 ≠ V2 ∧ configure_round_msg R1 C ∧ quorumin Q C →
    ∃ n r3 rp v, member n Q ∧ ¬ tot.le r3 R1 ∧ join_ack_msg n r3 rp v ∧ ¬ vote n R1 V1

invariant [configure_round_msg_bounds]
  configure_round_msg R C → tot.le (complete_of C) R ∧ tot.le (complete_of C) master_complete

invariant [complete_choosable_decision]
  complete_msg RR ∧ ¬ tot.le RR R ∧ configure_round_msg R C ∧ quorumin Q C ∧
      ¬ (∃ n r3 rp vp, member n Q ∧ ¬ tot.le r3 R ∧ join_ack_msg n r3 rp vp ∧ ¬ vote n R V) →
    ∃ nn, decision nn RR V

invariant [none_property1] ¬ proposal R none
invariant [none_property2] ¬ vote N R none
invariant [none_property3] ¬ decision N R none

invariant [join_ack_msg_property1] join_ack_msg N R RP V → one_a R RP
invariant [join_ack_msg_property2] join_ack_msg N R RP none → ¬ vote N RP V
invariant [join_ack_msg_property3] join_ack_msg N R RP V ∧ V ≠ none → vote N RP V


#gen_spec

run_cmd Lean.Elab.Command.liftTermElabM do
  IO.FS.writeFile "/tmp/veil-symbolic-bmc/results/batch-events/Ivy_VerticalPaxosFirstOrder__default__batch1.ready" (toString (← IO.monoMsNow))

set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.finiteModelFind true

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d1__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_0] {
  any action
  assert (∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d1__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/Ivy_VerticalPaxosFirstOrder__d1__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d1__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d1__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_1] {
  any action
  assert (∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d1__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/Ivy_VerticalPaxosFirstOrder__d1__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d1__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d2__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_2] {
  any 2 actions
  assert (∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d2__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/Ivy_VerticalPaxosFirstOrder__d2__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d2__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d2__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_3] {
  any 2 actions
  assert (∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d2__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/Ivy_VerticalPaxosFirstOrder__d2__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d2__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d4__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_4] {
  any 4 actions
  assert (∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d4__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/Ivy_VerticalPaxosFirstOrder__d4__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d4__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d4__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_5] {
  any 4 actions
  assert (∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d4__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/Ivy_VerticalPaxosFirstOrder__d4__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d4__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d8__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_6] {
  any 8 actions
  assert (∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d8__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/Ivy_VerticalPaxosFirstOrder__d8__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d8__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d8__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_7] {
  any 8 actions
  assert (∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d8__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/Ivy_VerticalPaxosFirstOrder__d8__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d8__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d16__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_8] {
  any 16 actions
  assert (∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d16__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/Ivy_VerticalPaxosFirstOrder__d16__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d16__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d16__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_9] {
  any 16 actions
  assert (∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d16__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/Ivy_VerticalPaxosFirstOrder__d16__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d16__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d32__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_10] {
  any 32 actions
  assert (∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d32__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/Ivy_VerticalPaxosFirstOrder__d32__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d32__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d32__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_11] {
  any 32 actions
  assert (∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d32__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/Ivy_VerticalPaxosFirstOrder__d32__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/Ivy_VerticalPaxosFirstOrder__d32__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

end VerticalPaxosFirstOrder
