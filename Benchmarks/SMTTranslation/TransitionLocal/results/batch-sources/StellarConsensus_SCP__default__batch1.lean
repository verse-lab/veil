module

public import Veil
public import Examples.StellarConsensus.SCPTheory

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

open scoped FBA

-- adapted from [SCP.ivy](https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/SCP.ivy)

/-
  NOTE: For now we do not prove liveness property in Veil, so we only
  adapt the proof for `intertwined_safe`.
-/

/-- This type class bundles the properties abstracted from the concrete model
    of SCP, which will be used in the subsequent verification.
    In the Ivy spec, they appear as `trusted` properties (assumptions). -/
public class SCP.Background (node : outParam Type) (nset : outParam Type) where
  well_behaved : node → Prop
  intertwined : node → Prop
  intact : node → Prop
  member : node → nset → Prop
  is_quorum : nset → Prop
  blocks_slices : nset → node → Prop

  axiom_0 : ∀ (n : node), intact n → intertwined n
  axiom_1 : ∀ (n : node), intertwined n → well_behaved n
  qi_intertwined : ∀ (q1 q2 : nset),
    (∃ (n1 : node), intertwined n1 ∧ is_quorum q1 ∧ member n1 q1) ∧
    (∃ (n2 : node), intertwined n2 ∧ is_quorum q2 ∧ member n2 q2) →
    ∃ (n3 : node), well_behaved n3 ∧ member n3 q1 ∧ member n3 q2

/-- Given a concrete system model `FBA.System`, fix the intertwined set `S` and
    the intact set `I ⊆ S` to consider, all abstracted properties can be satisfied. -/
@[reducible] def one_such_Background (node : Type) [fba : FBA.System node]
    (I : FBA.NodeSet node) (_hI : FBA.intact (inst := fba) I)
    (S : FBA.NodeSet node) (hS : FBA.intertwined (inst := fba) S)
    (hIS : I ⊆ S) : SCP.Background node (FBA.NodeSet node) where
  well_behaved n := n ∈ fba.W
  intertwined n := n ∈ S
  intact n := n ∈ I
  member n s := n ∈ s
  is_quorum := FBA.quorum (inst := fba)
  blocks_slices := FBA.blocks_slices (inst := fba)

  axiom_0 := by assumption
  axiom_1 := by
    intro n
    apply FBA.intertwined_node_is_well_behaved
    assumption
  qi_intertwined := by
    simp
    intro q1 q2
    have hinter := hS.q_inter q1 q2
    repeat rw [FBA.set_ne_empty_iff_exists_mem] at hinter
    simp at hinter
    intro n hin hq1 hinq1 n' hin' hq2 hinq2
    specialize hinter
      (FBA.quorum_after_proj (inst := { W := fba.W, slices := fba.slices, slices_ne := fba.slices_ne }) _ _ hq1)
      (FBA.quorum_after_proj (inst := { W := fba.W, slices := fba.slices, slices_ne := fba.slices_ne }) _ _ hq2)
      _ hinq1 hin _ hinq2 hin'
    rcases hinter with ⟨nn, h11, h22⟩
    exists nn
    apply And.intro
    · apply FBA.intertwined_node_is_well_behaved <;> assumption
    · assumption

veil module SCP

type value
type node
type nset
type ballot

/- NOTE: In `SCP.ivy`, `ballot` is modelled as an unbounded sequence,
   but neither `next` nor `prev` appears in the protocol or any invariant.
   So here we model `ballot` as simply a `TotalOrderWithMinimum`. -/
instantiate tot : TotalOrderWithMinimum ballot
instantiate bg : Background node nset

open Background

-- Parts for the protocol.
relation voted_prepared (N : node) (B : ballot) (V : value)
relation accepted_prepared (N : node) (B : ballot) (V : value)
relation confirmed_prepared (N : node) (B : ballot) (V : value)
relation voted_committed (N : node) (B : ballot) (V : value)
relation accepted_committed (N : node) (B : ballot) (V : value)
relation confirmed_committed (N : node) (B : ballot) (V : value)
relation nomination_output (N : node) (V : value)
relation started (N : node) (B : ballot)
relation left_ballot (N : node) (B : ballot)

relation received_vote_prepare (N1 : node) (N2 : node) (B : ballot) (V : value)
relation received_accept_prepare (N1 : node) (N2 : node) (B : ballot) (V : value)
relation received_vote_commit (N1 : node) (N2 : node) (B : ballot) (V : value)
relation received_accept_commit (N1 : node) (N2 : node) (B : ballot) (V : value)

#gen_state

-- NOTE: the following seem to be unnecessary for proving the safety.
/-
assumption [qi_intact]
  ∀ (q1 q2 : nset),
    (∃ (n1 : node), intact n1 ∧ is_quorum q1 ∧ member n1 q1) ∧
    (∃ (n2 : node), intact n2 ∧ is_quorum q2 ∧ member n2 q2) →
    ∃ (n3 : node), intact n3 ∧ member n3 q1 ∧ member n3 q2

assumption [slice_blocks_ne]
  ∀ (s : nset), (∃ (n : node), intact n ∧ blocks_slices s n) → ∃ (n2 : node), member n2 s ∧ intact n2

assumption [intact_is_quorum]
  ∃ (q : nset), (∀ (n : node), member n q ↔ intact n) ∧ is_quorum q
-/

after_init {
  voted_prepared N B V := false
  accepted_prepared N B V := false
  confirmed_prepared N B V := false
  voted_committed N B V := false
  accepted_committed N B V := false
  confirmed_committed N B V := false
  nomination_output N X := false
  left_ballot N B := false
  started N B := false
  received_vote_prepare N1 N2 B V := false
  received_vote_commit N1 N2 B V := false
  received_accept_prepare N1 N2 B V := false
  received_accept_commit N1 N2 B V := false
}

action nomination_update (n : node) (v : value) {
  nomination_output n V := V == v
}

action change_ballot (n : node) (b : ballot) {
  require ¬ left_ballot n b ∧ ¬ started n b
  left_ballot n B := decide $ tot.lt B b
  started n b := true
  let bmax : ballot ← pick
  let vmax : value ← pick
  require
    ((∀ B V, tot.lt B b → ¬ confirmed_prepared n B V) ∧ nomination_output n vmax) ∨
      (tot.lt bmax b ∧ confirmed_prepared n bmax vmax ∧
        (∀ B V, tot.lt B b ∧ confirmed_prepared n B V → tot.le B bmax))
  voted_prepared n b vmax := true
}

action receive_vote_prepare (na nb : node) (b : ballot) (v : value) {
  require voted_prepared nb b v
  received_vote_prepare na nb b v := true
  if (∃ Q, is_quorum Q ∧ member na Q ∧
      (∀ N, member N Q → (received_vote_prepare na N b v ∨ received_accept_prepare na N b v)))
    ∧ (∀ B V, ¬ (accepted_committed na B V ∧ tot.lt B b ∧ V ≠ v))
    ∧ (∀ V, ¬ accepted_prepared na b V) then
    accepted_prepared na b v := true
}

action receive_accept_prepare (na nb : node) (b : ballot) (v : value) {
  require accepted_prepared nb b v
  received_accept_prepare na nb b v := true
  if (∃ Q, is_quorum Q ∧ member na Q ∧
      (∀ N, member N Q → received_accept_prepare na N b v)) then
    confirmed_prepared na b v := true
    if ¬ left_ballot na b then
      voted_committed na b v := true
  if ((∃ Q, is_quorum Q ∧ member na Q ∧
        (∀ N, member N Q → (received_vote_prepare na N b v ∨ received_accept_prepare na N b v)))
      ∨ (∃ S, blocks_slices S na ∧ (∀ N, member N S → received_accept_prepare na N b v)))
    ∧ (∀ B V, ¬ (accepted_committed na B V ∧ tot.lt B b ∧ V ≠ v))
    ∧ (∀ V, ¬ accepted_prepared na b V) then
    accepted_prepared na b v := true
}

action receive_vote_commit (na nb : node) (b : ballot) (v : value) {
  require voted_committed nb b v
  received_vote_commit na nb b v := true
  if (∃ Q, is_quorum Q ∧ member na Q ∧
      (∀ N, member N Q → (received_vote_commit na N b v ∨ received_accept_commit na N b v)))
    ∧ (∀ B V, ¬ (accepted_prepared na B V ∧ tot.lt b B ∧ V ≠ v))
    ∧ (∀ V, ¬ accepted_committed na b V)
    ∧ confirmed_prepared na b v then
    accepted_committed na b v := true
}

action receive_accept_commit (na nb : node) (b : ballot) (v : value) {
  require accepted_committed nb b v
  received_accept_commit na nb b v := true
  if (∃ Q, is_quorum Q ∧ member na Q ∧
      (∀ N, member N Q → received_accept_commit na N b v)) then
    confirmed_committed na b v := true
  if ((∃ Q, is_quorum Q ∧ member na Q ∧
        (∀ N, member N Q → (received_vote_commit na N b v ∨ received_accept_commit na N b v)))
      ∨ (∃ S, blocks_slices S na ∧ (∀ N, member N S → received_accept_commit na N b v)))
    ∧ (∀ B V, ¬ (accepted_prepared na B V ∧ tot.lt b B ∧ V ≠ v))
    ∧ (∀ V, ¬ accepted_committed na b V)
    ∧ confirmed_prepared na b v then
    accepted_committed na b v := true
}

transition byzantine_step {
  (∀ N B X, well_behaved N → voted_prepared N B X = voted_prepared' N B X) ∧
  (∀ N B X, well_behaved N → accepted_prepared N B X = accepted_prepared' N B X) ∧
  (∀ N B X, well_behaved N → voted_committed N B X = voted_committed' N B X) ∧
  (∀ N B X, well_behaved N → accepted_committed N B X = accepted_committed' N B X) ∧
  (∀ N B X, well_behaved N → confirmed_prepared N B X = confirmed_prepared' N B X) ∧
  (∀ N B X, well_behaved N → confirmed_committed N B X = confirmed_committed' N B X) ∧
  (∀ N X, well_behaved N → nomination_output N X = nomination_output' N X) ∧
  (∀ N B, well_behaved N → started N B = started' N B) ∧
  (∀ N B, well_behaved N → left_ballot N B = left_ballot' N B) ∧
  (∀ N1 N2 B X, well_behaved N1 → received_vote_prepare N1 N2 B X = received_vote_prepare' N1 N2 B X) ∧
  (∀ N1 N2 B X, well_behaved N1 → received_accept_prepare N1 N2 B X = received_accept_prepare' N1 N2 B X) ∧
  (∀ N1 N2 B X, well_behaved N1 → received_vote_commit N1 N2 B X = received_vote_commit' N1 N2 B X) ∧
  (∀ N1 N2 B X, well_behaved N1 → received_accept_commit N1 N2 B X = received_accept_commit' N1 N2 B X)
}

-- The main safety property.
safety [intertwined_safe]
  ∀ (n1 n2 : node) (b1 b2 : ballot) (v1 v2 : value),
    intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 → v1 = v2

-- Auxiliary invariants.
invariant ∀ N B V, well_behaved N ∧ accepted_committed N B V → confirmed_prepared N B V

invariant ∀ N B1 B2 V1 V2,
  well_behaved N ∧ accepted_prepared N B2 V2 ∧ (tot.lt B1 B2 ∧ V1 ≠ V2) →
    ¬ accepted_committed N B1 V1

invariant (∃ N, intertwined N ∧ confirmed_committed N B V) →
  ∃ Q, is_quorum Q ∧ (∃ N, intertwined N ∧ member N Q) ∧
    (∀ N, well_behaved N ∧ member N Q → accepted_committed N B V)

invariant (∃ N, intertwined N ∧ confirmed_prepared N B V) →
  ∃ Q, is_quorum Q ∧ (∃ N, intertwined N ∧ member N Q) ∧
    (∀ N, well_behaved N ∧ member N Q → accepted_prepared N B V)

invariant ∀ N N2 B V, well_behaved N ∧ received_accept_commit N N2 B V ∧ well_behaved N2 →
  accepted_committed N2 B V

invariant ∀ N N2 B V, well_behaved N ∧ received_accept_prepare N N2 B V ∧ well_behaved N2 →
  accepted_prepared N2 B V

invariant ∀ N B V1 V2,
  well_behaved N ∧ accepted_prepared N B V1 ∧ accepted_prepared N B V2 → V1 = V2


#gen_spec

run_cmd Lean.Elab.Command.liftTermElabM do
  IO.FS.writeFile "/tmp/veil-transition-local/results/batch-events/StellarConsensus_SCP__default__batch1.ready" (toString (← IO.monoMsNow))

set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.finiteModelFind true

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d1__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_0] {
  any action
  assert (∃ n1 n2 b1 b2 v1 v2, intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d1__early__default.jsonl" "/tmp/veil-transition-local/results/queries/StellarConsensus_SCP__d1__early__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d1__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_1] {
  any action
  assert (∃ n1 n2 b1 b2 v1 v2, intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d1__local__default.jsonl" "/tmp/veil-transition-local/results/queries/StellarConsensus_SCP__d1__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_2] {
  any 2 actions
  assert (∃ n1 n2 b1 b2 v1 v2, intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d2__local__default.jsonl" "/tmp/veil-transition-local/results/queries/StellarConsensus_SCP__d2__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d2__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_3] {
  any 2 actions
  assert (∃ n1 n2 b1 b2 v1 v2, intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d2__early__default.jsonl" "/tmp/veil-transition-local/results/queries/StellarConsensus_SCP__d2__early__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d2__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d4__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_4] {
  any 4 actions
  assert (∃ n1 n2 b1 b2 v1 v2, intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d4__early__default.jsonl" "/tmp/veil-transition-local/results/queries/StellarConsensus_SCP__d4__early__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d4__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_5] {
  any 4 actions
  assert (∃ n1 n2 b1 b2 v1 v2, intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d4__local__default.jsonl" "/tmp/veil-transition-local/results/queries/StellarConsensus_SCP__d4__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_6] {
  any 8 actions
  assert (∃ n1 n2 b1 b2 v1 v2, intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d8__local__default.jsonl" "/tmp/veil-transition-local/results/queries/StellarConsensus_SCP__d8__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d8__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_7] {
  any 8 actions
  assert (∃ n1 n2 b1 b2 v1 v2, intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d8__early__default.jsonl" "/tmp/veil-transition-local/results/queries/StellarConsensus_SCP__d8__early__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d8__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d16__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_8] {
  any 16 actions
  assert (∃ n1 n2 b1 b2 v1 v2, intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d16__early__default.jsonl" "/tmp/veil-transition-local/results/queries/StellarConsensus_SCP__d16__early__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d16__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_9] {
  any 16 actions
  assert (∃ n1 n2 b1 b2 v1 v2, intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d16__local__default.jsonl" "/tmp/veil-transition-local/results/queries/StellarConsensus_SCP__d16__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_10] {
  any 32 actions
  assert (∃ n1 n2 b1 b2 v1 v2, intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d32__local__default.jsonl" "/tmp/veil-transition-local/results/queries/StellarConsensus_SCP__d32__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d32__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_11] {
  any 32 actions
  assert (∃ n1 n2 b1 b2 v1 v2, intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d32__early__default.jsonl" "/tmp/veil-transition-local/results/queries/StellarConsensus_SCP__d32__early__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/StellarConsensus_SCP__d32__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

end SCP
