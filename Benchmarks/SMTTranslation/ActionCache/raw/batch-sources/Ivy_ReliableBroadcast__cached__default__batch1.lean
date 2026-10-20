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
set_option veil.experimental.bmcCache true

veil module ReliableBroadcast

/-
  Reliable Broadcast is a Byzantine fault-tolerant broadcast protocol
  that ensures that all honest nodes deliver the same message, as long
  as the `originator` (the node that initiated the broadcast) is honest.

  It proceeds in three phases:
    - an initial phase, where the originator broadcasts `initial_msg`
    - an echo phase, where nodes broadcast an `echo` of the value they
      received
    - a vote phase, where nodes broadcast a `vote` for the value they've
      seen echoed by a `2f + 1` quorum of nodes; alternatively, a node
      votes if it sees `f + 1` votes for the same value

  The `deliver` action is triggered when a node sees `2f + 1` votes for
  the same value, and outputs (delivers) that value.

  The protocol has three separate quorum thresholds:
    - `echo4vote` -- `2f + 1` nodes that have echoed the same value to vote
    - `vote4vote` -- `f + 1` nodes that have voted for the same value to vote
    - `vote4output` -- `2f + 1` nodes that have voted for the same value to output/deliver
-/


type nodeset
type address
type round
type value

--  immutable relation?
-- variable (is_byz : address → Prop)

instantiate nset : ByzNodeSet address nodeset
open ByzNodeSet

-- TODO: we might want to replace the second condition in `vote` to use this
-- /-- A fraction of nodes (f + 1) with at least one honest member. -/
-- class FractionWithOneHonest (node : Type) (quorum : outParam Type) [ByzantineQuorum node quorum] :=
--   contains (a : node) (q : quorum) : Prop
--   one_honest (q : quorum) : ∃ (a : node), contains a q ∧ ¬ is_byz a

-- instantiate honest_fraction : FractionWithOneHonest address quorum
-- open FractionWithOneHonest

-- Messages over the network
relation initial_msg (originator : address) (dst : address) (r : round) (v : value)
relation echo_msg (src : address) (dst : address) (originator : address) (r : round) (v : value)
relation vote_msg (src : address) (dst : address) (originator : address) (r : round) (v : value)

-- State of the nodes
/- sent(address, round) := has the node initiated round `r`? -/
relation sent (n : address) (r : round)
relation echoed (n : address) (originator : address) (in_round : round) (v : value)
relation voted (n : address) (originator : address) (in_round : round) (v : value)
relation delivered (n : address) (originator : address) (in_round : round) (v : value)

#gen_state

-- Ghost relations
ghost relation initial_value (n : address) (r : round) (v : value) := ∀ dst, initial_msg n dst r v

after_init {
  initial_msg O D R V := false;
  echo_msg S D O R V  := false;
  vote_msg S D O R V  := false;

  sent N R            := false;
  echoed N O R V      := false;
  voted N O R V       := false;
  delivered N O R V   := false
}

transition byz {
  (∀ (src dst : address) (r : round) (v : value),
    (¬ is_byz src ∧ (initial_msg src dst r v ↔ initial_msg' src dst r v)) ∨
    (is_byz src ∧ (initial_msg src dst r v → initial_msg' src dst r v))) ∧
  (∀ (src dst originator : address) (r : round) (v : value),
    (¬ is_byz src ∧ (echo_msg src dst originator r v ↔ echo_msg' src dst originator r v)) ∨
    (is_byz src ∧ (echo_msg src dst originator r v → echo_msg' src dst originator r v))) ∧
  (∀ (src dst originator : address) (r : round) (v : value),
    (¬ is_byz src ∧ (vote_msg src dst originator r v ↔ vote_msg' src dst originator r v)) ∨
    (is_byz src ∧ (vote_msg src dst originator r v → vote_msg' src dst originator r v)))
}

action broadcast (n : address) (r : round) (v : value) {
  require ¬ sent n r;
  initial_msg n N r v := true;
  sent n r := true
}

action echo (n : address) (originator : address) (r : round) (v : value) {
  require initial_msg originator n r v;
  require ∀ V, ¬ echoed n originator r V;
  echoed n originator r v := true;
  echo_msg n DST originator r v := true
}

action vote (n : address) (originator : address) (r : round) (v : value) {
  -- received 2f + 1 echo messages OR f + 1 vote messages
  require (∃ (q : nodeset), nset.supermajority q ∧
              ∀ (src : address), nset.member src q → echo_msg src n originator r v) ∨
          (∃ (q : nodeset), nset.greater_than_third q ∧
              ∀ (src : address), nset.member src q → vote_msg src n originator r v);
  require ∀ V, ¬ voted n originator r V;
  voted n originator r v := true;
  vote_msg n DST originator r v := true
}

action deliver (n : address) (originator : address) (r : round) (v : value) {
  -- received 2f + 1 votes
  require (∃ (q : nodeset), nset.supermajority q ∧
              ∀ (src : address), nset.member src q → vote_msg src n originator r v);
  delivered n originator r v := true
}

/- If a value is voted for, it is the value that was initially proposed by the originator. -/
safety [vote_integrity]
  ∀ (src dst : address) (r : round) (v : value),
     ¬ is_byz src ∧ ¬ is_byz dst ∧ voted dst src r v → (sent src r ∧ initial_value src r v)

/- If a value is delivered, it is the value that was initially proposed by the originator. -/
safety [deliver_integrity]
  ∀ (src dst : address) (r : round) (v : value),
     ¬ is_byz src ∧ ¬ is_byz dst ∧ delivered dst src r v → (sent src r ∧ initial_value src r v)

/- Also known as "delivered uniqueness". -/
safety [agreement]
  ∀ (src dst₁ dst₂ : address) (r : round) (v₁ v₂ : value),
    ¬ is_byz dst₁ ∧ ¬ is_byz dst₂ ∧ delivered dst₁ src r v₁ ∧ delivered dst₂ src r v₂ → v₁ = v₂

-- These invariants are discovered in the order given, by inspecting the code
-- of the actions one by one.

-- broadcast
invariant [sent_iff_initial]
  ∀ (src : address) (r : round),
    ¬ is_byz src → (sent src r ↔ ∃ (v : value), initial_value src r v)

-- echo
invariant [echoed_iff_echo]
  ∀ (n dst originator : address) (r : round) (v : value),
    ¬ is_byz n → (echoed n originator r v ↔ echo_msg n dst originator r v)

invariant [echoed_requires_initial]
  ∀ (n originator : address) (r : round) (v : value),
    ¬ is_byz n → (echoed n originator r v → initial_msg originator n r v)

-- vote
invariant [voted_iff_vote]
  ∀ (n dst originator : address) (r : round) (v : value),
    ¬ is_byz n → (voted n originator r v ↔ vote_msg n dst originator r v)

-- not in the decidable fragment due to edge from `address` to `nodeset`:
invariant [voted_requires_echo_quorum_or_vote_quorum]
  ∀ (n originator : address) (r : round) (v : value),
    ¬ is_byz n → (voted n originator r v →
      (∃ (q : nodeset), nset.supermajority q ∧
        ∀ (src : address), member src q → echo_msg src n originator r v) ∨
      (∃ (q : nodeset), nset.greater_than_third q ∧
        ∀ (src : address), member src q → vote_msg src n originator r v))

-- deliver
-- not in the decidable fragment due to edge from `address` to `nodeset`
invariant [delivered_requires_vote_quorum]
  ∀ (n originator : address) (r : round) (v : value),
    ¬ is_byz n → (delivered n originator r v →
      ∃ (q : nodeset), nset.supermajority q ∧
        ∀ (src : address), member src q → vote_msg src n originator r v)

-- these invariants are discovered in the order given, by eliminating CTIs

-- vote_vote_integrity
-- this version is not in the decidable fragment:
-- invariant [sent_iff_initial]
--   ∀ (src : address) (r : round),
--     sent src r ↔ ∃ (dst : address) (v : value), initial_msg src dst r v

-- So instead we use the following:
invariant [initial_value_iff_initial_msg]
  ∀ (src dst : address) (r : round) (v : value),
    ¬ is_byz src → (initial_value src r v ↔ initial_msg src dst r v)

-- deliver_agreement
invariant [honest_non_conflicting_initial_msg]
  ∀ (src dst₁ dst₂ : address) (r : round) (v₁ v₂ : value),
    (¬ is_byz src) → (initial_msg src dst₁ r v₁ ∧ initial_msg src dst₂ r v₂ → v₁ = v₂)

invariant [honest_non_conflicting_echoes]
  ∀ (src originator dst₁ dst₂ : address) (r : round) (v₁ v₂ : value),
    (¬ is_byz src) → (echo_msg src dst₁ originator r v₁ ∧ echo_msg src dst₂ originator r v₂ → v₁ = v₂)

invariant [honest_non_conflicting_votes]
  ∀ (src originator dst₁ dst₂ : address) (r : round) (v₁ v₂ : value),
    (¬ is_byz src) → (vote_msg src dst₁ originator r v₁ ∧ vote_msg src dst₂ originator r v₂ → v₁ = v₂)


#gen_spec
run_cmd discard <| _root_.Veil.Verifier.waitFilteredSync _root_.Veil.Verifier.isDoesNotThrow

run_cmd Lean.Elab.Command.liftTermElabM do
  IO.FS.writeFile "/tmp/veil-action-cache/results/batch-events/Ivy_ReliableBroadcast__cached__default__batch1.ready" (toString (← IO.monoMsNow))

set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.finiteModelFind true

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d1__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_0] {
  any action
  assert (∃ src dst r v, ¬ is_byz src ∧ ¬ is_byz dst ∧ voted dst src r v ∧ ¬ (sent src r ∧ initial_value src r v))
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d1__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/Ivy_ReliableBroadcast__d1__cached__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "cached_normalize" __veil_bmc_normalize
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d1__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d2__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_1] {
  any 2 actions
  assert (∃ src dst r v, ¬ is_byz src ∧ ¬ is_byz dst ∧ voted dst src r v ∧ ¬ (sent src r ∧ initial_value src r v))
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d2__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/Ivy_ReliableBroadcast__d2__cached__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "cached_normalize" __veil_bmc_normalize
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d2__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d4__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_2] {
  any 4 actions
  assert (∃ src dst r v, ¬ is_byz src ∧ ¬ is_byz dst ∧ voted dst src r v ∧ ¬ (sent src r ∧ initial_value src r v))
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d4__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/Ivy_ReliableBroadcast__d4__cached__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "cached_normalize" __veil_bmc_normalize
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d4__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d8__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_3] {
  any 8 actions
  assert (∃ src dst r v, ¬ is_byz src ∧ ¬ is_byz dst ∧ voted dst src r v ∧ ¬ (sent src r ∧ initial_value src r v))
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d8__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/Ivy_ReliableBroadcast__d8__cached__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "cached_normalize" __veil_bmc_normalize
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d8__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d16__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_4] {
  any 16 actions
  assert (∃ src dst r v, ¬ is_byz src ∧ ¬ is_byz dst ∧ voted dst src r v ∧ ¬ (sent src r ∧ initial_value src r v))
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d16__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/Ivy_ReliableBroadcast__d16__cached__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "cached_normalize" __veil_bmc_normalize
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d16__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d32__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_5] {
  any 32 actions
  assert (∃ src dst r v, ¬ is_byz src ∧ ¬ is_byz dst ∧ voted dst src r v ∧ ¬ (sent src r ∧ initial_value src r v))
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d32__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/Ivy_ReliableBroadcast__d32__cached__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "cached_normalize" __veil_bmc_normalize
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Ivy_ReliableBroadcast__d32__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

end ReliableBroadcast
