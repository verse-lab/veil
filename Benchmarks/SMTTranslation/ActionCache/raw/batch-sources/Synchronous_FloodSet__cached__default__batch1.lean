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

/-!
# FloodSet Consensus Protocol

FloodSet is a synchronous consensus protocol that tolerates up to `t` crash
failures over `t+1` rounds. The protocol is remarkably simple:

1. Each node starts with an initial value (its proposal)
2. In each round, all alive nodes broadcast their seen values to everyone
3. After `t+1` rounds, each node decides on the minimum value it has seen

The key insight is the **pigeonhole principle**: with at most `t` crashes spread
over `t+1` rounds, at least one round must be crash-free. In that round, all
alive nodes successfully exchange their seen sets and become synchronized. Once
synchronized, all alive nodes have identical seen sets and will decide on the
same minimum value, guaranteeing agreement.

Partial delivery: When a node crashes mid-round, it may have sent its values to
some nodes but not others. We model this with `receivedFromDead`.
-/

veil module FloodSet

--------------------------------------------------------------------------------
-- PART 1: STATE
--
-- Veil state declarations:
-- - `type` declares an uninterpreted sort (abstract type)
-- - `instantiate` provides a typeclass instance for a type
-- - `immutable individual` declares a constant (theory parameter)
-- - `individual` declares a mutable scalar state component
-- - `relation` declares a mutable predicate (function to Bool)
-- - `#gen_state` finalizes the state type from all declarations
--------------------------------------------------------------------------------

-- Abstract types for nodes and values
type node
type value

-- Values must be totally ordered (for picking the minimum)
instantiate val_ord : TotalOrder value
open TotalOrder

-- Protocol state components:
-- - t: maximum crash failures tolerated (immutable theory parameter)
-- - round: current round number (0 to t+1)
-- - crashCount: total number of crashes so far
-- - seen: values each node has observed
-- - alive: whether each node is still functioning
-- - decision: the decided value (if any) for each node
-- - crashedInThisRound: nodes that crashed in the current round (before advanceRound)
-- - initialValue: snapshot of each node's initial proposal (for extended validity)

immutable individual t : Nat

individual round : Nat
individual crashCount : Nat

function initialValue : node → value
relation seen : node → value → Bool
relation alive : node → Bool
relation decision : node → value → Bool
relation crashedInThisRound : node → Bool

#gen_state

--------------------------------------------------------------------------------
-- PART 2: ACTIONS
--------------------------------------------------------------------------------

-- Initial state: each node has exactly one proposal value
after_init {
  initialValue := *
  seen N V := initialValue N == V

  alive N := true
  decision N V := false
  round := 0
  crashCount := 0
  crashedInThisRound N := false
}

-- Crash one alive node (can happen multiple times per round, up to t total)
action crash (n : node) {
  require round < t + 1
  require crashCount < t
  require alive n

  alive n := false
  crashedInThisRound n := true
  crashCount := crashCount + 1
}

-- Advance to next round: alive nodes exchange values, with possible partial
-- delivery from nodes that crashed this round (modeled by receivedFromDead)
action advanceRound {
  require round < t + 1

  -- Some nodes may receive values from some dead nodes
  -- The first argument is a possibly dead source
  -- The second is a possibly allive destination
  let deadToAliveDelivery : node → node → Bool :| true

  -- Alive nodes exchange values
  seen N V := seen N V ||
    alive N &&
      -- Get from alive nodes
      decide ((∃ m, alive m ∧ seen m V) ∨
      -- Get from some recently deceased nodes, too
              (∃ d, crashedInThisRound d ∧ deadToAliveDelivery d N ∧ seen d V))

  -- Reset crash-related bookkeeping for the next round
  crashedInThisRound N := false
  round := round + 1
}


-- Decision: after t+1 rounds, pick the minimum seen value
action nodeDecide (n : node) {
  require round = t + 1
  require alive n

  let v :| seen n v
  assume ∀ w, seen n w → le v w

  decision n V := V == v
}

--------------------------------------------------------------------------------
-- PART 3: SAFETY AND INVARIANTS
--------------------------------------------------------------------------------

-- Main safety properties
safety [agreement]
  ∀ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 → v1 = v2

-- Validity: decided value was some node's initial proposal
safety [validity]
  ∀ n v, decision n v → (∃ m, initialValue m == v)

-- Supporting invariants

-- Seen decision: decided value was seen by the deciding node
invariant [seen_decision]
  ∀ n v, decision n v → seen n v

-- Crashed node can't be alive
invariant [crashed_not_alive]
  ∀ n, crashedInThisRound n → ¬ alive n

-- Key invariant for extended validity: all seen values were initially proposed by some node
invariant [seen_is_initial]
  ∀ n v, seen n v → (∃ m, initialValue m == v)

invariant [decided_implies_alive]
  ∀ n v, decision n v → alive n

invariant [crash_bound]
  crashCount ≤ t

invariant [decision_only_at_end]
  ∀ n v, decision n v → round = t + 1

invariant [decision_is_minimum]
  ∀ n v, decision n v → (∀ w, seen n w → le v w)

-- All alive nodes have identical seen sets
ghost relation allSameSeen :=
  ∀ n1 n2 v, alive n1 ∧ alive n2 → (seen n1 v = seen n2 v)

-- Key invariant: after a crash-free round, all alive nodes are synchronized.
invariant [same_seen_if_synced]
  crashCount < round → allSameSeen

-- Crashed nodes this round have the same seen as alive nodes (when synced).
-- This ensures partial delivery doesn't break allSameSeen.
invariant [crashed_same_seen]
  ∀ n m v, crashCount < round ∧ crashedInThisRound n ∧ alive m → (seen n v = seen m v)

-- Crashed nodes this round have the same seen as alive nodes when crashCount = round.
-- They crashed after a clean round, so they inherited the synchronized seen set.
invariant [crashed_same_when_count_eq_round]
  ∀ n m v, crashCount = round ∧ crashedInThisRound n ∧ alive m → (seen n v = seen m v)

-------------------------------------------------------------
-- Reachability checks (commented out after validation):
-- These temporarily defined "bad" safety properties prove interesting states
-- are reachable by expecting the model checker to find violations.
-------------------------------------------------------------

-- 1. Decision is reachable (protocol can terminate)
-- Expected: violation found (meaning decisions ARE reachable)
--
-- safety [no_decision] ∀ n v, ¬decision n v

-- 2. Crashes are possible (not all nodes survive)
-- Expected: violation found (meaning crashes ARE possible)
--
-- safety [no_crashes] ∀ n, alive n

-- 3. Dead nodes may have different seen sets than alive nodes
-- Expected: violation found (dead nodes can diverge from alive ones)
--
-- safety [dead_same_as_alive] ∀ n1 n2 v, ¬alive n1 ∧ alive n2 → (seen n1 v = seen n2 v)

-- 4. Nodes can see multiple values (non-trivial seen sets) in non-init rounds
-- Expected: violation found (nodes can accumulate multiple values)
--
-- safety [single_value_only] ∀ n v1 v2, round > 0 → seen n v1 ∧ seen n v2 → v1 = v2


#gen_spec
run_cmd discard <| _root_.Veil.Verifier.waitFilteredSync _root_.Veil.Verifier.isDoesNotThrow

run_cmd Lean.Elab.Command.liftTermElabM do
  IO.FS.writeFile "/tmp/veil-action-cache/results/batch-events/Synchronous_FloodSet__cached__default__batch1.ready" (toString (← IO.monoMsNow))

set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.finiteModelFind true

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d1__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_0] {
  any action
  assert (∃ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d1__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/Synchronous_FloodSet__d1__cached__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d1__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d2__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_1] {
  any 2 actions
  assert (∃ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d2__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/Synchronous_FloodSet__d2__cached__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d2__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d4__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_2] {
  any 4 actions
  assert (∃ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d4__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/Synchronous_FloodSet__d4__cached__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d4__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d8__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_3] {
  any 8 actions
  assert (∃ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d8__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/Synchronous_FloodSet__d8__cached__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d8__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d16__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_4] {
  any 16 actions
  assert (∃ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d16__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/Synchronous_FloodSet__d16__cached__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d16__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d32__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_5] {
  any 32 actions
  assert (∃ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 ∧ v1 ≠ v2)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d32__cached__default.jsonl" "/tmp/veil-action-cache/results/queries/Synchronous_FloodSet__d32__cached__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Synchronous_FloodSet__d32__cached__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

end FloodSet
