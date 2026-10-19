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
  IO.FS.withFile "/tmp/veil-early-intro-multi/supplement-flood-early/events/FloodSet.log" .append fun h => h.putStrLn s

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
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

unsat trace [bench_early_32_1] {
  any 32 actions
  assert (∃ n v, decision n v)
} by
  bench_run "FloodSet_early_32_1" "/tmp/veil-early-intro-multi/supplement-flood-early/markers/FloodSet_early" (
    bench_stage "FloodSet_early_32_1" "early_intros" intro_data_prefix
    bench_stage "FloodSet_early_32_1" "nextSimp" (veil_simp +instances only [nextSimp])
    bench_stage "FloodSet_early_32_1" "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    bench_stage "FloodSet_early_32_1" "intros" veil_intros
    bench_stage "FloodSet_early_32_1" "destruct" veil_destruct
    bench_stage "FloodSet_early_32_1" "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_stage "FloodSet_early_32_1" "smtSimp" (veil_simp +instances only [smtSimp])
    bench_stage "FloodSet_early_32_1" "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    bench_preproc_complete "FloodSet_early_32_1"
    bench_smt_pipeline "FloodSet_early_32_1" "/tmp/veil-early-intro-multi/supplement-flood-early/queries/FloodSet_early_32_1.smt2"
  )

end FloodSet
