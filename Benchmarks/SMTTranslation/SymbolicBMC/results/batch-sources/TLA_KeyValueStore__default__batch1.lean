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

-- source: KeyValueStore.tla — Key-Value Store with Snapshot Isolation
-- https://github.com/tlaplus/Examples/blob/c2641e69204ed241cdf548d9645ac82df55bfcd8/specifications/KeyValueStore/KeyValueStore.tla
-- Rewrite of KeyValueStore.lean:
--   - Use Option value for Val ∪ {NoVal} (none = NoVal)
--   - Use TSet for written, missed (set-valued state) and tx
--   - Use function for store, snapshotStore (not relation)

veil module KeyValueStoreRe

type key
type value
type txId

-- NoVal is represented by `none : Option value`

type KeySet
type TxIdSet
instantiate kSet : TSet key KeySet
instantiate tSet : TSet txId TxIdSet

-- VARIABLES
--   store,          \* A data store mapping keys to values.
--   tx,             \* The set of open snapshot transactions.
--   snapshotStore,  \* Snapshots of the store for each transaction.
--   written,        \* A log of writes performed within each transaction.
--   missed          \* The set of writes invisible to each transaction.
function store         : key → Option value
individual tx          : TxIdSet
function snapshotStore : txId → key → Option value
function written       : txId → KeySet
function missed        : txId → KeySet

#gen_state

-- Init == \* The initial predicate.
--     /\ store = [k \in Key |-> NoVal]        \* All store values are initially NoVal.
--     /\ tx = {}                              \* The set of open transactions is initially empty.
--     /\ snapshotStore =                      \* All snapshotStore values are initially NoVal.
--         [t \in TxId |-> [k \in Key |-> NoVal]]
--     /\ written = [t \in TxId |-> {}]        \* All write logs are initially empty.
--     /\ missed = [t \in TxId |-> {}]         \* All missed writes are initially empty.
after_init {
  store K := none
  tx := tSet.empty
  snapshotStore T K := none
  written T := kSet.empty
  missed T := kSet.empty
}

-- OpenTx(t) ==    \* Open a new transaction.
--     /\ t \notin tx
--     /\ tx' = tx \cup {t}
--     /\ snapshotStore' = [snapshotStore EXCEPT ![t] = store]
--     /\ UNCHANGED <<written, missed, store>>
action OpenTx (t : txId) {
  require t ∉ tx
  tx := tSet.insert t tx
  snapshotStore t K := store K
}

-- Add(t, k, v) == \* Using transaction t, add value v to the store under key k.
--     /\ t \in tx
--     /\ snapshotStore[t][k] = NoVal
--     /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
--     /\ written' = [written EXCEPT ![t] = @ \cup {k}]
--     /\ UNCHANGED <<tx, missed, store>>
action Add (t : txId) (k : key) (v : value) {
  require t ∈ tx
  require snapshotStore t k = none
  snapshotStore t k := some v
  written t := kSet.insert k (written t)
}

-- Update(t, k, v) ==  \* Using transaction t, update the value associated with key k to v.
--     /\ t \in tx
--     /\ snapshotStore[t][k] \notin {NoVal, v}
--     /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
--     /\ written' = [written EXCEPT ![t] = @ \cup {k}]
--     /\ UNCHANGED <<tx, missed, store>>
action Update (t : txId) (k : key) (v : value) {
  require t ∈ tx
  require snapshotStore t k ∉ [none, some v]
  snapshotStore t k := some v
  written t := kSet.insert k (written t)
}

-- Remove(t, k) == \* Using transaction t, remove key k from the store.
--     /\ t \in tx
--     /\ snapshotStore[t][k] /= NoVal
--     /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = NoVal]
--     /\ written' = [written EXCEPT ![t] = @ \cup {k}]
--     /\ UNCHANGED <<tx, missed, store>>
action Remove (t : txId) (k : key) {
  require t ∈ tx
  require snapshotStore t k ≠ none
  snapshotStore t k := none
  written t := kSet.insert k (written t)
}

-- RollbackTx(t) ==    \* Close the transaction without merging writes into store.
--     /\ t \in tx
--     /\ tx' = tx \ {t}
--     /\ snapshotStore' = [snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]]
--     /\ written' = [written EXCEPT ![t] = {}]
--     /\ missed' = [missed EXCEPT ![t] = {}]
--     /\ UNCHANGED store
action RollbackTx (t : txId) {
  require t ∈ tx
  tx := tSet.remove t tx
  snapshotStore t K := none
  written t := kSet.empty
  missed t := kSet.empty
}

-- CloseTx(t) ==   \* Close transaction t, merging writes into store.
--     /\ t \in tx
--     /\ missed[t] \cap written[t] = {}   \* Detection of write-write conflicts.
--     /\ store' =                         \* Merge snapshotStore writes into store.
--         [k \in Key |-> IF k \in written[t] THEN snapshotStore[t][k] ELSE store[k]]
--     /\ tx' = tx \ {t}
--     /\ missed' =    \* Update the missed writes for other open transactions.
--         [otherTx \in TxId |-> IF otherTx \in tx' THEN missed[otherTx] \cup written[t] ELSE {}]
--     /\ snapshotStore' = [snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]]
--     /\ written' = [written EXCEPT ![t] = {}]
action CloseTx (t : txId) {
  require t ∈ tx
  -- missed[t] ∩ written[t] = {}
  require kSet.isEmpty (kSet.intersection (missed t) (written t))
  -- store' = [k ∈ Key |-> IF k ∈ written[t] THEN snapshotStore[t][k] ELSE store[k]]
  store K := if K ∈ written t then snapshotStore t K else store K
  -- tx' = tx \ {t}
  tx := tSet.remove t tx
  -- missed' = [otherTx ∈ TxId |-> IF otherTx ∈ tx' THEN missed[otherTx] ∪ written[t] ELSE {}]
  missed T := if T ∈ tx then kSet.union (missed T) (written t) else kSet.empty
  -- snapshotStore' = [snapshotStore EXCEPT ![t] = [k ∈ Key |-> NoVal]]
  snapshotStore t K := none
  -- written' = [written EXCEPT ![t] = {}]
  written t := kSet.empty
}

-- TxLifecycle ==
--     /\ \A t \in tx :
--         \A k \in Key : (store[k] /= snapshotStore[t][k] /\ k \notin written[t]) => k \in missed[t]
--     /\ \A t \in TxId \ tx :
--         /\ \A k \in Key : snapshotStore[t][k] = NoVal
--         /\ written[t] = {}
--         /\ missed[t] = {}
ghost relation snapshot_isolation :=
  ∀ t ∈ tx, ∀ k, store k ≠ snapshotStore t k → k ∉ written t → k ∈ missed t

ghost relation transaction_cleanup :=
  ∀ t ∉ tx, (∀ k, snapshotStore t k = none) ∧
    kSet.isEmpty (written t) ∧ kSet.isEmpty (missed t)

invariant [Txlifecycle] snapshot_isolation ∧ transaction_cleanup


#gen_spec

run_cmd Lean.Elab.Command.liftTermElabM do
  IO.FS.writeFile "/tmp/veil-symbolic-bmc/results/batch-events/TLA_KeyValueStore__default__batch1.ready" (toString (← IO.monoMsNow))

set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.finiteModelFind true

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d1__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_0] {
  any action
  assert (¬ (snapshot_isolation ∧ transaction_cleanup))
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d1__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_KeyValueStore__d1__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d1__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d1__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_1] {
  any action
  assert (¬ (snapshot_isolation ∧ transaction_cleanup))
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d1__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_KeyValueStore__d1__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d1__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d2__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_2] {
  any 2 actions
  assert (¬ (snapshot_isolation ∧ transaction_cleanup))
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d2__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_KeyValueStore__d2__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d2__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d2__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_3] {
  any 2 actions
  assert (¬ (snapshot_isolation ∧ transaction_cleanup))
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d2__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_KeyValueStore__d2__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d2__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d4__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_4] {
  any 4 actions
  assert (¬ (snapshot_isolation ∧ transaction_cleanup))
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d4__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_KeyValueStore__d4__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d4__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d4__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_5] {
  any 4 actions
  assert (¬ (snapshot_isolation ∧ transaction_cleanup))
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d4__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_KeyValueStore__d4__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d4__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d8__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_6] {
  any 8 actions
  assert (¬ (snapshot_isolation ∧ transaction_cleanup))
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d8__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_KeyValueStore__d8__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d8__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d8__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_7] {
  any 8 actions
  assert (¬ (snapshot_isolation ∧ transaction_cleanup))
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d8__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_KeyValueStore__d8__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d8__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d16__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_8] {
  any 16 actions
  assert (¬ (snapshot_isolation ∧ transaction_cleanup))
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d16__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_KeyValueStore__d16__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d16__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d16__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_9] {
  any 16 actions
  assert (¬ (snapshot_isolation ∧ transaction_cleanup))
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d16__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_KeyValueStore__d16__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d16__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d32__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_10] {
  any 32 actions
  assert (¬ (snapshot_isolation ∧ transaction_cleanup))
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d32__old__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_KeyValueStore__d32__old__default.smt2" (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d32__old__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d32__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_11] {
  any 32 actions
  assert (¬ (snapshot_isolation ∧ transaction_cleanup))
} by
  symbolic_bench_extract "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d32__early__default.jsonl" "/tmp/veil-symbolic-bmc/results/queries/TLA_KeyValueStore__d32__early__default.smt2" (
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
  withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-symbolic-bmc/results/events/TLA_KeyValueStore__d32__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

end KeyValueStoreRe
