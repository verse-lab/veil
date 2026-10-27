module

public import Veil

/-!
Upstream license: Apache-2.0; see Benchmarks/TLA/ParallelCommits/LICENSE.
Copyright: The Cockroach Authors; see Benchmarks/TLA/ParallelCommits/UPSTREAM-LICENSE.
Source (CockroachDB v21.1.0):
https://github.com/cockroachdb/cockroach/blob/eb9e1a7c237edac6893141d6c8dc10f05a829861/docs/tla-plus/ParallelCommits/ParallelCommits.tla
The BSL Change Date is 2024-04-01 and Change License is Apache-2.0;
see Benchmarks/TLA/ParallelCommits/LICENSE-BSL.
Modified: translated and adapted to Veil.
-/

veil module ParallelCommits

type key
type preventer
type KeySet
param maxAttempts : Nat

enum RecordStatus = {rPending, rStaging, rCommitted, rAborted}
enum PC = {beginTxnEpoch, pipelineWrites, stageWritesAndRecord, stageWritesAndRecordLoop,
  queryPipelinedWrite, parallelWrite, stageRecord, ackClient, asyncExplicitlyCommitted,
  asyncResolveIntents, endCommitter, preventLoop, pushRecord, preventWrites,
  recoverRecord, resolveIntents, done}

@[veil_decl]
structure TxnRecord (RecordStatus : Type) where
  status : RecordStatus
  epoch : Nat
  ts : Nat

@[veil_decl]
structure IntentWrite where
  epoch : Nat
  ts : Nat
  resolved : Bool

instantiate keySet : TSet key KeySet
immutable individual AllKeys : KeySet

individual record : TxnRecord RecordStatus
function intent_writes : key → IntentWrite
function tscache : key → Nat
individual commit_ack : Bool
function pc : Option preventer → PC
individual pipelined_keys : KeySet
individual parallel_keys : KeySet
individual attempt : Nat
individual txn_epoch : Nat
individual txn_ts : Nat
individual to_write : KeySet
individual to_check : KeySet
individual have_staging_record : Bool
function prevent_epoch : preventer → Nat
function prevent_ts : preventer → Nat
function found_writes : preventer → KeySet
function to_resolve : preventer → KeySet

set_option veil.deferVCGeneration true

veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

assumption [keys_complete] ∀ k : key, k ∈ AllKeys
assumption [keys_nonempty] ¬ keySet.isEmpty AllKeys
assumption [preventers_nonempty] ∃ _ : preventer, True
assumption [attempts_positive] maxAttempts > 0

ghost relation QueryIntent (k : key) (epoch ts : Nat) :=
  (intent_writes k).epoch = epoch ∧ (intent_writes k).ts ≤ ts ∧ ¬ (intent_writes k).resolved

-- Unlike QueryIntent, this source definition does not test resolved.
ghost relation ImplicitlyCommitted :=
  record.status = rStaging ∧ ∀ k : key,
    (intent_writes k).epoch = record.epoch ∧ (intent_writes k).ts ≤ record.ts

ghost relation Committed := ImplicitlyCommitted ∨ record.status = rCommitted

after_init {
  record := { status := rPending, epoch := 0, ts := 0 }
  intent_writes K := { epoch := 0, ts := 0, resolved := false }
  tscache K := 0
  commit_ack := false
  let chosen : { ks // TSet.isSubset ks AllKeys } :| true
  pipelined_keys := chosen.val
  parallel_keys := keySet.diff AllKeys chosen.val
  attempt := 1
  txn_epoch := 0
  txn_ts := 0
  to_write := keySet.empty
  to_check := keySet.empty
  have_staging_record := false
  prevent_epoch P := 0
  prevent_ts P := 0
  found_writes P := keySet.empty
  to_resolve P := AllKeys
  pc PP := if PP.isNone then beginTxnEpoch else preventLoop
}

action BeginTxnEpoch {
  require pc none = beginTxnEpoch
  txn_epoch := txn_epoch + 1
  txn_ts := txn_ts + 1
  to_write := pipelined_keys
  pc none := if attempt > maxAttempts then endCommitter else pipelineWrites
}

action PipelineWrites {
  require pc none = pipelineWrites
  if ¬ keySet.isEmpty to_write then
    let k : key :| k ∈ to_write
    to_write := keySet.remove k to_write
    if ¬ (intent_writes k).resolved then
      -- The generated source Assert(FALSE) fires when the cache prevents this write.
      assert tscache k < txn_ts
      let succeeded : Bool :| true
      if succeeded then
        intent_writes k := { epoch := txn_epoch, ts := txn_ts, resolved := false }
  else
    pc none := stageWritesAndRecord
}

action StageWritesAndRecord {
  require pc none = stageWritesAndRecord
  to_write := parallel_keys
  to_check := pipelined_keys
  have_staging_record := false
  pc none := if attempt > maxAttempts then endCommitter else stageWritesAndRecordLoop
}

-- The three work arms of the final-batch scheduler may overlap, so the arm is
-- chosen non-deterministically and keeps its own guard.
action StageWritesAndRecordLoop {
  require pc none = stageWritesAndRecordLoop
  if ¬ keySet.isEmpty to_check ∨ ¬ keySet.isEmpty to_write ∨ ¬ have_staging_record then
    let choice ← pick (Fin 3)
    if choice = 0 then
      assume ¬ keySet.isEmpty to_check
      pc none := queryPipelinedWrite
    else if choice = 1 then
      assume ¬ keySet.isEmpty to_write
      pc none := parallelWrite
    else
      assume ¬ have_staging_record
      pc none := stageRecord
  else
    pc none := ackClient
}

action QueryPipelinedWrite {
  require pc none = queryPipelinedWrite
  let k : key :| k ∈ to_check
  if QueryIntent k txn_epoch txn_ts then
    to_check := keySet.remove k to_check
    pc none := stageWritesAndRecordLoop
  else if record.status = rPending ∨ record.status = rStaging then
    attempt := attempt + 1
    pc none := beginTxnEpoch
  else if record.status = rAborted then
    pc none := endCommitter
  else
    pc none := ackClient
}

action ParallelWrite {
  require pc none = parallelWrite
  let k : key :| k ∈ to_write
  let oldIntent := intent_writes k
  to_write := keySet.remove k to_write
  if oldIntent.epoch = txn_epoch then
    pc none := stageWritesAndRecordLoop
  else if tscache k ≥ txn_ts ∨ oldIntent.resolved then
    let refresh : Bool :| true
    attempt := attempt + 1
    if refresh then
      txn_ts := txn_ts + 1
      pc none := stageWritesAndRecord
    else
      pc none := beginTxnEpoch
  else
    intent_writes k := { epoch := txn_epoch, ts := txn_ts, resolved := false }
    pc none := stageWritesAndRecordLoop
}

action StageRecord {
  require pc none = stageRecord
  have_staging_record := true
  if record.status = rPending then
    record := { status := rStaging, epoch := txn_epoch, ts := txn_ts }
    pc none := stageWritesAndRecordLoop
  else if record.status = rStaging then
    assert record.epoch ≤ txn_epoch ∧ record.ts < txn_ts
    record := { status := rStaging, epoch := txn_epoch, ts := txn_ts }
    pc none := stageWritesAndRecordLoop
  else if record.status = rAborted then
    pc none := endCommitter
  else
    assert False
    pc none := stageWritesAndRecordLoop
}

action AckClient {
  require pc none = ackClient
  assert Committed
  commit_ack := true
  pc none := asyncExplicitlyCommitted
}

action AsyncExplicitlyCommitted {
  require pc none = asyncExplicitlyCommitted
  if record.status = rStaging then
    assert ImplicitlyCommitted
    record := { record with status := rCommitted }
  else
    assert record.status = rCommitted
  to_write := AllKeys
  pc none := asyncResolveIntents
}

action AsyncResolveIntents {
  require pc none = asyncResolveIntents
  if ¬ keySet.isEmpty to_write then
    let k : key :| k ∈ to_write
    if ¬ (intent_writes k).resolved then
      intent_writes k := { intent_writes k with resolved := true }
    to_write := keySet.remove k to_write
  else
    pc none := endCommitter
}

action EndCommitter {
  require pc none = endCommitter
  pc none := done
}

action PreventLoop (p : preventer) {
  require pc (some p) = preventLoop
  found_writes p := keySet.empty
  pc (some p) := pushRecord
}

action PushRecord (p : preventer) {
  require pc (some p) = pushRecord
  if record.status = rPending then
    record := { record with status := rAborted }
    pc (some p) := resolveIntents
  else if record.status = rStaging then
    prevent_epoch p := record.epoch
    prevent_ts p := record.ts
    pc (some p) := preventWrites
  else
    pc (some p) := resolveIntents
}

-- found_writes[self] /= KEYS is set inequality, which relies on a canonical KeySet
-- (OrdList). As a guard, ∀ k, k ∈ found_writes p breaks wp_local_eq here.
action PreventWrites (p : preventer) {
  require pc (some p) = preventWrites
  if found_writes p ≠ AllKeys then
    let k : key :| k ∉ found_writes p
    if QueryIntent k (prevent_epoch p) (prevent_ts p) then
      found_writes p := keySet.insert k (found_writes p)
    else
      if tscache k < prevent_ts p then
        tscache k := prevent_ts p
      pc (some p) := recoverRecord
  else
    pc (some p) := recoverRecord
}

action RecoverRecord (p : preventer) {
  require pc (some p) = recoverRecord
  -- prevented == found_writes[self] /= KEYS
  if found_writes p ≠ AllKeys then
    if record.status = rAborted ∨ record.status = rCommitted then
      pc (some p) := resolveIntents
    else if record.status = rPending then
      assert False
      pc (some p) := resolveIntents
    else if record.epoch ≥ prevent_epoch p ∧ record.ts > prevent_ts p then
      pc (some p) := preventLoop
    else
      record := { record with status := rAborted }
      pc (some p) := resolveIntents
  else
    assert record.status = rStaging ∨ record.status = rCommitted
    assert record.epoch = prevent_epoch p
    assert record.ts = prevent_ts p
    if record.status = rStaging then
      assert ImplicitlyCommitted
      record := { record with status := rCommitted }
    pc (some p) := resolveIntents
}

action ResolveIntents (p : preventer) {
  require pc (some p) = resolveIntents
  if ¬ keySet.isEmpty (to_resolve p) then
    let k : key :| k ∈ to_resolve p
    if ¬ (intent_writes k).resolved then
      intent_writes k := { intent_writes k with resolved := true }
    to_resolve p := keySet.remove k (to_resolve p)
  else
    pc (some p) := done
}

-- Keep the source's explicit all-Done self-loop, in addition to implicit stutter.
action Terminating {
  require ∀ p : Option preventer, pc p = done
}

-- No bound on local attempt/txn_epoch/txn_ts was present in TypeInvariants.
invariant [TypeInvariants]
  record.epoch ≤ maxAttempts ∧ record.ts ≤ maxAttempts ∧
  ∀ k : key, (intent_writes k).epoch ≤ maxAttempts ∧
    (intent_writes k).ts ≤ maxAttempts ∧ tscache k ≤ maxAttempts

invariant [AckImpliesCommit] commit_ack → Committed

#gen_spec
#gen_executable

-- The check below uses the instance of the TLC model
-- `Benchmarks/TLA/ParallelCommits/ParallelCommits.cfg`. It is commented out; uncomment it to
-- run it.
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s:
-- * `key := Fin 2`: the keys are `0`, `1` (cfg: `KEYS = {k1, k2}`).
-- * `preventer := Fin 2`: the preventer processes are `0`, `1` (cfg: `PREVENTERS = {p1, p2}`).
-- * `KeySet := OrdList (Fin 2)`: `OrdList` has the `TSet` instance that the `instantiate` line
--   above requires.
-- * `maxAttempts := 4`: the committer gives up after 4 attempts (cfg: `MAX_ATTEMPTS = 4`).
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields:
-- * `AllKeys := OrdList.ofList (List.finRange 2)`: the set of all keys, for where the spec uses
--   `KEYS` as a value. The `assumption [keys_complete]` above checks that it contains every key.
--
-- Before searching, `#model_check` also checks the other `assumption`s above, which are the
-- spec's `ASSUME`s.
--
-- The other settings of the cfg:
-- * `INVARIANTS TypeInvariants AckImpliesCommit`: `#model_check` checks every `invariant` of the
--   module, which here has the same two names. The `TypeInvariants` here keeps the numeric
--   bounds of the spec's `TypeInvariants`; Lean's types ensure the rest.
-- * `CHECK_DEADLOCK FALSE`: this module has no `termination` clause, so Veil reports no
--   deadlocks either.
-- Options:
-- * `compiled` runs the search only in a compiled checker, not in Lean's interpreter.
-- * `(seenSet := HAMTMapShard)`: the sharded map of visited states uses `HAMTMapShard`.
/- EVAL
#model_check compiled
  { key := Fin 2, preventer := Fin 2, KeySet := OrdList (Fin 2), maxAttempts := 4 }
  { AllKeys := OrdList.ofList (List.finRange 2) }
  (seenSet := HAMTMapShard)
-/

end ParallelCommits
