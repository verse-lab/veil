module

public import Veil

/-!
Upstream license: Apache-2.0; see Benchmarks/TLA/Percolator/LICENSE.
Modified locally: translated and adapted to Veil.

Safety translation of PingCAP's Percolator, including its auxiliary SI state.
Source (Apache-2.0):
https://github.com/pingcap/tla-plus/blob/8ae629ddf9f5ad8efc763bff93e3e43ce0a3585d/Percolator/Percolator.tla
-/

veil module Percolator

type key
type client
type KeySet
type TimestampSet

enum ClientState = {init, working, prewriting, committing, committed, aborted}

@[veil_decl]
structure ClientTS where
  start_ts : Nat
  commit_ts : Nat

@[veil_decl]
structure ClientKeys (key KeySet : Type) where
  primary : key
  secondary : KeySet
  pending : KeySet

@[veil_decl]
structure Lock (key : Type) where
  ts : Nat
  primary : key

@[veil_decl]
structure Write where
  ts : Nat
  start_ts : Nat

type LockSet
instantiate keys : TSet key KeySet
instantiate timestamps : TSet Nat TimestampSet
instantiate locks : TSet (Lock key) LockSet

immutable individual AllKeys : KeySet
immutable function CLIENT_PRIMARY_KEY : client → key

individual next_ts : Nat
function client_state : client → ClientState
function client_ts : client → ClientTS
function client_key : client → ClientKeys key KeySet
function key_data : key → TimestampSet
function key_lock : key → LockSet
function key_write : key → List Write
function key_last_read_ts : key → Nat
function key_si : key → Bool

set_option veil.deferVCGeneration true

veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

assumption [nonempty_keys] ¬ keys.isEmpty AllKeys
assumption [all_keys_complete] ∀ k : key, k ∈ AllKeys

-- hasLockLE(k, ts) == ∃ l ∈ key_lock[k] : l.ts <= ts. ts is an integer: the
-- source also calls it with start_ts - 1.
ghost relation hasLockLE (k : key) (ts : Int) :=
  ∃ l : { l // l ∈ key_lock k }, (l.val.ts : Int) ≤ ts

-- hasLockEQ(k, ts) == ∃ l ∈ key_lock[k] : l.ts = ts
ghost relation hasLockEQ (k : key) (ts : Nat) :=
  ∃ l : { l // l ∈ key_lock k }, l.val.ts = ts

-- hasStaleLock(k, ts) == ∃ l ∈ key_lock[k] : isStaleLock(l, ts), where
-- isStaleLock(l, ts) == l.ts <= ts.
ghost relation hasStaleLock (k : key) (ts : Nat) :=
  ∃ l : { l // l ∈ key_lock k }, l.val.ts ≤ ts

-- findWriteWithCommitTS(k, ts) = { [ts |-> ts, start_ts |-> startTS] }.
-- Range ignores sequence multiplicities, so use existence and universal equality.
ghost relation uniqueWrite (k : key) (ts startTS : Nat) :=
  (∃ w ∈ key_write k, w.ts = ts ∧ w.start_ts = startTS) ∧
  (∀ w ∈ key_write k, w.ts = ts → w.start_ts = startTS)

ghost relation noWrite (k : key) (ts : Nat) :=
  ¬ ∃ w ∈ key_write k, w.ts = ts

-- checkSnapshotIsolation(k, commit_ts): FALSE iff last read >= commit_ts.
procedure checkSnapshotIsolation (k : key) (commitTS : Nat) {
  if key_last_read_ts k ≥ commitTS then
    key_si k := false
}

-- cleanupStaleLock(k, ts): every stale lock and matching primary write is a
-- possible witness. Helpers are procedures, not independently enabled actions.
procedure cleanupStaleLock (k : key) (ts : Nat) {
  let oldLocks := key_lock k
  let chosen : { l // l ∈ oldLocks } :| chosen.val.ts ≤ ts
  let l := chosen.val
  if l.primary = k then
    key_data k := timestamps.remove l.ts (key_data k)
    key_lock k := locks.remove l (key_lock k)
  else
    let writes := (key_write l.primary).filter (fun w => w.start_ts == l.ts)
    if writes.isEmpty then
      if hasLockEQ l.primary l.ts then
        -- Source removes l itself from the primary lock set, not a new lock.
        key_data l.primary := timestamps.remove l.ts (key_data l.primary)
        key_lock l.primary := locks.remove l (key_lock l.primary)
      else
        key_data k := timestamps.remove l.ts (key_data k)
        key_lock k := locks.remove l (key_lock k)
    else
      let chosenWrite : { w // w ∈ writes } :| true
      let w := chosenWrite.val
      key_lock k := locks.remove l (key_lock k)
      key_write k := key_write k ++ [w]
      checkSnapshotIsolation k w.ts
}

-- canLockKey: no lock and no committed timestamp >= this start timestamp.
ghost relation canLockKey (k : key) (ts : Nat) :=
  locks.isEmpty (key_lock k) ∧ ¬ ∃ w ∈ key_write k, w.ts ≥ ts

-- Init: primary and secondary keys are retained as state, even though fixed.
after_init {
  next_ts := 0
  client_state C := init
  client_ts C := { start_ts := 0, commit_ts := 0 }
  client_key C := {
    primary := CLIENT_PRIMARY_KEY C
    secondary := keys.remove (CLIENT_PRIMARY_KEY C) AllKeys
    pending := AllKeys }
  key_data K := timestamps.empty
  key_lock K := locks.empty
  key_write K := []
  key_last_read_ts K := 0
  key_si K := true
}

-- Start(c): start_ts reads next_ts', not next_ts.
action Start (c : client) {
  require client_state c = init
  next_ts := next_ts + 1
  client_state c := working
  client_ts c := { client_ts c with start_ts := next_ts }
}

-- Get(c) does one of three things: advance to the prewrite phase, clean up one
-- stale lock (cleanup(c)), or read one key without a stale lock (readKey(c)).
action Get (c : client) {
  require client_state c = working
  let start_ts := (client_ts c).start_ts
  let primary := (client_key c).primary
  let secondary := (client_key c).secondary
  let choice ← pick (Fin 3)
  if choice = 0 then
    client_state c := prewriting
  else if choice = 1 then
    -- cleanup(c): the primary key or a secondary key with a stale lock.
    let k : key :| (k = primary ∨ k ∈ secondary) ∧ hasStaleLock k start_ts
    cleanupStaleLock k start_ts
  else
    -- readKey(c): the last read timestamp increases strictly.
    let k : key :| (k = primary ∨ k ∈ secondary) ∧ ¬ hasStaleLock k start_ts ∧
      key_last_read_ts k < start_ts
    key_last_read_ts k := start_ts
}

-- Prewrite(c): lock primary first, otherwise choose any pending secondary.
action Prewrite (c : client) {
  require client_state c = prewriting
  let ck := client_key c
  if keys.isEmpty ck.pending then
    next_ts := next_ts + 1
    client_state c := committing
    client_ts c := { client_ts c with commit_ts := next_ts }
  else
    let chosen : { k // k ∈ ck.pending } :|
      (ck.primary ∈ ck.pending → chosen.val = ck.primary) ∧
        canLockKey chosen.val (client_ts c).start_ts
    let k := chosen.val
    key_lock k := locks.insert
      { ts := (client_ts c).start_ts, primary := ck.primary } (key_lock k)
    key_data k := timestamps.insert (client_ts c).start_ts (key_data k)
    client_key c := { ck with pending := keys.remove k ck.pending }
}

-- Commit(c): only primary is committed; secondary cleanup is performed by Get.
action Commit (c : client) {
  require client_state c = committing
  let ts := client_ts c
  let primary := (client_key c).primary
  require hasLockEQ primary ts.start_ts
  key_write primary := key_write primary ++ [{ ts := ts.commit_ts, start_ts := ts.start_ts }]
  key_lock primary := locks.remove { ts := ts.start_ts, primary } (key_lock primary)
  checkSnapshotIsolation primary ts.commit_ts
  client_state c := committed
}

-- Abort(c) also permits an already-aborted self-loop, exactly as upstream.
action Abort (c : client) {
  require client_state c ≠ committed
  client_state c := aborted
}

-- Adjacent write versions: w[n].ts < w[n+1].start_ts; every start < commit.
invariant [WriteConsistency]
  ∀ k : key,
    (∀ pair ∈ (key_write k).zip (key_write k).tail, pair.1.ts < pair.2.start_ts) ∧
    (∀ w ∈ key_write k, w.start_ts < w.ts)

invariant [LockConsistency]
  (∀ k : key, locks.count (key_lock k) ≤ 1) ∧
  (∀ c : client,
    client_state c = committing ∧
      hasLockEQ (client_key c).primary (client_ts c).start_ts →
      ∀ k ∈ (client_key c).secondary, hasLockEQ k (client_ts c).start_ts)

invariant [CommittedConsistency]
  ∀ c : client, client_state c = committed →
    let startTS := (client_ts c).start_ts
    let commitTS := (client_ts c).commit_ts
    let primary := (client_key c).primary
    ¬ hasLockLE primary startTS ∧ uniqueWrite primary commitTS startTS ∧
    startTS ∈ key_data primary ∧
    ∀ k ∈ (client_key c).secondary,
      ((¬ hasLockEQ k startTS ∧ uniqueWrite k commitTS startTS ∧
          -- TLA+ uses integer subtraction, including the startTS=0 case.
          ¬ hasLockLE k ((startTS : Int) - 1)) ∨
        (hasLockEQ k startTS ∧ noWrite k commitTS ∧
          -- Len(key_write[k]) > 0 => the last write's ts < start_ts.
          ∀ w ∈ (key_write k).getLast?, w.ts < startTS)) ∧
      startTS ∈ key_data k

invariant [AbortedConsistency]
  ∀ c : client,
    client_state c = aborted ∧ (client_ts c).commit_ts ≠ 0 →
      noWrite (client_key c).primary (client_ts c).commit_ts

invariant [SnapshotIsolation] ∀ k : key, key_si k = true

#gen_spec
#gen_executable

/- EVAL
#model_check compiled
  { key := Fin 4, client := Fin 3, KeySet := OrdList (Fin 4),
    TimestampSet := OrdList Nat, LockSet := OrdList (Lock (Fin 4)) }
  { AllKeys := TSet.ofList (List.finRange 4), CLIENT_PRIMARY_KEY := Fin.castSucc }
  (seenSet := HAMTMapShard)
-/

-- -- Boundary case: one primary key, no secondary keys.
-- #model_check
--   { key := Fin 1, client := Fin 1, KeySet := OrdList (Fin 1),
--     TimestampSet := OrdList Nat, LockSet := OrdList (Lock (Fin 1)) }
--   { AllKeys := TSet.ofList (List.finRange 1), CLIENT_PRIMARY_KEY := id }
--   (fingerprintType := UInt64)

end Percolator
