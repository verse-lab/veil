\* Upstream license: Apache-2.0; see LICENSE.
\* Source: https://github.com/pingcap/tla-plus/blob/8ae629ddf9f5ad8efc763bff93e3e43ce0a3585d/Percolator/Percolator.tla
\* Modified locally: merged local finite-model constants from BenchPercolator.
------------------------------- MODULE Percolator ------------------------------

EXTENDS Integers, FiniteSets, Sequences, TLC

\* The set of transaction keys.
CONSTANTS KEY
ASSUME KEY # {} \* Keys cannot be empty.

\* The set of clients to execute a transaction.
CONSTANTS CLIENT

\* Primary keys of all clients (transactions).
CONSTANTS CLIENT_PRIMARY_KEY
ASSUME CLIENT_PRIMARY_KEY \in [CLIENT -> KEY]

\* $next_ts$ is the timestamp for transaction. It is increased monotonically,
\* so every transaction must have a unique start and commit ts.
VARIABLES next_ts

\* $client_state[c]$ is the state of client.
VARIABLES client_state

\* $client_ts[c]$ is a record of [start_ts: ts, commit_ts: ts].
VARIABLES client_ts

\* $client_key[c]$ is a record of [primary: key, secondary: {key},
\* pending: {key}]. Hereby, "pending" denotes the keys that are pending for
\* prewrite.
VARIABLES client_key

\* $key_data[k]$ is the set of multi-version data of the key.
\* Since we don't care about the concrete value of data, a record of
\* [ts: start_ts] is sufficient to represent one data version.
VARIABLES key_data

\* $key_lock[k]$ is the set of lock. A lock is of a record of
\* [ts: start_ts, primary: lock]. If $primary$ equals to $k$, it is a primary
\* lock, otherwise secondary lock.
VARIABLES key_lock

\* $key_write[k]$ is a sequence of committed version of the key.
\* A committed version of the key is a record of [ts: commit_ts,
\* start_ts: start_ts].
VARIABLES key_write

\* Two auxiliary variables for verifying snapshot isolation invariant. These
\* variables should not appear in a real-world implementation.
\*
\* $key_last_read_ts[k]$ denotes the last read timestamp for key $k$, this
\* should be monotonic.
\*
\* $key_si[k]$ denotes if the snapshot isolation invariant is preserved for
\* key $k$ so far.
VARIABLES key_last_read_ts, key_si

client_vars == <<client_state, client_ts, client_key>>
key_vars == <<key_data, key_lock, key_write, key_last_read_ts, key_si>>
vars == <<next_ts, client_vars, key_vars>>

--------------------------------------------------------------------------------
Range(m) ==
  {m[i] : i \in DOMAIN m}

--------------------------------------------------------------------------------
\* Checks whether there is a lock of key $k$, whose $ts$ is less or equal than
\* $ts$.
hasLockLE(k, ts) ==
  \E l \in key_lock[k] : l.ts <= ts

\* Checks whether there is a lock of key $k$ with $ts$.
hasLockEQ(k, ts) ==
  \E l \in key_lock[k] : l.ts = ts

\* Returns TRUE if a lock can be cleanup up.
\* A lock can be cleaned up iff its ts is less than or equal to $ts$.
isStaleLock(l, ts) ==
  l.ts <= ts

\* Returns TRUE if we have a stale lock for key $k$.
hasStaleLock(k, ts) ==
  \E l \in key_lock[k] : isStaleLock(l, ts)

\* Returns the writes with start_ts equals to $ts$.
findWriteWithStartTS(k, ts) ==
  {w \in Range(key_write[k]) : w.start_ts = ts}

\* Returns the writes with commit_ts equals to $ts$.
findWriteWithCommitTS(k, ts) ==
  {w \in Range(key_write[k]) : w.ts = ts}

\* Updates $key_si$ for key $k$. If a new version of key $k$ is committed with
\* $commit_ts$ < last read timestamp, consider the snapshot isolation invariant
\* for key $k$ has been violated.
checkSnapshotIsolation(k, commit_ts) ==
  IF key_last_read_ts[k] >= commit_ts
  THEN
    key_si' = [key_si EXCEPT ![k] = FALSE]
  ELSE
    UNCHANGED <<key_si>>

\* Cleans up a stale lock and its data.
\* If the lock is a secondary lock, and the assoicated primary lock is cleaned
\* up, we can clean up the lock and do,
\*   1. If the primary key is committed, we must also commit the secondary key.
\*   2. Otherwise, clean up the stale data too.
cleanupStaleLock(k, ts) ==
  \E l \in key_lock[k] :
    /\ isStaleLock(l, ts)
    /\ UNCHANGED <<key_last_read_ts>>
    /\ \/ /\ l.primary = k  \* this is a primary key, always rollback
                            \* because it is not committed.
          /\ key_data' = [key_data EXCEPT ![k] = @ \ {[ts |-> l.ts]}]
          /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
          /\ UNCHANGED <<key_write, key_si>>
       \/ /\ l.primary # k  \* this is a secondary key.
          /\ LET
                writes == findWriteWithStartTS(l.primary, l.ts)
              IN
                IF writes = {}
                THEN
                  \* the primary key is not committed, clean up the data.
                  \* Note we should always clean up the corresponding primary
                  \* lock first, then this secondary lock.
                  IF hasLockEQ(l.primary, l.ts)
                  THEN
                    /\ key_data' = [key_data EXCEPT ![l.primary] = @ \ {[ts |-> l.ts]}]
                    /\ key_lock' = [key_lock EXCEPT ![l.primary] = @ \ {l}]
                    /\ UNCHANGED <<key_write, key_si>>
                  ELSE
                    /\ key_data' = [key_data EXCEPT ![k] = @ \ {[ts |-> l.ts]}]
                    /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
                    /\ UNCHANGED <<key_write, key_si>>
                ELSE
                  \* the primary key is committed, commit the secondary key.
                  \E w \in writes :
                    /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
                    /\ key_write' = [key_write EXCEPT ![k] = Append(@, w)]
                    /\ checkSnapshotIsolation(k, w.ts)
                    /\ UNCHANGED <<key_data>>

\* Cleans up a stale lock when the client encounters one.
cleanup(c) ==
  LET
    start_ts == client_ts[c].start_ts
    primary == client_key[c].primary
    secondary == client_key[c].secondary
  IN
    \/ /\ hasStaleLock(primary, start_ts)
       /\ cleanupStaleLock(primary, start_ts)
    \/ \E k \in secondary :
         /\ hasStaleLock(k, start_ts)
         /\ cleanupStaleLock(k, start_ts)

\* Reads one key if there is no stale lock, and updates last read timestamp.
readKey(c) ==
  LET
    start_ts == client_ts[c].start_ts
    primary == client_key[c].primary
    secondary == client_key[c].secondary
  IN
    \E k \in {primary} \union secondary :
      /\ ~hasStaleLock(k, start_ts)
      /\ key_last_read_ts[k] < start_ts
      /\ key_last_read_ts' = [key_last_read_ts EXCEPT ![k] = start_ts]
      /\ UNCHANGED <<key_data, key_lock, key_write, key_si>>

\* Returns TRUE if there is no lock for key $k$, and no any newer write than
\* $ts$.
canLockKey(k, ts) ==
  LET
    writes == {w \in DOMAIN key_write[k] : key_write[k][w].ts >= ts}
  IN
    /\ key_lock[k] = {}  \* no any lock for the key.
    /\ writes = {}       \* no any newer write.

\* Locks the key and places the data.
lockKey(k, start_ts, primary) ==
  /\ key_lock' = [key_lock EXCEPT ![k] = @ \union {[ts |-> start_ts, primary |-> primary]}]
  /\ key_data' = [key_data EXCEPT ![k] = @ \union {[ts |-> start_ts]}]
  /\ UNCHANGED <<key_write, key_last_read_ts, key_si>>

\* Tries to lock primary key first, then the secondary key.
lock(c) ==
  LET
    start_ts == client_ts[c].start_ts
    primary == client_key[c].primary
    pending == client_key[c].pending
  IN
    IF primary \in pending
    THEN  \* primary key is not locked, lock it first.
      /\ canLockKey(primary, start_ts)
      /\ lockKey(primary, start_ts, primary)
      /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {primary}]
      /\ UNCHANGED <<client_state, client_ts>>
    ELSE  \* primary key has already been locked, choose a secondary key to lock.
      \E k \in pending :
        /\ canLockKey(k, start_ts)
        /\ lockKey(k, start_ts, primary)
        /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
        /\ UNCHANGED <<client_state, client_ts>>

\* Commits the primary key.
commitPrimary(c) ==
  LET
    start_ts == client_ts[c].start_ts
    commit_ts == client_ts[c].commit_ts
    primary == client_key[c].primary
  IN
    /\ hasLockEQ(primary, start_ts)
    /\ key_write' = [key_write EXCEPT ![primary] = Append(@, [ts |-> commit_ts, start_ts |-> start_ts])]
    /\ key_lock' = [key_lock EXCEPT ![primary] = @ \ {[ts |-> start_ts, primary |-> primary]}]
    /\ checkSnapshotIsolation(primary, commit_ts)
    /\ UNCHANGED <<key_data, key_last_read_ts>>

\* Assigns $start_ts$ to the transaction.
Start(c) ==
  /\ client_state[c] = "init"
  /\ next_ts' = next_ts + 1
  /\ client_state' = [client_state EXCEPT ![c] = "working"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts']
  /\ UNCHANGED <<key_vars, client_key>>

\* Does either one thing from these following threes.
\*  1. Advances to prewrite phase,
\*  2. Tries to clean up one stale lock,
\*  3. Reads one key if no stale lock.
Get(c) ==
  /\ client_state[c] = "working"
  /\ \/ /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
        /\ UNCHANGED <<next_ts, key_vars, client_ts, client_key>>
     \/ /\ cleanup(c)
        /\ UNCHANGED <<next_ts, client_vars>>
     \/ /\ readKey(c)
        /\ UNCHANGED <<next_ts, client_vars>>

\* Enters commit phase if all locks are granted, otherwise tries to lock the
\* primary lock and secondary locks.
Prewrite(c) ==
  /\ client_state[c] = "prewriting"
  /\ IF client_key[c].pending = {}
     THEN  \* all keys have been pre-written
       /\ next_ts' = next_ts + 1
       /\ client_state' = [client_state EXCEPT ![c] = "committing"]
       /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts']
       /\ UNCHANGED <<key_vars, client_key>>
     ELSE
       /\ lock(c)
       /\ UNCHANGED <<next_ts>>

\* If we commit the primary key successfully, we can think the transaction is
\* committed.
Commit(c) ==
  /\ client_state[c] = "committing"
  /\ commitPrimary(c)
  /\ client_state' = [client_state EXCEPT ![c] = "committed"]
  /\ UNCHANGED <<next_ts, client_ts, client_key>>

\* We can choose to abort at any time if not committed. Hereby, the aborted
\* state unifies client crash, client abort and transaction failure. The client
\* simply halts when aborted, and leaves cleanup to future transaction.
Abort(c) ==
  /\ client_state[c] # "committed"
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, key_vars>>

ClientOp(c) ==
  \/ Start(c)
  \/ Get(c)
  \/ Prewrite(c)
  \/ Commit(c)
  \/ Abort(c)

Next == \E c \in CLIENT : ClientOp(c)

Init ==
  LET
    \* Selects a primary key and use the rest for the secondary keys.
    chooseKey(ks, c) ==
    LET
      primary == CLIENT_PRIMARY_KEY[c]
    IN
      [primary |-> primary,
       secondary |-> ks \ {primary},
       pending |-> ks]
  IN
    /\ next_ts = 0
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
    /\ client_key = [c \in CLIENT |-> chooseKey(KEY, c)]
    /\ key_lock = [k \in KEY |-> {}]
    /\ key_data = [k \in KEY |-> {}]
    /\ key_write = [k \in KEY |-> <<>>]
    /\ key_last_read_ts = [k \in KEY |-> 0]
    /\ key_si = [k \in KEY |-> TRUE]

PercolatorSpec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------
NextTsTypeInv ==
  next_ts \in Nat

ClientStateTypeInv ==
  client_state \in [CLIENT -> {"init", "working", "prewriting",
                               "committing", "committed", "aborted"}]

ClientTsTypeInv ==
  client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat]]

ClientKeyTypeInv ==
  client_key \in [CLIENT -> [primary : KEY,
                             secondary : SUBSET KEY,
                             pending : SUBSET KEY]]

KeyDataTypeInv ==
  key_data \in [KEY -> SUBSET [ts : Nat]]

KeyLockTypeInv ==
  key_lock \in [KEY -> SUBSET [ts : Nat, primary : KEY]]

KeyWriteTypeInv ==
  key_write \in [KEY -> Seq([ts : Nat, start_ts : Nat])]

KeyLastReadTsTypeInv ==
  key_last_read_ts \in [KEY -> Nat]

KeySiTypeInv ==
  key_si \in [KEY -> BOOLEAN]

TypeInvariant ==
  /\ NextTsTypeInv
  /\ ClientStateTypeInv
  /\ ClientTsTypeInv
  /\ ClientKeyTypeInv
  /\ KeyDataTypeInv
  /\ KeyLockTypeInv
  /\ KeyWriteTypeInv
  /\ KeyLastReadTsTypeInv
  /\ KeySiTypeInv

--------------------------------------------------------------------------------
\* The committed write timestamp of one key must be in order, and no two writes
\* can overlap. For each write, the commit_ts should be strictly greater than
\* start_ts.
WriteConsistency ==
  /\ \A k \in KEY :
       \A n \in 1..Len(key_write[k]) - 1 :
         key_write[k][n].ts < key_write[k][n + 1].start_ts
  /\ \A k \in KEY :
       \A n \in 1..Len(key_write[k]) :
         key_write[k][n].start_ts < key_write[k][n].ts

LockConsistency ==
  \* There should be at most one lock for each key.
  /\ \A k \in KEY :
       Cardinality(key_lock[k]) <= 1
  \* When the client finishes prewriting and is ready for commit, if the
  \* primary lock exists, all secondary locks should exist.
  /\ \A c \in CLIENT :
       (/\ client_state[c] = "committing"
        /\ hasLockEQ(client_key[c].primary, client_ts[c].start_ts)
       ) =>
         \A k \in client_key[c].secondary :
           hasLockEQ(k, client_ts[c].start_ts)

CommittedConsistency ==
  \A c \in CLIENT :
    LET
      start_ts == client_ts[c].start_ts
      commit_ts == client_ts[c].commit_ts
      primary == client_key[c].primary
      secondary == client_key[c].secondary
      w == [ts |-> commit_ts, start_ts |-> start_ts]
    IN
      client_state[c] = "committed" =>
        \* The primary key lock must be cleaned up, and no any older lock.
        /\ ~hasLockLE(primary, start_ts)
        /\ findWriteWithCommitTS(primary, commit_ts) = {w}
        /\ [ts |-> start_ts] \in key_data[primary]
        /\ \A k \in secondary :
           \* The secondary key lock can be empty or not.
           /\ \/ /\ ~hasLockEQ(k, start_ts)
                 /\ findWriteWithCommitTS(k, commit_ts) = {w}
                 /\ ~hasLockLE(k, start_ts - 1)
              \/ /\ hasLockEQ(k, start_ts)
                 /\ findWriteWithCommitTS(k, commit_ts) = {}
                 /\ (Len(key_write[k]) > 0 =>
                      \* Lock has not been cleaned up, so the committed
                      \* timestamp of last write must be less than lock's
                      \* start_ts.
                      key_write[k][Len(key_write[k])].ts < start_ts)
           /\ [ts |-> start_ts] \in key_data[k]

\* If one transaction is aborted, there should be no committed primary key.
AbortedConsistency ==
  \A c \in CLIENT :
    (/\ client_state[c] = "aborted"
     /\ client_ts[c].commit_ts # 0
    ) =>
      findWriteWithCommitTS(client_key[c].primary, client_ts[c].commit_ts) = {}

\* Snapshot isolation invariant should be preserved.
SnapshotIsolation ==
  \A k \in KEY :
    key_si[k] = TRUE

--------------------------------------------------------------------------------
THEOREM Safety ==
  PercolatorSpec => [](/\ TypeInvariant
                       /\ WriteConsistency
                       /\ LockConsistency
                       /\ CommittedConsistency
                       /\ AbortedConsistency
                       /\ SnapshotIsolation)

\* ---- Merged from BenchPercolator, which EXTENDS this module. ----
CONSTANTS c1, c2, c3
Key == 1..4
Client == {c1, c2, c3}
ClientPrimaryKey == c1 :> 1 @@ c2 :> 2 @@ c3 :> 3
================================================================================
