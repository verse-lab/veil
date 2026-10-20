module

public import Veil

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

#model_check compiled
{ key := Fin 2,
  value := Fin 2,
  txId := Fin 3,
  KeySet := OrdList (Fin 2),
  TxIdSet := OrdList (Fin 3) } {}
  (maxDepth := 2) (sequential := true)

end KeyValueStoreRe
