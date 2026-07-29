import Veil

-- https://github.com/tlaplus/Examples/blob/c2641e69204ed241cdf548d9645ac82df55bfcd8/specifications/KeyValueStore/KeyValueStore.tla

veil module KeyValueStore

enum key = {K1, K2}
enum value = {noVal, v1, v2}
enum txId = {T1, T2, T3}


-- A data store mapping keys to values.
relation store : key → value → Bool
-- The set of open snapshot transactions.
relation tx : txId → Bool
-- Snapshots of the store for each transaction.
relation snapshotStore : txId → key → value → Bool
-- A log of writes performed within each transaction.
relation written : txId → key → Bool
-- The set of writes invisible to each transaction.
relation missed : txId → key → Bool

#gen_state


-- Init == \* The initial predicate.
--     /\ store = [k \in Key |-> NoVal]        \* All store values are initially NoVal.
--     /\ tx = {}                              \* The set of open transactions is initially empty.
--     /\ snapshotStore =                      \* All snapshotStore values are initially NoVal.
--         [t \in TxId |-> [k \in Key |-> NoVal]]
--     /\ written = [t \in TxId |-> {}]        \* All write logs are initially empty.
--     /\ missed = [t \in TxId |-> {}]         \* All missed writes are initially empty.
after_init {
  store K V := V == noVal
  tx T := false
  snapshotStore T K V := V == noVal
  written T K := false
  missed T K := false

}


-- OpenTx(t) ==    \* Open a new transaction.
--     /\ t \notin tx
--     /\ tx' = tx \cup {t}
--     /\ snapshotStore' = [snapshotStore EXCEPT ![t] = store]
--     /\ UNCHANGED <<written, missed, store>>
action OpenTx (t : txId) {
  require ¬ tx t
  tx t := true
  snapshotStore t K V:= store K V
}


-- Add(t, k, v) == \* Using transaction t, add value v to the store under key k.
--     /\ t \in tx
--     /\ snapshotStore[t][k] = NoVal
--     /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
--     /\ written' = [written EXCEPT ![t] = @ \cup {k}]
--     /\ UNCHANGED <<tx, missed, store>>
action Add (t : txId) (k : key) (v : value)  {
  require v ≠ noVal
  require tx t
  require snapshotStore t k noVal
  snapshotStore t k V := V == v
  written t k := true
}


-- Update(t, k, v) ==  \* Using transaction t, update the value associated with key k to v.
--     /\ t \in tx
--     /\ snapshotStore[t][k] \notin {NoVal, v}
--     /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
--     /\ written' = [written EXCEPT ![t] = @ \cup {k}]
--     /\ UNCHANGED <<tx, missed, store>>
action Update (t : txId) (k : key) (v : value)  {
  require v ≠ noVal
  require tx t
  require ¬ (snapshotStore t k noVal ∨ snapshotStore t k v)
  snapshotStore t k V := decide $ V = v
  written t k := true
}


-- Remove(t, k) == \* Using transaction t, remove key k from the store.
--     /\ t \in tx
--     /\ snapshotStore[t][k] /= NoVal
--     /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = NoVal]
--     /\ written' = [written EXCEPT ![t] = @ \cup {k}]
--     /\ UNCHANGED <<tx, missed, store>>
action Remove (t : txId) (k : key) {
  require tx t
  require ¬ snapshotStore t k noVal
  snapshotStore t k V := decide $ V = noVal
  written t k := true
}



-- RollbackTx(t) ==    \* Close the transaction without merging writes into store.
--     /\ t \in tx
--     /\ tx' = tx \ {t}
--     /\ snapshotStore' = [snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]]
--     /\ written' = [written EXCEPT ![t] = {}]
--     /\ missed' = [missed EXCEPT ![t] = {}]
--     /\ UNCHANGED store
action RollbackTx (t : txId) {
  require tx t
  tx t := false
  snapshotStore t K V :=  V == noVal
  written t K := false
  missed t K := false
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
  require tx t
  require ¬(∃k, missed t k ∧ written t k)
  store K V := if written t K then decide $ snapshotStore t K V else store K V
  tx t := false
  missed T K := if tx T then decide $ missed T K ∨ written t K else false
  snapshotStore t K V := V == noVal
  written t K := false
}


ghost relation snapshot_isolation :=
  ∀t, tx t → (∀k, (∃v, store k v ≠ snapshotStore t k v ∧ ¬ written t k) → missed t k)

ghost relation transaction_cleanup :=
  ∀t, (¬tx t) → (∀k v, snapshotStore t k v → v = noVal) ∧
  (∀k, ¬written t k) ∧ (∀k, ¬missed t k)
invariant [unique_store] store K M ∧ store K N → M = N
invariant [unique_snapshotStore] snapshotStore T K M ∧ snapshotStore T K N → M = N
invariant [Txlifecycle] snapshot_isolation ∧ transaction_cleanup

#time #gen_spec

#model_check {key := key_IndT, value := value_IndT, txId := txId_IndT } {}


end KeyValueStore
