import Veil

-- https://github.com/tlaplus/Examples/blob/c2641e69204ed241cdf548d9645ac82df55bfcd8/specifications/KeyValueStore/KeyValueStore.tla

veil module KeyValueStore

enum key = {K1, K2}
enum value = {noVal, v1, v2}
enum txId = {T1, T2}


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
-- Choose something to represent the absence of a value.
-- immutable individual noVal : value

#gen_state

after_init {
  store K V := V == noVal
  tx T := false
  snapshotStore T K V := V == noVal
  written T K := false
  missed T K := false

}

action OpenTx (t : txId) {
  require ¬ tx t
  tx t := true
  snapshotStore t K V:= store K V
}

action Add (t : txId) (k : key) (v : value)  {
  require v ≠ noVal
  require tx t
  require snapshotStore t k noVal
  snapshotStore t k V := V == v
  written t k := true
}

action Update (t : txId) (k : key) (v : value)  {
  require v ≠ noVal
  require tx t
  require ¬ (snapshotStore t k noVal ∨ snapshotStore t k v)
  snapshotStore t k V := decide $ V = v
  written t k := true
}

action Remove (t : txId) (k : key) {
  require tx t
  require ¬ snapshotStore t k noVal
  snapshotStore t k V := decide $ V = noVal
  written t k := true
}

action RollbackTx (t : txId) {
  require tx t
  tx t := false
  snapshotStore t K V :=  V == noVal
  written t K := false
  missed t K := false
}

action CloseTx (t : txId) {
  require tx t
  require ¬(∃k, missed t k ∧ written t k)
  store K V := if written t K then decide $ snapshotStore t K V else store K V
  tx t := false
  missed T K := if tx T then decide $ missed T K ∨ written t K else false
  -- Here introduces error in the spec, originally is uncommented.
  snapshotStore t K V := V == noVal
  written t K := false
}


ghost relation snapshot_isolation :=
  -- ∀t, tx t → (∀k, (∃v, store k v ≠ snapshotStore t k v ∧ ¬ written t k) → missed t k)
  ∀t, tx t → (∀k, (∃v, store k v ≠ snapshotStore t k v ∧ ¬ written t k) → missed t k)

ghost relation transaction_cleanup :=
  ∀t, (¬tx t) → (∀k v, snapshotStore t k v → v = noVal) ∧
  (∀k, ¬written t k) ∧ (∀k, ¬missed t k)
invariant [unique_store] store K M ∧ store K N → M = N
invariant [unique_snapshotStore] snapshotStore T K M ∧ snapshotStore T K N → M = N
invariant [Txlifecycle] snapshot_isolation ∧ transaction_cleanup

#time #gen_spec

#check_invariants

#model_check {key := key_IndT, value := value_IndT, txId := txId_IndT } {}


end KeyValueStore
