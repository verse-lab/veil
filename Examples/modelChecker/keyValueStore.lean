import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main

import Veil.Core.Tools.Checker.Concrete.modelCheckerView
import ProofWidgets.Component.HtmlDisplay
/-
Key-Value Store with Snapshot Isolation

This module specifies a simple key-value store that exhibits snapshot isolation.
In snapshot isolation, each transaction sees a consistent snapshot of the database
as it existed at the start of the transaction.

TLA⁺ Specification Author: Andrew Helwer

Key Properties:
- If two concurrent transactions write to the same key, the one committing later
  will be rejected (write-write conflict detection)
- If they write to different keys, both transactions will succeed
- Each transaction operates on its own snapshot of the store
- Write conflicts are detected by tracking which keys each transaction has written
  and which writes it has "missed" from other concurrent transactions

For a more detailed TLA⁺ specification of snapshot isolation, see:
https://github.com/tlaplus/Examples/blob/master/specifications/KeyValueStore/KeyValueStore.tla
-/
veil module KeyValueStore

/- Constants -/
-- type key    -- The set of all keys.
enum key = {K1, K2}
-- type value  -- The set of all values.
enum value = {noVal, v1, v2}
-- type txId   -- The set of all transaction IDs.
enum txId = {T1, T2}



/- Variables -/
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
  -- tx T := tx T ∨ t = T
  tx t := true
  snapshotStore t K V := store K V
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
action CloseTx (t : txId) (otherTx : txId) {
  require tx t
  require ¬(∃k, missed t k ∧ written t k)
  store K V := if written t K then decide $ snapshotStore t K V else store K V
  tx t := false
  missed T K := if tx T then decide $ missed T K ∨ written t K else false
  -- Here introduces error in the spec, originally is uncommented.
  -- snapshotStore t K V := V == noVal
  -- written t K := false
}


ghost relation snapshot_isolation :=
  -- ∀t, tx t → (∀k, (∃v, store k v ≠ snapshotStore t k v ∧ ¬ written t k) → missed t k)
  ∀t, tx t → (∀k, (∃v, store k v ≠ snapshotStore t k v ∧ ¬ written t k) → missed t k)

ghost relation transaction_cleanup :=
  ∀t, (¬tx t) → (∀k v, snapshotStore t k v → v = noVal) ∧
  (∀k, ¬written t k) ∧ (∀k, ¬missed t k)
invariant [unique_store] store K M ∧ store K N → M = N
invariant [unique_snapshotStore] snapshotStore T K M ∧ snapshotStore T K N → M = N
-- invariant [Txlifecycle] snapshot_isolation ∧ transaction_cleanup
invariant [Txlifecycle] (  ∀t, tx t → (∀k, (∃v, store k v ≠ snapshotStore t k v ∧ ¬ written t k) → missed t k)) ∧
  (∀t, (¬tx t) → (∀k v, snapshotStore t k v → v = noVal) ∧
  (∀k, ¬written t k) ∧ (∀k, ¬missed t k))

#gen_spec
-- #time #check_invariants


#prepareExecution

#finitizeTypes key, value, txId
-- #finitizeTypes (Fin 2), value, (Fin 2)



def view (st : StateConcrete) := hash st
def modelCheckerResult' :=(runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => Txlifecycle ρ σ) ((fun ρ σ => true)) {} view).snd
#eval modelCheckerResult'.seen.size
def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM {} (collectTrace' modelCheckerResult'))
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />


end KeyValueStore
