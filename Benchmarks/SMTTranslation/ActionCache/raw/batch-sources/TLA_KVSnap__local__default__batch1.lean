module

public import Veil
public import Veil.Util.Permutations

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
set_option veil.experimental.bmcCache false

-- source: KVsnap.tla, checked with MCKVsnap.cfg
-- https://github.com/tlaplus/Examples/blob/master/specifications/KeyValueStore/KVsnap.tla
-- (**************************************************************************)
-- (* Pluscal algorithm for a simple key-value store with snapshot isolation  *)
-- (* This version has atomic updates of store and missed sets of txns       *)
-- (**************************************************************************)
--
-- Translation notes:
--   - `NoVal` is the only value outside `TxId`, so `TxId \union {NoVal}` is `Option txId`
--     (`none` = `NoVal`).
--   - `SetToSeq(S)` is a `CHOOSE`; here it is fixed to "ascending key order". Within a
--     transaction this only orders the reads among themselves and the writes among
--     themselves, which `ClientCentric` never compares (every read precedes every write).
--   - `TypeOK` is enforced by the Veil types and is not restated.
--   - Out of scope: the fairness conjuncts of `Spec` and the temporal property
--     `Termination`. The `termination` clause below only reports stuck states where some
--     transaction is not `Done`, matching TLC's deadlock check given the `Terminating`
--     stutter step.

veil module KVsnapNew

-- CONSTANTS   Key,            \* The set of all keys.
--             TxId,           \* The set of all transaction IDs.
--             NoVal           \* NoVal, which all keys are initialized with.
type key
type txId
type keySet
instantiate kset : TSet key keySet
-- `ClientCentric` quantifies over all keys (states) and `Range(ops)` over all TxIds
instantiate keyEnum : Veil.Enumeration key
instantiate txEnum : Veil.Enumeration txId

-- PlusCal labels
enum pcLabel = { START, READ, UPDATE, COMMIT, Done }

/-! ## ClientCentric (only what `Serializability` needs)

`CC == INSTANCE ClientCentric WITH Keys <- Key, Values <- TxId \union {NoVal}`. A database
state is a function `κ → ν`; states are compared pointwise over the list of all keys. -/

-- Operation == [op: {"read", "write"}, key: Keys, value: Values]
@[veil_decl]
inductive OpKind where
  | read
  | write

@[veil_decl]
structure Operation (κ ν : Type) where
  op : OpKind
  key : κ
  value : ν

-- ExecutionElem == [parentState: State, transaction: Transaction]
structure ExecutionElem (κ ν : Type) where
  parentState : κ → ν
  transaction : List (Operation κ ν)

namespace CC

/-- Equality of two states `[Keys -> Values]`, given the list of all keys. -/
def stateEq {κ ν : Type} [DecidableEq ν] (keys : List κ) (s₁ s₂ : κ → ν) : Bool :=
  keys.all fun k => s₁ k == s₂ k

/-- `Index(executionStates(execution), s)`: the first index (TLC's `CHOOSE` over `1..n`). -/
def stateIndex {κ ν : Type} [DecidableEq ν] (keys : List κ) (states : List (κ → ν)) (s : κ → ν) : Nat :=
  states.findIdx (stateEq keys · s)

-- effects(state, transaction) ==
--        ReduceSeq(LAMBDA o, newState: IF o.op = "write" THEN [newState EXCEPT ![o.key] = o.value] ELSE newState, transaction, state)
def effects {κ ν : Type} [DecidableEq κ] (state : κ → ν) (txn : List (Operation κ ν)) : κ → ν :=
  txn.foldl (fun st o =>
    if o.op = .write then fun k => if k = o.key then o.value else st k else st) state

-- executions(initialState, transactions) ==
--   LET orderings == PermSeqs(transactions)
--       accummulator == [ execution |-> <<>>, nextState |-> initialState ]
--   IN { LET executionAcc == ReduceSeq(
--                             LAMBDA t, acc: [ execution |-> Append(acc.execution, [parentState |-> acc.nextState, transaction |-> t])
--                                            , nextState |-> effects(acc.nextState,t) ],
--                             ordering, accummulator)
--        IN executionAcc.execution
--      : ordering \in orderings }
-- `transactions` must be duplicate-free (it is a set in TLA+).
def executions {κ ν : Type} [DecidableEq κ] (initialState : κ → ν) (transactions : List (List (Operation κ ν))) :
    List (List (ExecutionElem κ ν)) :=
  (Veil.List.permutations transactions).map fun ordering =>
    (ordering.foldl (fun (acc : List (ExecutionElem κ ν) × (κ → ν)) t =>
      (acc.1 ++ [⟨acc.2, t⟩], effects acc.2 t)) ([], initialState)).1

-- parentState(execution, transaction) ==
--   LET ind == CHOOSE i \in 1..Len(execution): execution[i].transaction = transaction
--   IN execution[ind].parentState
-- `none` when `transaction` is not in `execution` (never the case for `CT_SER` below).
def parentState {κ ν : Type} [DecidableEq κ] [DecidableEq ν] (execution : List (ExecutionElem κ ν))
    (transaction : List (Operation κ ν)) : Option (κ → ν) :=
  (execution.find? (·.transaction == transaction)).map (·.parentState)

-- beforeOrEqualInExecution(execution, state1, state2) ==
--   LET states == executionStates(execution)
--   IN  Index(states, state1) <= Index(states, state2)
def beforeOrEqualInExecution {κ ν : Type} [DecidableEq ν] (keys : List κ) (execution : List (ExecutionElem κ ν))
    (state1 state2 : κ → ν) : Bool :=
  let states := execution.map (·.parentState)
  stateIndex keys states state1 ≤ stateIndex keys states state2

-- The condition defining `ReadStates(execution, operation, transaction)`, for one `s \in Se`:
--   /\ beforeOrEqualInExecution(execution, s, sp)
--   /\ \/ s[operation.key] = operation.value
--      \/ \E write \in SeqToSet(transaction):
--         /\ write.op = "write" /\ write.key = operation.key /\ write.value = operation.value
--         /\ earlierInTransaction(transaction, write, operation)
--      \/ operation.op = "write"
def isReadState {κ ν : Type} [DecidableEq κ] [DecidableEq ν] (keys : List κ) (execution : List (ExecutionElem κ ν))
    (transaction : List (Operation κ ν)) (sp : κ → ν) (operation : Operation κ ν) (s : κ → ν) : Bool :=
  beforeOrEqualInExecution keys execution s sp &&
    (s operation.key == operation.value ||
     transaction.any (fun w =>
       w.op == .write && w.key == operation.key && w.value == operation.value &&
       transaction.idxOf w < transaction.idxOf operation) ||
     operation.op == .write)

-- Complete(execution, transaction, state) ==
--   LET setOfAllReadStatesOfOperation(transactionOperations) ==
--         { ReadStates(execution, operation, transaction) : operation \in SeqToSet(transactionOperations) }
--       readStatesForEmptyTransaction == { s \in SeqToSet(executionStates(execution)) : beforeOrEqualInExecution(execution, s, parentState(execution, transaction)) }
--   IN state \in INTERSECTION(setOfAllReadStatesOfOperation(transaction) \union { readStatesForEmptyTransaction } )
-- Membership in the intersection is checked directly instead of building the sets.
def complete {κ ν : Type} [DecidableEq κ] [DecidableEq ν] (keys : List κ) (execution : List (ExecutionElem κ ν))
    (transaction : List (Operation κ ν)) (state : κ → ν) : Bool :=
  match parentState execution transaction with
  | none => false
  | some sp =>
    (execution.any fun e => stateEq keys e.parentState state) &&
      beforeOrEqualInExecution keys execution state sp &&
      transaction.all fun operation => isReadState keys execution transaction sp operation state

-- CT_SER(transaction, execution) ==
--   Complete(execution, transaction, parentState(execution, transaction))
def CT_SER {κ ν : Type} [DecidableEq κ] [DecidableEq ν] (keys : List κ) (transaction : List (Operation κ ν))
    (execution : List (ExecutionElem κ ν)) : Bool :=
  match parentState execution transaction with
  | none => false
  | some sp => complete keys execution transaction sp

-- satisfyIsolationLevel(initialState, transactions, commitTest(_,_)) ==
--   \E execution \in executions(initialState, transactions): \A transaction \in transactions:
--     commitTest(transaction, execution)
-- Serializability(initialState, transactions) == satisfyIsolationLevel(initialState, transactions, CT_SER)
def Serializability {κ ν : Type} [DecidableEq κ] [DecidableEq ν] (keys : List κ) (initialState : κ → ν)
    (transactions : List (List (Operation κ ν))) : Bool :=
  (executions initialState transactions).any fun execution =>
    transactions.all fun transaction => CT_SER keys transaction execution

end CC

-- VARIABLES store, tx, missed, pc, snapshotStore, read_keys, write_keys, ops
-- \* A data store mapping keys to values
function store : key → Option txId
-- \* The set of open snapshot transactions
relation tx : txId → Bool
-- \* The set of writes invisible to each transaction
function missed : txId → keySet
function pc : txId → pcLabel
-- \* local snapshot of the store
function snapshotStore : txId → key → Option txId
-- \* read keys  for the transaction
function read_keys : txId → keySet
-- \* write keys for the transaction
function write_keys : txId → keySet
-- \* a log of reads & writes this transaction executes; used for interfacing to CC
function ops : txId → List (Operation key (Option txId))

#gen_state

-- Init == (* Global variables *)
--         /\ store = [k \in Key |-> NoVal]
--         /\ tx = {}
--         /\ missed = [t \in TxId |-> {}]
--         (* Process t *)
--         /\ snapshotStore = [self \in TxId |-> [k \in Key |-> NoVal]]
--         /\ read_keys = [self \in TxId |-> {}]
--         /\ write_keys = [self \in TxId |-> {}]
--         /\ ops = [self \in TxId |-> <<>>]
--         /\ pc = [self \in ProcSet |-> "START"]
after_init {
  store K := none
  tx T := false
  missed T := kset.empty
  snapshotStore T K := none
  read_keys T := kset.empty
  write_keys T := kset.empty
  ops T := []
  pc T := START
}

-- START(self) == /\ pc[self] = "START"
--                /\ tx' = (tx \union {self})
--                /\ snapshotStore' = [snapshotStore EXCEPT ![self] = store]
--                /\ \E rk \in SUBSET Key \ { {} }:
--                     \E wk \in SUBSET Key \ { {} }:
--                       /\ read_keys' = [read_keys EXCEPT ![self] = rk]
--                       /\ write_keys' = [write_keys EXCEPT ![self] = wk]
--                /\ pc' = [pc EXCEPT ![self] = "READ"]
--                /\ UNCHANGED << store, missed, ops >>
-- (`SUBSET Key \ { {} }` parses as `(SUBSET Key) \ { {} }`: the non-empty subsets.)
action Start (self : txId) {
  require pc self = START
  tx self := true
  snapshotStore self K := store K
  let rk :| ¬ kset.isEmpty rk
  let wk :| ¬ kset.isEmpty wk
  read_keys self := rk
  write_keys self := wk
  pc self := READ
}

-- READ(self) == /\ pc[self] = "READ"
--               /\ ops' = [ops EXCEPT ![self] = ops[self] \o SetToSeq({rOp(k, snapshotStore[self][k]): k \in read_keys[self]})]
--               /\ pc' = [pc EXCEPT ![self] = "UPDATE"]
--               /\ UNCHANGED << store, tx, missed, snapshotStore, read_keys, write_keys >>
action Read (self : txId) {
  require pc self = READ
  ops self := ops self ++
    (kset.toList (read_keys self)).map (fun k => ⟨.read, k, snapshotStore self k⟩)
  pc self := UPDATE
}

-- UPDATE(self) == /\ pc[self] = "UPDATE"
--                 /\ snapshotStore' = [snapshotStore EXCEPT ![self] = [k \in Key |-> IF k \in write_keys[self] THEN self ELSE snapshotStore[self][k] ]]
--                 /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
--                 /\ UNCHANGED << store, tx, missed, read_keys, write_keys, ops >>
action Update (self : txId) {
  require pc self = UPDATE
  snapshotStore self K := if K ∈ write_keys self then some self else snapshotStore self K
  pc self := COMMIT
}

-- COMMIT(self) == /\ pc[self] = "COMMIT"
--                 /\ IF missed[self] \intersect write_keys[self] = {}
--                       THEN /\ tx' = tx \ {self}
--                            /\ missed' = [o \in TxId |-> IF o \in tx' THEN missed[o] \union write_keys[self] ELSE missed[o]]
--                            /\ store' = [k \in Key |-> IF k \in write_keys[self] THEN snapshotStore[self][k] ELSE store[k] ]
--                            /\ ops' = [ops EXCEPT ![self] = ops[self] \o SetToSeq({wOp(k, self): k \in write_keys[self]})]
--                       ELSE /\ TRUE
--                            /\ UNCHANGED << store, tx, missed, ops >>
--                 /\ pc' = [pc EXCEPT ![self] = "Done"]
--                 /\ UNCHANGED << snapshotStore, read_keys, write_keys >>
-- Reads: `missed'` reads the new `tx`, so `tx` is updated first; nothing else reads a
-- field that this action changes.
action Commit (self : txId) {
  require pc self = COMMIT
  if kset.isEmpty (kset.intersection (missed self) (write_keys self)) then
    tx self := false
    missed O := if tx O then kset.union (missed O) (write_keys self) else missed O
    store K := if K ∈ write_keys self then snapshotStore self K else store K
    ops self := ops self ++
      (kset.toList (write_keys self)).map (fun k => ⟨.write, k, some self⟩)
  pc self := Done
}

-- Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
--                /\ UNCHANGED vars
termination [AllDone] ∀ t, pc t = Done

-- InitialState == [k \in Key |-> NoVal]
-- Serialization == CC!Serializability(InitialState, Range(ops))
-- \* Serializability would not be satisfied due to write-skew
ghost relation serialization :=
  CC.Serializability keyEnum.allValues (fun _ => (none : Option txId))
    ((txEnum.allValues.map ops).eraseDups) = true

safety [Serialization] serialization


#gen_spec
run_cmd discard <| _root_.Veil.Verifier.waitFilteredSync _root_.Veil.Verifier.isDoesNotThrow

run_cmd Lean.Elab.Command.liftTermElabM do
  IO.FS.writeFile "/tmp/veil-action-cache/results/batch-events/TLA_KVSnap__local__default__batch1.ready" (toString (← IO.monoMsNow))

set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.finiteModelFind true

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_KVSnap__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_0] {
  any action
  assert (¬ serialization)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_KVSnap__d1__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_KVSnap__d1__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_KVSnap__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_KVSnap__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_1] {
  any 2 actions
  assert (¬ serialization)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_KVSnap__d2__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_KVSnap__d2__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_KVSnap__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_KVSnap__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_2] {
  any 4 actions
  assert (¬ serialization)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_KVSnap__d4__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_KVSnap__d4__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_KVSnap__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_KVSnap__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_3] {
  any 8 actions
  assert (¬ serialization)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_KVSnap__d8__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_KVSnap__d8__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_KVSnap__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_KVSnap__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_4] {
  any 16 actions
  assert (¬ serialization)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_KVSnap__d16__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_KVSnap__d16__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_KVSnap__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_KVSnap__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_5] {
  any 32 actions
  assert (¬ serialization)
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/TLA_KVSnap__d32__local__default.jsonl" "/tmp/veil-action-cache/results/queries/TLA_KVSnap__d32__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/TLA_KVSnap__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

end KVsnapNew
