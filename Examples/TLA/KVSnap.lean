import Veil

open Std

veil module KVSnap
-- src : https://github.com/tlaplus/Examples/blob/master/specifications/KeyValueStore/KVsnap.tla
-- --------------------------- MODULE KVsnap ---------------------------------
-- (**************************************************************************)
-- (* Pluscal algorithm for a simple key-value store with snapshot isolation  *)
-- (* This version has atomic updates of store and missed sets of txns       *)
-- (**************************************************************************)
-- EXTENDS Integers, Sequences, FiniteSets, Util

-- CONSTANTS   Key,            \* The set of all keys.
--             TxId,           \* The set of all transaction IDs.
--             NoVal           \* NoVal, which all keys are initialized with.
-- type key
enum key = { K1, K2 }
type Keys
enum txId = { noVal, T1, T2, T3}
type TxIds
enum states = { START, READ, UPDATE, COMMIT, Done }
instantiate keySet : TSet key Keys
instantiate txIdSet : TSet txId TxIds

@[veil_decl]
inductive OpType where
  | Read
  | Write
deriving instance Veil.Enumeration, Lean.ToJson for OpType

@[veil_decl]
structure Op (α β : Type) where
  op : OpType
  key : α
  value : β
deriving instance Veil.Enumeration, Lean.ToJson for Op

type Ops
instantiate opsSet : TSet (Op key txId) Ops
-- \* Instantiating ClientCentric enables us to check transaction isolation guarantees this model satisfies
-- \* https://muratbuffalo.blogspot.com/2022/07/automated-validation-of-state-based.html
-- CC == INSTANCE ClientCentric WITH Keys <- Key, Values <- TxId \union {NoVal}
-- \* BEGIN TRANSLATION (chksum(pcal) = "1adfcb46" /\ chksum(tla) = "5b28617f")
-- VARIABLES store, tx, missed, pc, snapshotStore, read_keys, write_keys, ops
-- vars == << store, tx, missed, pc, snapshotStore, read_keys, write_keys, ops>>
function store : key → txId
relation tx : txId → Bool
function missed : txId → Keys
function snapshotStore : txId → key → txId
function read_keys : txId → Keys
function write_keys : txId → Keys
relation pc : txId → states → Bool
function ops : txId → List (Op key txId)


/- __GHOST VAIRBLES__ -/
-- State == [Keys -> Values]
-- Note: In TLA+, State is a function from Keys to Values
-- We represent this as (key → txId) in Veil
-- abbrev KVState (key txId : Type) [BEq key] [Hashable key] := HashMap key txId
type KVState
instantiate totalMap : TMap key txId KVState

-- ExecutionElem == [parentState: State, transaction: Transaction]

@[veil_decl]
structure ExecutionElem (k t σ: Type) where
  parentState : σ  -- State is a function
  transaction : List (Op k t)

-- Execution == Seq(ExecutionElem) -- List (ExecutionElem k t σ)
-- Accumulator for execution computation
@[veil_decl]
structure ExecutionAcc (k t σ : Type) where
  execution : List (ExecutionElem k t σ)
  nextState : σ -- State is a function

-- type transactions
-- type executionsTy
-- instantiate transactionSet : TSet (List (Op key txId)) transactions
-- instantiate executionSet : TSet (List (ExecutionElem key txId KVState)) executionsTy
immutable individual initialState : KVState
individual transaction : List (Op key txId)
individual TransactionsPool : List (List (Op key txId))
individual ExecutionsPool : List (List (ExecutionElem key txId KVState))
immutable individual txIdUniv : TxIds



#gen_state

procedure SetToSeq (L : Ops) { return opsSet.toList L }

procedure effects (curState : KVState) (transaction : List (Op key txId)) {
  let newState := transaction.foldl (fun acc o =>
    match o.op with
    | OpType.Write => totalMap.insert o.key o.value acc
    | OpType.Read => acc
  ) curState
  return newState
}

procedure executions (initState : KVState) (trans : List (List (Op key txId))) {
  let orderings := trans.permutations
  let initAcc : ExecutionAcc key txId KVState := { execution := [], nextState := initState }
  let allExecutions := orderings.map fun ordering =>
    let executionAcc := ordering.foldl (fun acc t =>
      let newState := t.foldl (fun st o =>
        if o.op == OpType.Write then
          totalMap.insert o.key o.value st
        else
          st
      ) acc.nextState

      { execution := acc.execution ++ [{ parentState := acc.nextState, transaction := t }],
        nextState := newState }
    ) initAcc
    executionAcc.execution

  return allExecutions
}



procedure updatePools {
  let allTxIds := txIdSet.toList txIdUniv
  let allTransactions := allTxIds.map (fun t => ops t)
  let nonEmptyTransactions := allTransactions.filter (fun t => t.length > 0)
  TransactionsPool := nonEmptyTransactions.eraseDups
  let allExecs ← executions initialState TransactionsPool
  ExecutionsPool := allExecs.eraseDups
}


-- Init == (* Global variables *)txId
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
  store K := noVal
  tx T := false
  missed T := keySet.empty
  snapshotStore T K := noVal
  read_keys T := keySet.empty
  write_keys T := keySet.empty
  ops T := []
  updatePools
  pc T S := S == START
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
action _START (self : txId) {
  require self ≠ noVal
  require pc self START
  -- require ¬ tx self
  tx self := true
  snapshotStore self K := store K
  let rk :| keySet.count rk > 0
  let wk :| keySet.count wk > 0
  read_keys self := rk
  write_keys self := wk
  pc self S := S == READ
}

-- READ(self) == /\ pc[self] = "READ"
--               /\ ops' = [ops EXCEPT ![self] = ops[self] \o SetToSeq({rOp(k, snapshotStore[self][k]): k \in read_keys[self]})]
--               /\ pc' = [pc EXCEPT ![self] = "UPDATE"]
--               /\ UNCHANGED << store, tx, missed, snapshotStore, read_keys,
--                               write_keys >>
action _READ (self : txId) {
  require self ≠ noVal
  require pc self READ
  let readOps : Ops := keySet.map (read_keys self) (fun k =>
    { op := OpType.Read,
      key := k,
      value := snapshotStore self k : Op key txId })
  let readOpsSeq ← SetToSeq readOps
  ops self := ops self ++ readOpsSeq
  updatePools

  pc self S := S == UPDATE
}

-- UPDATE(self) == /\ pc[self] = "UPDATE"
--                 /\ snapshotStore' = [snapshotStore EXCEPT ![self] = [k \in Key |-> IF k \in write_keys[self] THEN self ELSE snapshotStore[self][k] ]]
--                 /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
--                 /\ UNCHANGED << store, tx, missed, read_keys, write_keys, ops >>
action _UPDATE (self : txId) {
  require self ≠ noVal
  require pc self UPDATE
  snapshotStore self K := if keySet.contains K (write_keys self) then self else snapshotStore self K
  pc self S := S == COMMIT
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
action _COMMIT (self : txId) {
  require self ≠ noVal
  require pc self COMMIT
  if keySet.intersection (missed self) (write_keys self) == keySet.empty then
    tx self := false
    missed O := if tx O then keySet.union (missed O) (write_keys self) else missed O
    store K := if keySet.contains K (write_keys self) then (snapshotStore self K) else store K
    let writeOps : Ops := keySet.map (write_keys self) (fun k =>
      { op := OpType.Write,
        key := k,
        value := self : Op key txId })
    let writeOpsSeq ← SetToSeq writeOps
    ops self := ops self ++ writeOpsSeq

    updatePools

  pc self S := S == Done
}



ghost relation isComplete (execution : List (ExecutionElem key txId KVState)) (transaction : List (Op key txId)) (state : KVState) :=
  let Se := execution.map (fun e => e.parentState)
  let spIdx := (execution.findIdx? (fun e => e.transaction == transaction)) |>.getD 0
  let statesUpToSp := Se.take (spIdx + 1)
  -- Helper: compute read states for a single operation (pure function)
  let computeReadStates (operation : Op key txId) : List KVState :=
    statesUpToSp.filter (fun s =>
      let stateMatchesOp := (totalMap.lookup operation.key s |>.getD noVal) == operation.value
      let writeIdx := transaction.findIdx? (fun w =>
        w.op == OpType.Write && w.key == operation.key && w.value == operation.value
      )
      let opIdx := transaction.findIdx? (fun w => w == operation)
      let existsEarlierWrite := writeIdx.isSome && (opIdx.getD 0) > (writeIdx.getD 0)
      let isWriteOp := operation.op == OpType.Write
      stateMatchesOp || existsEarlierWrite || isWriteOp
    )
  -- All read states for each operation
  let allReadStates := transaction.map computeReadStates
  -- Read states for empty transaction
  let emptyReadStates := statesUpToSp
  -- Check if state is in intersection
  if transaction.isEmpty then
    emptyReadStates.contains state = true
  else
    let isInIntersection := allReadStates.all (fun readStateList => readStateList.contains state)
    let isInEmptyStates := emptyReadStates.contains state
    isInIntersection && isInEmptyStates = true


invariant [serializability]
  TransactionsPool.length > 0 →
    (∃ exec ∈ ExecutionsPool,
      ∀ trans ∈ TransactionsPool,
        let parentStateIdx := (exec.findIdx? (fun e => e.transaction == trans)) |>.getD 0
        let parentSt := if parentStateIdx < exec.length
                        then exec[parentStateIdx]!.parentState
                        else initialState
        isComplete exec trans parentSt)


termination [all_thread_done] (∀ t : txId, t ≠ noVal → pc t Done)

-- veil_set_option useNewExtraction true
#gen_spec



def m1 : Std.ExtTreeMap key_IndT txId_IndT compare :=
  ExtTreeMap.ofList [
    (.K1, .noVal),
    (.K2, .noVal),
  ] compare


/- In interactive mode, reconstruct this counterexample trace is
very slow, taking about ~4 minutes (241738ms).
time: 250844ms -/
set_option veil.violationIsError false in
#time #model_check
{
  key := key_IndT,
  Keys := Std.ExtTreeSet key_IndT compare,
  txId := txId_IndT,
  TxIds := Std.ExtTreeSet txId_IndT compare,
  states := states_IndT,
  Ops := ExtTreeSet (Op key_IndT txId_IndT),
  KVState := ExtTreeMap key_IndT txId_IndT
}
{
  initialState := Std.ExtTreeMap.ofList [
    (key_IndT.K1, txId_IndT.noVal),
    (key_IndT.K2, txId_IndT.noVal),
  ] compare
  -- initialState := m1
,
  txIdUniv := ExtTreeSet.ofList ([.T1, .T2, .T3] : List txId_IndT),
}
/-BUG:
If we pass parameter from context (e.g., m1), then compilation will be failed.
After resolve the first issue, compilation will be successful though,
it would not report any bug.
It seems that stop at the right position,
but it does not report the violation found.
-/
-- Done!
-- Diameter:	8
-- States Found:	1
-- Distinct States:	336169
-- Queue:	166296
-- Elapsed time:	10m 6.4s


/-
Parralle:
Done!
Diameter:	9
States Found:	666813
Distinct States:	333910
Queue:	1110
Elapsed time:	7.5s


Done!
Diameter:	8
States Found:	672654
Distinct States:	336169
Queue:	166296
Elapsed time:	8m 21.1s
-/
end KVSnap
