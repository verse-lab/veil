import Veil
import Batteries.Data.List.Perm
open Std

def myTreeSet : Std.ExtTreeSet Nat := Std.ExtTreeSet.ofList [1, 2, 3,3]
def allPerms : List (List Nat) := myTreeSet.toList.permutations
#eval allPerms

veil module KVSnap
-- --------------------------- MODULE KVsnap ---------------------------------
-- (**************************************************************************)
-- (* Pluscal algorithm for a simple key-value store with snapshot isolation  *)
-- (* This version has atomic updates of store and missed sets of txns       *)
-- (**************************************************************************)
-- EXTENDS Integers, Sequences, FiniteSets, Util

-- CONSTANTS   Key,            \* The set of all keys.
--             TxId,           \* The set of all transaction IDs.
--             NoVal           \* NoVal, which all keys are initialized with.
type key
type Keys
type txId
type TxIds
enum states = { START, READ, UPDATE, COMMIT, Done }
instantiate keySet : TSet key Keys
instantiate txIdSet : TSet txId TxIds

inductive OpType
  | Read
  | Write
deriving DecidableEq, Inhabited, Hashable, Repr, Lean.ToJson, Ord

instance : FinEnum OpType :=
  FinEnum.ofList
    [OpType.Read, OpType.Write]
    (by simp; intro x; cases x <;> simp )

instance : Std.TransOrd OpType where
  eq_swap := by intro a b; cases a <;> cases b <;> decide
  isLE_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide

instance : Std.LawfulEqOrd OpType where
  compare_self := by intro a; cases a <;> decide
  eq_of_compare := by intro a b; cases a <;> cases b <;> decide

section VariousByEquiv
variable {α : Type u} {β : Type v} [Ord α] [Ord β] (equiv : α ≃ β)
  (hmorph : ∀ (a1 a2 : α), compare a1 a2 = compare (equiv a1) (equiv a2))
include hmorph
def Std.TransOrd.by_equiv [inst : Std.TransOrd α] : Std.TransOrd β where
  eq_swap := by
    intro b1 b2
    rw [← equiv.right_inv b1, ← equiv.right_inv b2] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    apply inst.eq_swap
  isLE_trans := by
    intro b1 b2 b3
    rw [← equiv.right_inv b1, ← equiv.right_inv b2, ← equiv.right_inv b3] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    apply inst.isLE_trans
def Std.LawfulEqOrd.by_equiv [inst : Std.LawfulEqOrd α] : Std.LawfulEqOrd β where
  compare_self := by
    intro b ; specialize hmorph (equiv.symm b) (equiv.symm b) ; grind
  eq_of_compare := by
    intro b1 b2
    rw [← equiv.right_inv b1, ← equiv.right_inv b2] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    simp
end VariousByEquiv

structure Op (key value : Type) where
  op : OpType
  key : key
  value : value
deriving DecidableEq, Inhabited, Hashable, Repr, Lean.ToJson, Ord


namespace OpDef

def OpEquiv : Op α β ≃ (OpType × α × β) where
  toFun v := (v.op, v.key, v.value)
  invFun := fun (a, b, c) => { op := a, key := b, value := c }
  left_inv := by intro v; cases v; rfl
  right_inv := by intro p; rfl


theorem Op_compare_hmorph
  [Ord α] [Ord β]
  (v1 v2 : Op α β) :
  compare v1 v2 = compare (OpEquiv v1) (OpEquiv v2) := by
  simp [Ord.compare, OpEquiv, instOrdOp.ord]


instance instTransOrdForOp
[Ord α] [Ord β]
[Std.TransOrd α]
[Std.TransOrd β]
: Std.TransOrd (Op α β) :=
  @Std.TransOrd.by_equiv (OpType × α × β) (Op α β) _ _ OpEquiv.symm
    (fun a1 a2 => (Op_compare_hmorph (OpEquiv.symm a1) (OpEquiv.symm a2)).symm)
    inferInstance


instance instLawfulEqOrdForOp
[Ord α] [Ord β]
[Std.LawfulEqOrd α]
[Std.LawfulEqOrd β]
: Std.LawfulEqOrd (Op α β) :=
  @Std.LawfulEqOrd.by_equiv (OpType × α × β) (Op α β) _ _ OpEquiv.symm
    (fun a1 a2 => (Op_compare_hmorph (OpEquiv.symm a1) (OpEquiv.symm a2)).symm)
    inferInstance
end OpDef


instance instFinEnumForOp
  {key value : Type}
  [FinEnum key]
  [FinEnum value]
  : FinEnum (Op key value) :=
  FinEnum.ofEquiv _
  { toFun := fun m => (m.op, m.key, m.value)
    invFun := fun (t, k, v) => { op := t, key := k, value := v }
    left_inv := by intro m; cases m; simp
    right_inv := by intro x; simp }



instance [FinEnum α] : Veil.Enumeration α where
  -- allValues := FinEnum.toList α
  allValues := FinEnum.toList α
  complete := FinEnum.mem_toList



type Ops
instantiate opsSet : TSet (Op key txId) Ops
-- \* Instantiating ClientCentric enables us to check transaction isolation guarantees this model satisfies
-- \* https://muratbuffalo.blogspot.com/2022/07/automated-validation-of-state-based.html
-- CC == INSTANCE ClientCentric WITH Keys <- Key, Values <- TxId \union {NoVal}

-- \* Helpers representing Reads and Writes
-- r(k,v) == [op |-> "read",  key |-> k, value |-> v]
-- w(k,v) == [op |-> "write", key |-> k, value |-> v]
-- \* for instantiating the ClientCentric module
-- wOp(k,v) == CC!w(k,v)
-- rOp(k,v) == CC!r(k,v)
-- InitialState == [k \in Key |-> NoVal]
-- SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

-- \* BEGIN TRANSLATION (chksum(pcal) = "1adfcb46" /\ chksum(tla) = "5b28617f")
-- VARIABLES store, tx, missed, pc, snapshotStore, read_keys, write_keys, ops

-- vars == << store, tx, missed, pc, snapshotStore, read_keys, write_keys, ops>>

-- ProcSet == (TxId)
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
structure ExecutionElem (k t σ: Type) where
  parentState : σ  -- State is a function
  transaction : List (Op k t)
deriving Inhabited, DecidableEq, Repr, Lean.ToJson, Ord, Hashable
-- Execution == Seq(ExecutionElem) -- List (ExecutionElem k t σ)


namespace ExecutionElemDef
def ExecutionElemEquiv : ExecutionElem α β σ ≃ (σ × List (Op α β)) where
  toFun v := (v.parentState, v.transaction)
  invFun := fun (a, b) => { parentState := a, transaction := b }
  left_inv := by intro v; cases v; rfl
  right_inv := by intro p; rfl

theorem ExecutionElem_compare_hmorph
  [Ord α] [Ord β] [Ord σ]
  (v1 v2 : ExecutionElem α β σ) :
  compare v1 v2 = compare (ExecutionElemEquiv v1) (ExecutionElemEquiv v2) := by
  simp [Ord.compare, ExecutionElemEquiv, instOrdExecutionElem.ord]


instance instTransOrdForExecutionElem
[Ord α] [Ord β] [Ord σ]
[Std.TransOrd α]
[Std.TransOrd β]
[Std.TransOrd σ]
: Std.TransOrd (ExecutionElem α β σ) :=
  @Std.TransOrd.by_equiv (σ × List (Op α β)) (ExecutionElem α β σ) _ _ ExecutionElemEquiv.symm
    (fun a1 a2 => (ExecutionElem_compare_hmorph (ExecutionElemEquiv.symm a1) (ExecutionElemEquiv.symm a2)).symm)
    inferInstance


instance instLawfulEqOrdForExecutionElem
[Ord α] [Ord β] [Ord σ]
[Std.LawfulEqOrd α]
[Std.LawfulEqOrd β]
[Std.LawfulEqOrd σ]
: Std.LawfulEqOrd (ExecutionElem α β σ) :=
  @Std.LawfulEqOrd.by_equiv (σ × List (Op α β)) (ExecutionElem α β σ) _ _ ExecutionElemEquiv.symm
    (fun a1 a2 => (ExecutionElem_compare_hmorph (ExecutionElemEquiv.symm a1) (ExecutionElemEquiv.symm a2)).symm)
    inferInstance
end ExecutionElemDef

-- Accumulator for execution computation
structure ExecutionAcc (k t σ : Type) where
  execution : List (ExecutionElem k t σ)
  nextState : σ -- State is a function
deriving Inhabited, DecidableEq, Repr, Lean.ToJson, Ord, Hashable


namespace ExecutionAccDef

def ExecutionAccEquiv : ExecutionAcc α β σ ≃ (List (ExecutionElem α β σ) × σ) where
  toFun v := (v.execution, v.nextState)
  invFun := fun (a, b) => { execution := a, nextState := b }
  left_inv := by intro v; cases v; rfl
  right_inv := by intro p; rfl

theorem ExecutionAcc_compare_hmorph
  [Ord α] [Ord β] [Ord σ]
  (v1 v2 : ExecutionAcc α β σ) :
  compare v1 v2 = compare (ExecutionAccEquiv v1) (ExecutionAccEquiv v2) := by
  simp [Ord.compare, ExecutionAccEquiv, instOrdExecutionAcc.ord]

instance instTransOrdForExecutionAcc
[Ord α] [Ord β] [Ord σ]
[Std.TransOrd α]
[Std.TransOrd β]
[Std.TransOrd σ]
: Std.TransOrd (ExecutionAcc α β σ) :=
  @Std.TransOrd.by_equiv (List (ExecutionElem α β σ) × σ) (ExecutionAcc α β σ) _ _ ExecutionAccEquiv.symm
    (fun a1 a2 => (ExecutionAcc_compare_hmorph (ExecutionAccEquiv.symm a1) (ExecutionAccEquiv.symm a2)).symm)
    inferInstance

instance instLawfulEqOrdForExecutionAcc
[Ord α] [Ord β] [Ord σ]
[Std.LawfulEqOrd α]
[Std.LawfulEqOrd β]
[Std.LawfulEqOrd σ]
: Std.LawfulEqOrd (ExecutionAcc α β σ) :=
  @Std.LawfulEqOrd.by_equiv (List (ExecutionElem α β σ) × σ) (ExecutionAcc α β σ) _ _ ExecutionAccEquiv.symm
    (fun a1 a2 => (ExecutionAcc_compare_hmorph (ExecutionAccEquiv.symm a1) (ExecutionAccEquiv.symm a2)).symm)
    inferInstance
end ExecutionAccDef



-- type transactions
-- type executionsTy
-- instantiate transactionSet : TSet (List (Op key txId)) transactions
-- instantiate executionSet : TSet (List (ExecutionElem key txId KVState)) executionsTy
immutable individual initialState : KVState
individual transaction : List (Op key txId)
immutable individual noVal : txId

-- Individual representing Range(ops): the set of all transaction operation lists
-- individual TransactionsPool : transactions
individual TransactionsPool : List (List (Op key txId))
-- Individual representing executions(initialState, allTransactions): all possible executions
individual ExecutionsPool : List (List (ExecutionElem key txId KVState))
--
immutable individual txIdUniv : TxIds

-- #exit

#gen_state
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
procedure SetToSeq (L : Ops) {
  -- choose f : (Nat → Op key txId) where
  --   IsInjective f ∧
  --   ∀ i : Nat, i ≥ 1 ∧ i ≤ pset.count L → pset.contains (f i) L
  -- return f
  return opsSet.toList L
}



-- effects(state, transaction) ==
--        ReduceSeq(LAMBDA o, newState: IF o.op = "write" THEN [newState EXCEPT![o.key] = o.value] ELSE newState, transaction, state)
procedure effects (curState : KVState) (transaction : List (Op key txId)) {
  let newState := transaction.foldl (fun acc o =>
    if o.op == OpType.Write then
      -- [newState EXCEPT![o.key] = o.value]
      totalMap.insert o.key o.value acc
    else
      acc
    ) curState
  return newState
}

-- transactions ~ Set (List (Op key txId))
-- executions(initialState, transactions) ==
--   LET orderings == PermSeqs(transactions)
--       accummulator == [ execution |-> <<>>, nextState |-> initialState ]
--   IN { LET executionAcc == ReduceSeq(
--                             LAMBDA t, acc: [ execution |-> Append(acc.execution, [parentState |-> acc.nextState, transaction |-> t])
--                                            , nextState |-> effects(acc.nextState,t)
--                             ],
--                             ordering, accummulator)
--        IN executionAcc.execution
--      : ordering \in orderings }
procedure executions (initState : KVState) (trans : List (List (Op key txId))) {
  -- Generate all permutations of transactions (orderings == PermSeqs(transactions))
  -- trans is already a List, no need to convert
  let orderings := trans.permutations
  -- accumulator == [ execution |-> <<>>, nextState |-> initialState ]
  let initAcc : ExecutionAcc key txId KVState := { execution := [], nextState := initState }
  -- IN { LET executionAcc == ReduceSeq(..., ordering, accumulator) IN executionAcc.execution : ordering \in orderings }
  let allExecutions := orderings.map fun ordering =>
    -- ReduceSeq with LAMBDA t, acc: [ execution |-> Append(...), nextState |-> effects(...) ]
    let executionAcc := ordering.foldl (fun acc t =>
      -- Compute nextState := effects(acc.nextState, t)
      -- Inline effects: apply all write operations to the state
      let newState := t.foldl (fun st o =>
        if o.op == OpType.Write then
          totalMap.insert o.key o.value st
        else
          st
      ) acc.nextState
      -- Build new accumulator: [ execution |-> Append(acc.execution, [parentState |-> acc.nextState, transaction |-> t]), nextState |-> newState ]
      { execution := acc.execution ++ [{ parentState := acc.nextState, transaction := t }],
        nextState := newState }
    ) initAcc
    executionAcc.execution

  return allExecutions
}


-- executionStates(execution) == [ i \in 1..Len(execution) |-> execution[i].parentState ]
procedure executionStates (execution : List (ExecutionElem key txId KVState)) {
  return execution.map (fun e => e.parentState)
}



-- parentState(execution, transaction) ==
--   LET ind == CHOOSE i \in 1..Len(execution): execution[i].transaction = transaction
--   IN execution[ind].parentState

-- CT_SER(transaction, execution) ==
--   Complete(execution, transaction, parentState(execution, transaction))
procedure parentState (execution : List (ExecutionElem key txId KVState)) (transaction : List (Op key txId)) {
  let ind := (execution.findIdx? (fun e => e.transaction == transaction)) |>.getD 0
  return ind
}



-- readStatesForEmptyTransaction(execution, transaction) ==
--   { s \in SeqToSet(executionStates(execution)) : beforeOrEqualInExecution(execution, s, parentState(execution, transaction)) }
-- beforeOrEqualInExecution(execution, state1, state2) ==
--   LET states == executionStates(execution)
--   IN  Index(states, state1) <= Index(states, state2)
ghost relation beforeOrEqualInExecution (execution : List (ExecutionElem key txId KVState)) (state1 state2 : KVState) :=
  let states := execution.map (fun e => e.parentState)
  let idx1 := states.findIdx? (fun s => s == state1) |>.getD 0
  let idx2 := states.findIdx? (fun s => s == state2) |>.getD 0
  idx1 ≤ idx2

procedure readStatesForEmptyTransaction
  (execution : List (ExecutionElem key txId KVState))
  (transaction : List (Op key txId)) {
  -- Get all execution states: SeqToSet(executionStates(execution))
  let allStates ← executionStates execution
  let spIdx ← parentState execution transaction
  -- { s \in allStates : beforeOrEqualInExecution(execution, s, parentState(execution, transaction)) }
  -- This means all states from index 0 to spIdx (inclusive)
  let validStates := allStates.take (spIdx + 1)
  return validStates
}


-- ReadStates(execution, operation, transaction) ==
--   LET Se == SeqToSet(executionStates(execution))
--       sp == parentState(execution, transaction)
--   IN { s \in Se:
--         /\ beforeOrEqualInExecution(execution, s, sp) \* s -*-> s_p: restrict the valid read states for the operations in T to be no later than sp
--         /\ \/ s[operation.key] = operation.value \* (k,v) \in s
--            \/ \E write \in SeqToSet(transaction):
--               /\ write.op = "write" /\ write.key = operation.key /\ write.value = operation.value
--               /\ earlierInTransaction(transaction, write, operation) \* w(k,v)-to->r(k,v)
--            \/ operation.op = "write"
--      }
procedure ReadStates
  (execution : List (ExecutionElem key txId KVState))
  (operation : Op key txId)
  (transaction : List (Op key txId)) {
  -- LET Se == SeqToSet(executionStates(execution))
  let Se ← executionStates execution
  -- sp == parentState(execution, transaction)
  let spIdx ← parentState execution transaction
  -- Filter states that satisfy all conditions:
  -- { s \in Se : beforeOrEqualInExecution(execution, s, sp) ∧ (...) }
  -- We need to filter states by index, so we take only states up to spIdx first
  let statesUpToSp := Se.take (spIdx + 1)

  -- Then filter by the other conditions
  let validStates := statesUpToSp.filter (fun s =>
    -- s[operation.key] = operation.value
    let stateMatchesOp := (totalMap.lookup operation.key s |>.getD noVal) == operation.value

    -- \E write \in SeqToSet(transaction):
    --   /\ write.op = "write" /\ write.key = operation.key /\ write.value = operation.value
    --   /\ earlierInTransaction(transaction, write, operation)
    let writeIdx := transaction.findIdx? (fun w =>
      w.op == OpType.Write && w.key == operation.key && w.value == operation.value
    )
    let opIdx := transaction.findIdx? (fun w => w == operation)
    let existsEarlierWrite := writeIdx.isSome && (opIdx.getD 0) > (writeIdx.getD 0)

    -- operation.op = "write"
    let isWriteOp := operation.op == OpType.Write

    -- Combine conditions: stateMatchesOp ∨ existsEarlierWrite ∨ isWriteOp
    stateMatchesOp || existsEarlierWrite || isWriteOp
  )
  return validStates
}

-- Complete(execution, transaction, state) ==
--   LET setOfAllReadStatesOfOperation(transactionOperations) ==
--         { ReadStates(execution, operation, transaction) : operation \in SeqToSet(transactionOperations) }
--       readStatesForEmptyTransaction == { s \in SeqToSet(executionStates(execution)) : beforeOrEqualInExecution(execution, s, parentState(execution, transaction)) }
--   IN state \in INTERSECTION(setOfAllReadStatesOfOperation(transaction) \union { readStatesForEmptyTransaction } )

-- setOfAllReadStatesOfOperation(transactionOperations) ==
--   { ReadStates(execution, operation, transaction) : operation \in SeqToSet(transactionOperations) }
procedure setOfAllReadStatesOfOperation
  (execution : List (ExecutionElem key txId KVState))
  (transaction : List (Op key txId)) {
  -- For each operation in the transaction, compute ReadStates(execution, operation, transaction)
  -- { ReadStates(execution, operation, transaction) : operation \in SeqToSet(transactionOperations) }

  -- Get execution states and parent state index once (to avoid repeated computation)
  let Se ← executionStates execution
  let spIdx ← parentState execution transaction
  let statesUpToSp := Se.take (spIdx + 1)

  -- Pure function: compute ReadStates for a single operation
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

  -- Map each operation to its ReadStates result using pure function
  let result := transaction.map computeReadStates

  return result
}



procedure Complete
  (execution : List (ExecutionElem key txId KVState))
  (transaction : List (Op key txId))
  (state : KVState) {
  -- Get all read states for each operation
  let allReadStates ← setOfAllReadStatesOfOperation execution transaction
  -- Get read states for empty transaction
  let emptyReadStates ← readStatesForEmptyTransaction execution transaction
  -- If transaction is empty, use emptyReadStates
  -- Otherwise, compute intersection of all read state sets
  if transaction.isEmpty then
    let isInEmptyStates := emptyReadStates.contains state
    return isInEmptyStates
  else
    -- Compute intersection: state must be in all read state sets
    let isInIntersection := allReadStates.all (fun readStateList =>
      readStateList.contains state
    )
    -- Also must be in empty read states
    let isInEmptyStates := emptyReadStates.contains state
    let result := isInIntersection && isInEmptyStates
    return result
}





-- Helper procedure to update TransactionsPool and ExecutionsPool based on current ops
-- Range(ops) = { ops[t] : t ∈ TxId, ops[t] ≠ <<>> }
procedure updatePools {
  -- Get universe of all valid txIds (excluding noVal)
  -- let txIdUniv :| ∀ t : txId, txIdSet.contains t txIdUniv ∧ t ≠ noVal
  -- Convert txIdUniv to a list for iteration
  let allTxIds := txIdSet.toList txIdUniv
  -- Build TransactionsPool using List instead of TSet
  -- Range(ops) = { ops[t] : t ∈ TxId, ops[t] ≠ <<>> }
  -- Only include non-empty transactions
  let allTransactions := allTxIds.map (fun t => ops t)
  let nonEmptyTransactions := allTransactions.filter (fun t => t.length > 0)
  -- Remove duplicates by converting to a deduplicated list
  TransactionsPool := nonEmptyTransactions.eraseDups


  -- Compute executions(initialState, TransactionsPool)
  let allExecs ← executions initialState TransactionsPool
  -- ExecutionsPool is already a List, just assign it
  ExecutionsPool := allExecs.eraseDups

}



-- satisfyIsolationLevel(initialState, transactions, commitTest(_,_)) ==
--   \E execution \in executions(initialState, transactions): \A transaction \in transactions:
--     \* PrintT(<<"try execution:",execution>>) =>
--     commitTest(transaction, execution)

-- executions ->  List (List (ExecutionElem key txId KVState))
-- transactions -> transactionSet : TSet (List (Op key txId)) transactions
-- parameters : transactions ← Range(ops)

-- \* Serializability commit test
-- CT_SER(transaction, execution) ==
--   Complete(execution, transaction, parentState(execution, transaction))

after_init {
  store K := noVal
  tx T := false
  missed T := keySet.empty
  -- process t
  snapshotStore T K := noVal
  read_keys T := keySet.empty
  write_keys T := keySet.empty
  ops T := []
  updatePools
  pc T S := S == START
  /- ghost variables -/
  -- initialState := totalMap.empty
}

#print initializer.do
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
  require ¬ tx self
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
  /- Currently, we have two ways to have an univ:
  1. utitize non-determisitic operation.
  2. define an immutable individual for the `univ`, then -/
  let readKeysUniv :| ∀k, keySet.contains k (read_keys self) → keySet.contains k readKeysUniv
  let readOps : Ops := keySet.map readKeysUniv (fun k =>
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
  /- LLM is really good at finding errors. Initially I omit `∃` by mistake.
  All I find a trivial invariant `¬ (∀t, pc t Done)` is satisfied.-/
  -- if ¬(∃k, keySet.contains k (missed self) ∧ keySet.contains k (write_keys self)) then
  if keySet.intersection (missed self) (write_keys self) == keySet.empty then
    tx self := false
    missed O := if tx O then keySet.union (missed O) (write_keys self) else missed O
    store K := if keySet.contains K (write_keys self) then (snapshotStore self K) else store K
    let writeKeysUniv :| ∀k, keySet.contains k (write_keys self) → keySet.contains k writeKeysUniv
    let writeOps : Ops := keySet.map writeKeysUniv (fun k =>
      { op := OpType.Write,
        key := k,
        value := self : Op key txId })
    let writeOpsSeq ← SetToSeq writeOps
    ops self := ops self ++ writeOpsSeq
    updatePools
  pc self S := S == Done
}


-- invariant [pc_valid] ∀ self : txId, pc self START
termination [tx_done] (∀ self : txId, pc self Done)
-- t(self) == START(self) \/ READ(self) \/ UPDATE(self) \/ COMMIT(self)

-- (* Allow infinite stuttering to prevent deadlock on termination. *)
-- Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
--                /\ UNCHANGED vars

-- Next == (\E self \in TxId: t(self))
--            \/ Terminating

-- Spec == /\ Init /\ [][Next]_vars
--         /\ \A self \in TxId : WF_vars(t(self))

-- Termination == <>(\A self \in ProcSet: pc[self] = "Done")

-- \* END TRANSLATION

-- invariant [lenlog_less_three]∀t, (ops t).length ≤ 1

-- \* Snapshot isolation invariant



-- TypeOK == \* type invariant
--     /\ store \in [Key -> TxId \union {NoVal}]
--     /\ tx \subseteq TxId
--     /\ missed \in [TxId -> SUBSET Key]


-- \* Serializability would not be satisfied due to write-skew
-- Serialization == CC!Serializability(InitialState, Range(ops))

-- WriteSet(transaction) ==
--   LET writes == { operation \in SeqToSet(transaction) : operation.op = "write" }
--   IN { operation.key : operation \in writes }
procedure WriteSet (transaction : List (Op key txId)) {
  let writes := transaction.filter (fun op => op.op == OpType.Write)
  let writeKeys := writes.map (fun op => op.key)
  return writeKeys
}

-- NoConf(execution, transaction, state) ==
--   LET Sp == parentState(execution, transaction)
--       delta == { key \in DOMAIN Sp : Sp[key] /= state[key] }
--   IN delta \intersect WriteSet(transaction) = {}
--
-- NoConf checks that the keys that changed between Sp and state
-- do NOT intersect with the WriteSet of the transaction.
-- This prevents write-write conflicts.
ghost relation noConf (execution : List (ExecutionElem key txId KVState)) (transaction : List (Op key txId)) (state : KVState) :=
  let spIdx := (execution.findIdx? (fun e => e.transaction == transaction)).getD 0
  let Sp := if spIdx < execution.length then execution[spIdx]!.parentState else state
  -- WriteSet: keys written by this transaction
  let writes := transaction.filter (fun op => op.op == OpType.Write)
  let writeKeys := writes.map (fun op => op.key)
  -- Check: for each write key, the value in Sp and state must be the same
  -- (i.e., no other transaction modified these keys between Sp and state)
  let result := writeKeys.all (fun k =>
    let spVal := (totalMap.lookup k Sp).getD noVal
    let stVal := (totalMap.lookup k state).getD noVal
    spVal == stVal
  )
  result = true

-- Complete(execution, transaction, state) ==
--   LET setOfAllReadStatesOfOperation(transactionOperations) ==
--         { ReadStates(execution, operation, transaction) : operation \in SeqToSet(transactionOperations) }
--       readStatesForEmptyTransaction == { s \in SeqToSet(executionStates(execution)) : beforeOrEqualInExecution(execution, s, parentState(execution, transaction)) }
--   IN state \in INTERSECTION(setOfAllReadStatesOfOperation(transaction) \union { readStatesForEmptyTransaction } )
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

-- SnapshotIsolation == CC!SnapshotIsolation(InitialState, Range(ops))
-- CT_SI(transaction, execution) ==
--   \E state \in SeqToSet(executionStates(execution)):
--     Complete(execution, transaction, state) /\ NoConf(execution, transaction, state)
-- satisfyIsolationLevel(initialState, transactions, CT_SI(_,_)) ==
--   \E execution \in executions(initialState, transactions): \A transaction \in transactions:
--     CT_SI(transaction, execution)
invariant [snapshot_isolation]
  -- Only check when there are actual transactions
  TransactionsPool.length > 0 →
    (∃ exec ∈ ExecutionsPool,
      ∀ trans ∈ TransactionsPool,
        let executionStates := exec.map (fun e => e.parentState)
        ∃ state ∈ executionStates,
          isComplete exec trans state ∧ noConf exec trans state)

-- Serializability (for comparison, should be violated)
-- CT_SER(transaction, execution) ==
--   Complete(execution, transaction, parentState(execution, transaction))
invariant [serializability]
  TransactionsPool.length > 0 →
    (∃ exec ∈ ExecutionsPool,
      ∀ trans ∈ TransactionsPool,
        let parentStateIdx := (exec.findIdx? (fun e => e.transaction == trans)) |>.getD 0
        let parentSt := if parentStateIdx < exec.length
                        then exec[parentStateIdx]!.parentState
                        else initialState
        isComplete exec trans parentSt)

-- Debug invariants to check if pools are populated
-- invariant [pools_populated]
--   -- If all transactions are done, there should be some non-empty transactions
--   (∀ t : txId, t ≠ noVal → pc t Done) →
--     TransactionsPool.length > 0

-- #exit

-- invariant [logs_len]
--   (∀ t : txId,
--   let tlen := (ops t).length
--   pc t Done → tlen < 4)

termination [all_thread_done] (∀ t : txId, t ≠ noVal → pc t Done)
#gen_spec
--  txID = fin4, key= fin2 : (166375) states

set_option synthInstance.maxSize 1000
-- #model_check {
--   key := Fin 2,
--   txId := Fin 3,
--   Keys := Std.ExtTreeSet (Fin 2),
--   TxIds := Std.ExtTreeSet (Fin 3),
--   Ops := Std.ExtTreeSet (Op (Fin 2) (Fin 3)),
--   transactions := Std.ExtTreeSet (List (Op (Fin 2) (Fin 3))),
--   KVState := ExtTreeMap (Fin 2) (Fin 3),
-- }
-- {
--   noVal := 0
-- }
#print Theory
open Veil.ModelChecker

-- set_option synthInstance.maxHeartbeats 10000
-- set_option synthInstance.maxSize 20000
-- #synth Ord (List (Op (Fin 2) (Fin 2)))
-- #synth TransOrd (List (Op (Fin 2) (Fin 2)))
-- #synth LawfulEqOrd (List (Op (Fin 2) (Fin 2)))
-- #synth TSet (List (Op (Fin 2) (Fin 2))) (ExtTreeSet (List (Op (Fin 2) (Fin 2))))
-- #synth TSet (Op (Fin 2) (Fin 2)) (ExtTreeSet (Op (Fin 2) (Fin 2)) compare)

-- instance : Veil.Enumeration (ExtTreeSet (List (Op (Fin 2) (Fin 2))) compare) := sorry
-- #synth Veil.Enumeration (ExtTreeMap (Fin 2) (Fin 2) compare)
-- -- #synth Veil.Enumeration (ExecutionElem (Fin 2) (Fin 2) (ExtTreeMap (Fin 2) (Fin 2) compare))
-- instance : Veil.Enumeration (ExtTreeSet (List (ExecutionElem (Fin 2) (Fin 2) (ExtTreeMap (Fin 2) (Fin 2) compare))) compare) := sorry
-- set_option trace.Meta.synthInstance true
-- #synth Ord (List (ExecutionElem (Fin 2) (Fin 2) (ExtTreeMap (Fin 2) (Fin 2) compare)))
-- #synth TransOrd (ExtTreeMap (Fin 2) (Fin 2) compare)
-- #synth TransOrd (ExecutionElem (Fin 2) (Fin 2) (ExtTreeMap (Fin 2) (Fin 2) compare))
-- #synth TransOrd (List (ExecutionElem (Fin 2) (Fin 2) (ExtTreeMap (Fin 2) (Fin 2) compare)))
-- #synth Ord (ExtTreeSet (List (ExecutionElem (Fin 2) (Fin 2) (ExtTreeMap (Fin 2) (Fin 2) compare))) compare)


def m1 : Std.ExtTreeMap (Fin 2) (Fin 4) compare :=
  ({} : Std.ExtTreeMap (Fin 2) (Fin 4) compare)
    |>.insert ⟨0, by decide⟩ (0 : Fin 4)
    |>.insert ⟨1, by decide⟩ (0 : Fin 4)
#eval m1
-- #print instEnumerationExtTreeSetListOpFinOfNatNatCompare
-- set_option trace.Meta.synthInstance true
-- set_option synthInstance.maxSize 100000
-- set_option synthInstance.maxHeartbeats 100000
#print Theory



#model_check
{ key := Fin 2,
  Keys := Std.ExtTreeSet (Fin 2)
  txId := Fin 4,
  TxIds := Std.ExtTreeSet (Fin 4),
  Ops := ExtTreeSet (Op (Fin 2) (Fin 4))
  KVState := ExtTreeMap (Fin 2) (Fin 4),
}
{ initialState := m1,
  noVal := 0,
  txIdUniv := ExtTreeSet.ofList ([1, 2, 3] : List (Fin 4)) }

#exit
def modelCheckerResult :=
  Concrete.findReachable
  (
    enumerableTransitionSystem
    (Fin 2)
    (ExtTreeSet (Fin 2))
    (Fin 4)
    (ExtTreeSet (Fin 4))
    states_IndT
    (ExtTreeSet (Op (Fin 2) (Fin 4)))
    (ExtTreeMap (Fin 2) (Fin 4))
    {
      initialState := m1,
      noVal := 0,
      txIdUniv := ExtTreeSet.ofList ([1, 2, 3] : List (Fin 4))
    }
  )
  {
  «invariants» := [
    { name := `serializability
      property := fun th st => serializability th st }
  ],
  «terminating» := {
    name := `all_thread_done
    property := fun th st => all_thread_done th st
  },
  earlyTerminationConditions := [
    EarlyTerminationCondition.foundViolatingState,
    -- EarlyTerminationCondition.reachedDepthBound 4,
    EarlyTerminationCondition.deadlockOccurred
  ]
}


#eval! modelCheckerResult


-- #print instEnumerationExtTreeSetListOpFinOfNatNatCompare
-- #print instEnumerationExtTreeSetListOpFinOfNatNatCompare

-- #eval! modelCheckerResult


end KVSnap
