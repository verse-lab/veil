module

public import Veil

/-
  Translation of the swscop TLA+ specification.
  Source: https://github.com/Azure/azure-cosmos-tla/blob/a8357c9c0a8d0ed710c68a64bc3a9ed0dc860a8a/scenario1/swscop.tla
  Copyright (c) Microsoft Corporation. All rights reserved.
  Upstream license: MIT; see Benchmarks/TLA/CosmosDB/LICENSE.
  The translation and quoted source definitions are adapted from that model.

  Models CosmosDB consistency levels (Eventual, Consistent Prefix,
  Session, Bounded Staleness, Strong) with a single cloud server
  and a single client performing write-read cycles.
  Correspondence with the source is restricted to client := Fin 1 and
  MaxNumOp < 10. These source assumptions are not enforced by this module.
-/

veil module SWSCOP

-- EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Bags
-- CONSTANT NumClients, MaxNumOp, Consistency, K

type client

-- Cloud == 0; Clients == 1..NumClients.
@[veil_decl]
inductive Node (client : Type) where
  | cloud
  | client (id : client)
deriving instance Veil.Enumeration, Veil.FinEncodable for Node

immutable individual oneClient : client

-- MaxNumOp, K
immutable individual MaxNumOp : Nat
immutable individual K : Nat

-- Read consistency levels (the client sends type = Consistency).
@[veil_decl]
inductive ConsistencyLevel where
  | Eventual
  | Consistent_Prefix
  | Session
  | Bounded_Staleness
  | Strong
deriving instance Veil.Enumeration for ConsistencyLevel

-- ASSUME Consistency \in {"Eventual", "Consistent_Prefix", "Session", "Bounded_Staleness", "Strong"}
immutable individual Consistency : ConsistencyLevel

-- Follow the records constructed by the actions: only writes carry request data,
-- and only requests carry an origin. The source's unused Messages set omits
-- Write and Session and gives read requests a dat field that they do not send.
@[veil_decl]
inductive Request where
  | write (dat : Nat)
  | read (consistency : ConsistencyLevel)

@[veil_decl]
inductive ResponseKind where
  | Ack
  | Reply

@[veil_decl]
inductive Msg (client : Type) where
  | request (req : Request) (ses : Nat) (orig : client)
  | response (kind : ResponseKind) (dat : Nat) (ses : Nat)

-- PC labels (D/DW/DE/DP/DS/DB/DG for cloud, CW/CWA/CR/CRA/Done for clients)
enum pc_label = { D, DW, DE, DP, DS, DB, DG, CW, CWA, CR, CRA, Done }

-- VARIABLES chan, pc, Database, msg, m, op, chistory, ses

-- chan = [n \in 0..NumClients |-> <<>>]   \* FIFO channels
function chan : Node client → fQueue (Msg client)

-- Database = [self \in {Cloud} |-> <<0>>]
individual database : List Nat

-- msg = [self \in {Cloud} |-> <<>>]       \* cloud's current message
individual cloudMsg : Option (Msg client)

-- m = [self \in Clients |-> <<>>]         \* client's current message
function clientMsg : client → Option (Msg client)

-- op = [self \in Clients |-> 0]
function op : client → Nat

-- chistory = [self \in Clients |-> <<0>>]
function chistory : client → List Nat

-- ses = [self \in Clients |-> 1]
function ses : client → Nat

-- pc = [self \in ProcSet |-> CASE self \in {Cloud} -> "D"
--                               [] self \in Clients -> "CW"]
function pc : Node client → pc_label

veil_set_field_representation relation Veil.ArrayAsFinset
veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

-- Init == (* Global variables *)
--         /\ chan = [n \in 0..NumClients |-> <<>>]
--         (* Process cosmosdb *)
--         /\ Database = [self \in {Cloud} |-> <<0>>]
--         /\ msg = [self \in {Cloud} |-> <<>>]
--         (* Process client *)
--         /\ m = [self \in Clients |-> <<>>]
--         /\ op = [self \in Clients |-> 0]
--         /\ chistory = [self \in Clients |-> <<0>>]
--         /\ ses = [self \in Clients |-> 1]
--         /\ pc = [self \in ProcSet |-> CASE self \in {Cloud} -> "D"
--                                         [] self \in Clients -> "CW"]
after_init {
  chan N := fQueue.empty
  database := [0]
  cloudMsg := none
  clientMsg C := none
  op C := 0
  chistory C := [0]
  ses C := 1
  pc N := match N with
    | .cloud => D
    | .client _ => CW
}

-- ==================== Cloud (cosmosdb) actions ====================

-- D(self) == /\ pc[self] = "D"
--            /\ Len(chan[self]) > 0
--            /\ msg' = [msg EXCEPT ![self] = Head(chan[self])]
--            /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
--            /\ IF msg'[self].type="Write"
--                  THEN /\ Database' = [Database EXCEPT ![self] = Append(Database[self],msg'[self].dat)]
--                       /\ pc' = [pc EXCEPT ![self] = "DW"]
--                  ELSE /\ IF msg'[self].type="Eventual"
--                             THEN /\ pc' = [pc EXCEPT ![self] = "DE"]
--                             ELSE /\ IF msg'[self].type="Consistent_Prefix"
--                                        THEN /\ pc' = [pc EXCEPT ![self] = "DP"]
--                                        ELSE /\ IF msg'[self].type="Session"
--                                                   THEN /\ pc' = [pc EXCEPT ![self] = "DS"]
--                                                   ELSE /\ IF msg'[self].type="Bounded_Staleness"
--                                                              THEN /\ pc' = [pc EXCEPT ![self] = "DB"]
--                                                              ELSE /\ IF msg'[self].type="Strong"
--                                                                         THEN /\ pc' = [pc EXCEPT ![self] = "DG"]
--                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "D"]
--                       /\ UNCHANGED Database
--            /\ UNCHANGED << m, op, chistory, ses >>
action _D {
  require pc .cloud = D
  require (chan .cloud).isEmpty = false
  let (headMsg, rest) := (chan .cloud).dequeueD
  cloudMsg := some headMsg
  chan .cloud := rest
  database := match headMsg with
  | .request (.write dat) _ _ => database ++ [dat]
  | _ => database
  pc .cloud := match headMsg with
  | .request (.write _) _ _ => DW
  | .request (.read consistency) _ _ =>
    match consistency with
    | .Eventual => DE
    | .Consistent_Prefix => DP
    | .Session => DS
    | .Bounded_Staleness => DB
    | .Strong => DG
  | .response _ _ _ => D
}

-- DW(self) == /\ pc[self] = "DW"
--             /\ chan' = [chan EXCEPT ![(msg[self].orig)] = Append(chan[(msg[self].orig)],
--                  ([type|-> "Ack", dat|->Database[self][Len(Database[self])], ses|->Len(Database[self])]))]
--             /\ pc' = [pc EXCEPT ![self] = "D"]
--             /\ UNCHANGED << Database, msg, m, op, chistory, ses >>
action _DW {
  require pc .cloud = DW
  let orig? := match cloudMsg with
    | some (.request _ _ orig) => some orig
    | _ => none
  require orig?.isSome
  let orig := orig?.get!
  let dbLen := database.length
  let lastVal := database.getLast!
  let ackMsg : Msg client := .response .Ack lastVal dbLen
  chan (.client orig) := (chan (.client orig)).enqueue ackMsg
  pc .cloud := D
}

-- DE(self) == /\ pc[self] = "DE"
--             /\ \E k \in 1..Len(Database[self]):
--                  chan' = [chan EXCEPT ![(msg[self].orig)] = Append(chan[(msg[self].orig)],
--                    ([type|-> "Reply", dat|->Database[self][k], ses|->k]))]
--             /\ pc' = [pc EXCEPT ![self] = "D"]
--             /\ UNCHANGED << Database, msg, m, op, chistory, ses >>
action _DE {
  require pc .cloud = DE
  let orig? := match cloudMsg with
    | some (.request _ _ orig) => some orig
    | _ => none
  require orig?.isSome
  let orig := orig?.get!
  let dbLen := database.length
  let ksub : (Fin dbLen.succ):| 1 ≤ ksub ∧ ksub ≤ dbLen
  -- TLA+ is 1-indexed; Lean List is 0-indexed.
  let replyMsg : Msg client := .response .Reply database[ksub.val - 1]! ksub.val
  chan (.client orig) := (chan (.client orig)).enqueue replyMsg
  pc .cloud := D
}

-- DP(self) == /\ pc[self] = "DP"
--             /\ \E k \in 1..Len(Database[self]):
--                  chan' = [chan EXCEPT ![(msg[self].orig)] = Append(chan[(msg[self].orig)],
--                    ([type|-> "Reply", dat|->Database[self][k], ses|->k]))]
--             /\ pc' = [pc EXCEPT ![self] = "D"]
--             /\ UNCHANGED << Database, msg, m, op, chistory, ses >>
action _DP {
  require pc .cloud = DP
  let orig? := match cloudMsg with
    | some (.request _ _ orig) => some orig
    | _ => none
  require orig?.isSome
  let orig := orig?.get!
  let dbLen := database.length
  let ksub : (Fin dbLen.succ):| 1 ≤ ksub ∧ ksub ≤ dbLen
  let replyMsg : Msg client := .response .Reply database[ksub.val - 1]! ksub.val
  chan (.client orig) := (chan (.client orig)).enqueue replyMsg
  pc .cloud := D
}

-- DS(self) == /\ pc[self] = "DS"
--             /\ \E k \in msg[self].ses..Len(Database[self]):
--                  chan' = [chan EXCEPT ![(msg[self].orig)] = Append(chan[(msg[self].orig)],
--                    ([type|-> "Reply", dat|->Database[self][k], ses|->k]))]
--             /\ pc' = [pc EXCEPT ![self] = "D"]
--             /\ UNCHANGED << Database, msg, m, op, chistory, ses >>
action _DS {
  require pc .cloud = DS
  let request? := match cloudMsg with
    | some (.request _ token orig) => some (token, orig)
    | _ => none
  require request?.isSome
  let (sesVal, orig) := request?.get!
  let dbLen := database.length
  let ksub : (Fin dbLen.succ):| sesVal ≤ ksub ∧ ksub ≤ dbLen
  let replyMsg : Msg client := .response .Reply database[ksub.val - 1]! ksub.val
  chan (.client orig) := (chan (.client orig)).enqueue replyMsg
  pc .cloud := D
}

-- DB(self) == /\ pc[self] = "DB"
--             /\ \E k \in (IF Len(Database[self])>K THEN Len(Database[self])-K ELSE 1)..Len(Database[self]):
--                  chan' = [chan EXCEPT ![(msg[self].orig)] = Append(chan[(msg[self].orig)],
--                    ([type|-> "Reply", dat|->Database[self][k], ses|->k]))]
--             /\ pc' = [pc EXCEPT ![self] = "D"]
--             /\ UNCHANGED << Database, msg, m, op, chistory, ses >>
action _DB {
  require pc .cloud = DB
  let orig? := match cloudMsg with
    | some (.request _ _ orig) => some orig
    | _ => none
  require orig?.isSome
  let orig := orig?.get!
  let dbLen := database.length
  let lower := if dbLen > K then dbLen - K else 1
  let ksub : (Fin dbLen.succ):| lower ≤ ksub ∧ ksub ≤ dbLen
  let replyMsg : Msg client := .response .Reply database[ksub.val - 1]! ksub.val
  chan (.client orig) := (chan (.client orig)).enqueue replyMsg
  pc .cloud := D
}

-- DG(self) == /\ pc[self] = "DG"
--             /\ LET k == Len(Database[self]) IN
--                  chan' = [chan EXCEPT ![(msg[self].orig)] = Append(chan[(msg[self].orig)],
--                    ([type|-> "Reply", dat|->Database[self][k], ses|->k]))]
--             /\ pc' = [pc EXCEPT ![self] = "D"]
--             /\ UNCHANGED << Database, msg, m, op, chistory, ses >>
action _DG {
  require pc .cloud = DG
  let orig? := match cloudMsg with
    | some (.request _ _ orig) => some orig
    | _ => none
  require orig?.isSome
  let orig := orig?.get!
  let dbLen := database.length
  let replyMsg : Msg client := .response .Reply database.getLast! dbLen
  chan (.client orig) := (chan (.client orig)).enqueue replyMsg
  pc .cloud := D
}

-- ==================== Client actions ====================

-- CW(self) == /\ pc[self] = "CW"
--             /\ IF op[self]<MaxNumOp
--                   THEN /\ op' = [op EXCEPT ![self] = op[self]+1]
--                        /\ chan' = [chan EXCEPT ![Cloud] = Append(chan[Cloud],
--                             ([type |-> "Write", dat |-> op'[self], ses|->ses[self], orig |-> self]))]
--                        /\ pc' = [pc EXCEPT ![self] = "CWA"]
--                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
--                        /\ UNCHANGED << chan, op >>
--             /\ UNCHANGED << Database, msg, m, chistory, ses >>
action _CW (self : client) {
  require pc (.client self) = CW
  if op self < MaxNumOp then
    let newOp := op self + 1
    op self := newOp
    let writeMsg : Msg client := .request (.write newOp) (ses self) self
    chan .cloud := (chan .cloud).enqueue writeMsg
    pc (.client self) := CWA
  else
    pc (.client self) := Done
}

-- CWA(self) == /\ pc[self] = "CWA"
--              /\ Len(chan[self]) > 0
--              /\ m' = [m EXCEPT ![self] = Head(chan[self])]
--              /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
--              /\ ses' = [ses EXCEPT ![self] = m'[self].ses]
--              /\ pc' = [pc EXCEPT ![self] = "CR"]
--              /\ UNCHANGED << Database, msg, op, chistory >>
action _CWA (self : client) {
  require pc (.client self) = CWA
  require (chan (.client self)).isEmpty = false
  let (headMsg, rest) := (chan (.client self)).dequeueD
  let token? := match headMsg with
    | .response _ _ token => some token
    | _ => none
  require token?.isSome
  clientMsg self := some headMsg
  chan (.client self) := rest
  ses self := token?.get!
  pc (.client self) := CR
}

-- CR(self) == /\ pc[self] = "CR"
--             /\ chan' = [chan EXCEPT ![Cloud] = Append(chan[Cloud],
--                  ([type |-> Consistency, ses|->ses[self], orig |-> self]))]
--             /\ pc' = [pc EXCEPT ![self] = "CRA"]
--             /\ UNCHANGED << Database, msg, m, op, chistory, ses >>
action _CR (self : client) {
  require pc (.client self) = CR
  let readMsg : Msg client := .request (.read Consistency) (ses self) self
  chan .cloud := (chan .cloud).enqueue readMsg
  pc (.client self) := CRA
}

-- CRA(self) == /\ pc[self] = "CRA"
--              /\ Len(chan[self]) > 0
--              /\ m' = [m EXCEPT ![self] = Head(chan[self])]
--              /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
--              /\ chistory' = [chistory EXCEPT ![self] = Append(chistory[self],m'[self].dat)]
--              /\ ses' = [ses EXCEPT ![self] = m'[self].ses]
--              /\ pc' = [pc EXCEPT ![self] = "CW"]
--              /\ UNCHANGED << Database, msg, op >>
action _CRA (self : client) {
  require pc (.client self) = CRA
  require (chan (.client self)).isEmpty = false
  let (headMsg, rest) := (chan (.client self)).dequeueD
  let response? := match headMsg with
    | .response _ dat token => some (dat, token)
    | _ => none
  require response?.isSome
  let (dat, token) := response?.get!
  clientMsg self := some headMsg
  chan (.client self) := rest
  chistory self := (chistory self) ++ [dat]
  ses self := token
  pc (.client self) := CW
}

-- ==================== Termination ====================

-- Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
--                /\ UNCHANGED vars
-- termination ∀ C : client, pc (.client C) = Done
-- ==================== Invariants ====================

-- -- Eventual == chistory[1][Len(chistory[1])] \in
-- --               {Database[Cloud][i] : i \in 1..Len(Database[Cloud])}
-- The source Consistent_Prefix invariant has exactly the same definition.
invariant [Eventual]
  ∃ i, i < database.length ∧
    database[i]! = (chistory oneClient).getLast!


-- Session == pc[1]="CW" => chistory[1][Len(chistory[1])] \in
--              {Database[Cloud][i] : i \in ses[1]..Len(Database[Cloud])}
invariant [Session] pc (.client oneClient) = CW →
  -- ∃ i, ses oneClient ≤ i + 1 ∧ i < database.length ∧
  --   database[i]! = (chistory oneClient).getLast!
  -- ∃ i : {n // ses oneClient ≤ n + 1 ∧ n < database.length},
  -- database[i.val]! = (chistory oneClient).getLast!
  (database.drop (ses oneClient - 1)).any (· == (chistory oneClient).getLast!)


-- Bounded_Staleness == pc[1]="CW" => chistory[1][Len(chistory[1])] \in
--   {Database[Cloud][i] : i \in (IF Len(Database[Cloud])>K THEN Len(Database[Cloud])-K ELSE 1)..Len(Database[Cloud])}
-- 1-indexed drop count: (IF Len>K THEN Len-K-1 ELSE 0) keeps the last K+1 elements (or all if Len≤K)
invariant [Bounded_Staleness] pc (.client oneClient) = CW →
  let dropCnt := if database.length > K then database.length - K - 1 else 0
  (database.drop dropCnt).any (· == (chistory oneClient).getLast!)

-- -- Strong == pc[1]="CW" => chistory[1][Len(chistory[1])] = Database[Cloud][Len(Database[Cloud])]
invariant [Strong] pc (.client oneClient) = CW →
  (chistory oneClient).getLast! = database.getLast!

#gen_spec
#gen_executable

-- ==================== Model checking ====================
-- Each check below uses the instance of one TLC model `Benchmarks/TLA/CosmosDB/properties-*.cfg`,
-- named above the check. Uncomment one entire command block to run it.
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s:
-- * `client := Fin 1`: a single client, `0` (cfg: `NumClients = 1`, with
--   `Clients == 1..NumClients`). `Node.cloud` stands for TLA+'s `Cloud == 0`, and
--   `Node.client i` for TLA+'s client `i + 1`.
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields:
-- * `oneClient := 0`: the client whose history the invariants read, TLA+'s client `1`. The cfg
--   has no counterpart, since the TLA+ invariants name `chistory[1]` and `pc[1]` directly.
-- * `MaxNumOp := 3`: the client makes 3 writes, each followed by a read (cfg: `MaxNumOp = 3`).
--   This satisfies the source assumption `MaxNumOp < 10`.
-- * `K := 1` or `K := 0`: a `Bounded_Staleness` read returns one of the last `K + 1` entries
--   (cfg: `K = 1` or `K = 0`).
-- * `Consistency := ConsistencyLevel.Strong`, and so on: the consistency level of the client's
--   reads (cfg: `Consistency = "Strong"`, and so on).
--
-- The other settings of the cfgs:
-- * `INVARIANTS Eventual Consistent_Prefix Session Bounded_Staleness Strong`: every case checks
--   all declared invariants. `Eventual` stands for both `Eventual` and `Consistent_Prefix`, which
--   the source defines identically.
-- * `CHECK_DEADLOCK FALSE`: the `termination` clause above is commented out, so Veil reports no
--   deadlocks either. The client stops at `Done`.
-- * No depth bound or state constraint is used, as in the cfgs.
-- * `counts-*.cfg` and `bug-*.cfg` check fewer invariants. `Benchmarks/TLA/CosmosDB/check.py`
--   runs their Veil counterparts on copies of this module that declare only those invariants.
-- Options:
-- * `compiled` runs the search only in a compiled checker, not in Lean's interpreter.
-- * Fingerprints and parallel search use the defaults; Elab.async does not serialize Veil's
--   background tasks.

-- cfg: `properties-Strong-3-1.cfg`.
-- Strong reads the latest write: all invariants hold (26 states).
-- #model_check compiled
--   { client := Fin 1 }
--   { oneClient := 0, MaxNumOp := 3, K := 1,
--     Consistency := ConsistencyLevel.Strong }

-- cfg: `properties-Session-3-1.cfg`.
-- With one client, Session's token also forces reads to see its latest write.
-- Expected: all invariants hold (26 states).
-- #model_check compiled
--   { client := Fin 1 }
--   { oneClient := 0, MaxNumOp := 3, K := 1,
--     Consistency := ConsistencyLevel.Session }

-- cfg: `properties-Bounded_Staleness-3-0.cfg`.
-- K = 0 forces Bounded Staleness to return the latest entry.
-- Expected: all invariants hold (26 states).
-- #model_check compiled
--   { client := Fin 1 }
--   { oneClient := 0, MaxNumOp := 3, K := 0,
--     Consistency := ConsistencyLevel.Bounded_Staleness }

-- cfg: `properties-Bounded_Staleness-3-1.cfg`.
-- K = 1 permits write 1 followed by read 0: Bounded Staleness holds, Strong fails.
-- Expected: safety_failure (violates: Strong).
-- #model_check compiled
--   { client := Fin 1 }
--   { oneClient := 0, MaxNumOp := 3, K := 1,
--     Consistency := ConsistencyLevel.Bounded_Staleness }

-- cfg: `properties-Eventual-3-1.cfg`.
-- Eventual permits the same stale read; the search stops at the Strong violation.
-- Expected: safety_failure (violates: Strong).
-- #model_check compiled
--   { client := Fin 1 }
--   { oneClient := 0, MaxNumOp := 3, K := 1,
--     Consistency := ConsistencyLevel.Eventual }

-- cfg: `properties-Consistent_Prefix-3-1.cfg`.
-- Consistent Prefix has the same read choices as Eventual in this source model.
-- Expected: safety_failure (violates: Strong).
-- #model_check compiled
--   { client := Fin 1 }
--   { oneClient := 0, MaxNumOp := 3, K := 1,
--     Consistency := ConsistencyLevel.Consistent_Prefix }
end SWSCOP
