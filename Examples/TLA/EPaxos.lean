module

public import Veil

/-!
Adapted into Veil from the EPaxos specification by Iulian Moraru.
Upstream license: Apache-2.0; see Benchmarks/TLA/EPaxos/LICENSE.
Copyright 2013 Carnegie Mellon University
Source: https://github.com/efficient/epaxos/blob/791b115669fca472d3136f6a2eda46c00b3f8251/tla+/EgalitarianPaxos.tla
Modified locally: translated to Veil.

The source repository has no TLC configuration. The checks at the end of this file are compared
with the TLC models in `Benchmarks/TLA/EPaxos/`: `MCEgalitarianPaxos.tla` and its `.cfg` files.

Encoding choices:
* A message is a value of the inductive type `Msg`, with one constructor per message type.
  `msg.src`, `msg.cmd`, ... read its fields, as in the source.
* `none == CHOOSE c : c \notin Commands` is `Option.none`. Command fields have type
  `Option Command`, where `some c` stands for the command `c`.
* The instance `<<r, k>>` is `⟨r, k - 1⟩ : Instance Replica (Fin cardCommands)`. Its index has
  type `Fin cardCommands`, so `Instances == Replicas \X (1..Cardinality(Commands))` is the whole
  type.
* The ballot `<<n, r>>` is `⟨n, r⟩ : Ballot Replica`. Ballot numbers, sequence numbers and
  `crtInst` are `Nat`s, as in the source. `MaxBallot` and the number of commands bound them.
* The variable `executed` is left out: `Init` sets it to `[r \in Replicas |-> {}]`, and every
  action leaves it unchanged.
* No action sets a status to `"executed"`, which is not even in `Status`. So
  `status \in {"committed", "executed"}` is written `status = .committed`.
-/

-- -------------------------- MODULE EgalitarianPaxos --------------------------
-- EXTENDS Naturals, FiniteSets

veil module EPaxos

-- Status == {"not-seen", "pre-accepted", "accepted", "committed"}
@[veil_decl]
inductive Status where
  | notSeen
  | preAccepted
  | accepted
  | committed

-- Status \cup {"OK"}: the status of a try-pre-accept-reply.
@[veil_decl]
inductive StatusOrOK where
  | ok
  | status (s : Status)

-- Instances == Replicas \X (1..Cardinality(Commands))
-- The instance <<r, k>> is `{ leader := r, idx := k - 1 }`, where `idx : Fin cardCommands`.
@[veil_decl]
structure Instance (rep idxT : Type) where
  leader : rep
  idx : idxT
deriving instance Veil.Enumeration for Instance
-- `FinEncodable` for the arrays that store `committed`, `FinEncodableInjOnly` for action labels.
deriving instance Veil.FinEncodable, Veil.FinEncodableInjOnly for Instance

-- A ballot <<num, owner>>, in Nat \X Replicas.
@[veil_decl]
structure Ballot (rep : Type) where
  num : Nat
  owner : rep

-- A record of a command log:
-- [inst: Instances, status: Status, ballot: Nat \X Replicas, cmd: Commands \cup {none},
--  deps: SUBSET Instances, seq: Nat]
@[veil_decl]
structure LogRec (inst rep cmd instSet : Type) where
  inst : inst
  status : Status
  ballot : Ballot rep
  cmd : Option cmd
  deps : instSet
  seq : Nat

-- An element <<cmd, deps, seq>> of committed[i], in
-- (Commands \cup {none}) \X (SUBSET Instances) \X Nat.
@[veil_decl]
structure CommitTuple (cmd instSet : Type) where
  cmd : Option cmd
  deps : instSet
  seq : Nat

-- Message ==
--         [type: {"pre-accept"}, src: Replicas, dst: Replicas,
--         inst: Instances, ballot: Nat \X Replicas,
--         cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Nat]
--   \cup  [type: {"accept"}, src: Replicas, dst: Replicas,
--         inst: Instances, ballot: Nat \X Replicas,
--         cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Nat]
--   \cup  [type: {"commit"},
--         inst: Instances, ballot: Nat \X Replicas,
--         cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Nat]
--   \cup  [type: {"prepare"}, src: Replicas, dst: Replicas,
--         inst: Instances, ballot: Nat \X Replicas]
--   \cup  [type: {"pre-accept-reply"}, src: Replicas, dst: Replicas,
--         inst: Instances, ballot: Nat \X Replicas,
--         deps: SUBSET Instances, seq: Nat, committed: SUBSET Instances]
--   \cup  [type: {"accept-reply"}, src: Replicas, dst: Replicas,
--         inst: Instances, ballot: Nat \X Replicas]
--   \cup  [type: {"prepare-reply"}, src: Replicas, dst: Replicas,
--         inst: Instances, ballot: Nat \X Replicas, prev_ballot: Nat \X Replicas,
--         status: Status,
--         cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Nat]
--   \cup  [type: {"try-pre-accept"}, src: Replicas, dst: Replicas,
--         inst: Instances, ballot: Nat \X Replicas,
--         cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Nat]
--   \cup  [type: {"try-pre-accept-reply"}, src: Replicas, dst: Replicas,
--         inst: Instances, ballot: Nat \X Replicas, status: Status \cup {"OK"}]
@[veil_decl]
inductive Msg (rep inst cmd instSet : Type) where
  | preAccept (src dst : rep) (inst : inst) (ballot : Ballot rep)
      (cmd : Option cmd) (deps : instSet) (seq : Nat)
  | accept (src dst : rep) (inst : inst) (ballot : Ballot rep)
      (cmd : Option cmd) (deps : instSet) (seq : Nat)
  | commit (inst : inst) (ballot : Ballot rep)
      (cmd : Option cmd) (deps : instSet) (seq : Nat)
  | prepare (src dst : rep) (inst : inst) (ballot : Ballot rep)
  | preAcceptReply (src dst : rep) (inst : inst) (ballot : Ballot rep)
      (deps : instSet) (seq : Nat) (committed : instSet)
  | acceptReply (src dst : rep) (inst : inst) (ballot : Ballot rep)
  | prepareReply (src dst : rep) (inst : inst) (ballot : Ballot rep) (prevBallot : Ballot rep)
      (status : Status) (cmd : Option cmd) (deps : instSet) (seq : Nat)
  | tryPreAccept (src dst : rep) (inst : inst) (ballot : Ballot rep)
      (cmd : Option cmd) (deps : instSet) (seq : Nat)
  | tryPreAcceptReply (src dst : rep) (inst : inst) (ballot : Ballot rep) (status : StatusOrOK)

-- The values of the `type` field of a message.
@[veil_decl]
inductive MsgType where
  | preAccept
  | accept
  | commit
  | prepare
  | preAcceptReply
  | acceptReply
  | prepareReply
  | tryPreAccept
  | tryPreAcceptReply

-- The fields of a message, read as the source reads them (`msg.type`, `msg.src`, ...). The source
-- reads a field only from messages whose type has it; on other messages these return a default.
def Msg.type {rep inst cmd instSet : Type} : Msg rep inst cmd instSet → MsgType
  | .preAccept .. => .preAccept
  | .accept .. => .accept
  | .commit .. => .commit
  | .prepare .. => .prepare
  | .preAcceptReply .. => .preAcceptReply
  | .acceptReply .. => .acceptReply
  | .prepareReply .. => .prepareReply
  | .tryPreAccept .. => .tryPreAccept
  | .tryPreAcceptReply .. => .tryPreAcceptReply

def Msg.src {rep inst cmd instSet : Type} [Inhabited rep] :
    Msg rep inst cmd instSet → rep
  | .preAccept src .. | .accept src .. | .prepare src .. | .preAcceptReply src ..
  | .acceptReply src .. | .prepareReply src .. | .tryPreAccept src ..
  | .tryPreAcceptReply src .. => src
  | .commit .. => default

def Msg.dst {rep inst cmd instSet : Type} [Inhabited rep] :
    Msg rep inst cmd instSet → rep
  | .preAccept _ dst .. | .accept _ dst .. | .prepare _ dst .. | .preAcceptReply _ dst ..
  | .acceptReply _ dst .. | .prepareReply _ dst .. | .tryPreAccept _ dst ..
  | .tryPreAcceptReply _ dst .. => dst
  | .commit .. => default

def Msg.inst {rep inst cmd instSet : Type} : Msg rep inst cmd instSet → inst
  | .preAccept _ _ i .. | .accept _ _ i .. | .prepare _ _ i .. | .preAcceptReply _ _ i ..
  | .acceptReply _ _ i .. | .prepareReply _ _ i .. | .tryPreAccept _ _ i ..
  | .tryPreAcceptReply _ _ i .. | .commit i .. => i

def Msg.ballot {rep inst cmd instSet : Type} : Msg rep inst cmd instSet → Ballot rep
  | .preAccept _ _ _ b .. | .accept _ _ _ b .. | .prepare _ _ _ b | .preAcceptReply _ _ _ b ..
  | .acceptReply _ _ _ b | .prepareReply _ _ _ b .. | .tryPreAccept _ _ _ b ..
  | .tryPreAcceptReply _ _ _ b _ | .commit _ b .. => b

def Msg.cmd {rep inst cmd instSet : Type} : Msg rep inst cmd instSet → Option cmd
  | .preAccept _ _ _ _ c .. | .accept _ _ _ _ c .. | .tryPreAccept _ _ _ _ c ..
  | .commit _ _ c .. | .prepareReply _ _ _ _ _ _ c .. => c
  | _ => none

def Msg.deps {rep inst cmd instSet : Type} [Inhabited instSet] :
    Msg rep inst cmd instSet → instSet
  | .preAccept _ _ _ _ _ d _ | .accept _ _ _ _ _ d _ | .tryPreAccept _ _ _ _ _ d _
  | .commit _ _ _ d _ | .prepareReply _ _ _ _ _ _ _ d _ | .preAcceptReply _ _ _ _ d .. => d
  | _ => default

def Msg.seq {rep inst cmd instSet : Type} : Msg rep inst cmd instSet → Nat
  | .preAccept _ _ _ _ _ _ s | .accept _ _ _ _ _ _ s | .tryPreAccept _ _ _ _ _ _ s
  | .commit _ _ _ _ s | .prepareReply _ _ _ _ _ _ _ _ s | .preAcceptReply _ _ _ _ _ s _ => s
  | _ => 0

def Msg.committed {rep inst cmd instSet : Type} [Inhabited instSet] :
    Msg rep inst cmd instSet → instSet
  | .preAcceptReply _ _ _ _ _ _ c => c
  | _ => default

def Msg.prevBallot {rep inst cmd instSet : Type} [Inhabited rep] :
    Msg rep inst cmd instSet → Ballot rep
  | .prepareReply _ _ _ _ pb .. => pb
  | _ => default

-- The status of a prepare-reply.
def Msg.status {rep inst cmd instSet : Type} : Msg rep inst cmd instSet → Status
  | .prepareReply _ _ _ _ _ s .. => s
  | _ => .notSeen

-- The status of a try-pre-accept-reply.
def Msg.replyStatus {rep inst cmd instSet : Type} : Msg rep inst cmd instSet → StatusOrOK
  | .tryPreAcceptReply _ _ _ _ s => s
  | _ => .ok

-- Max(S) == IF S = {} THEN 0 ELSE CHOOSE i \in S : \A j \in S : j <= i
-- It takes the elements of the set as a list. It is named `MaxOf` because Lean has a class `Max`.
def MaxOf (S : List Nat) : Nat := S.foldl max 0

-- (*********************************************************************************)
-- (* Constant parameters:                                                          *)
-- (*       Commands: the set of all possible commands                              *)
-- (*       Replicas: the set of all EPaxos replicas                                *)
-- (*       FastQuorums(r): the set of all fast quorums where r is a command leader *)
-- (*       SlowQuorums(r): the set of all slow quorums where r is a command leader *)
-- (*********************************************************************************)

-- CONSTANTS Commands, Replicas, FastQuorums(_), SlowQuorums(_), MaxBallot
type Command
type Replica
-- Cardinality(Commands), the size of the index type of `Instance`.
param cardCommands : Nat

type CommandSet
type ReplicaSet
-- Sets of quorums, such as FastQuorums(r).
type QuorumSet
type InstanceSet
type LogSet
type CommitTupleSet
type MsgSet
instantiate cmdSet : TSet Command CommandSet
instantiate repSet : TSet Replica ReplicaSet
instantiate quorumSet : TSet ReplicaSet QuorumSet
instantiate instSet : TSet (Instance Replica (Fin cardCommands)) InstanceSet
instantiate logSet :
  TSet (LogRec (Instance Replica (Fin cardCommands)) Replica Command InstanceSet) LogSet
instantiate tupleSet : TSet (CommitTuple Command InstanceSet) CommitTupleSet
instantiate msgSet :
  TSet (Msg Replica (Instance Replica (Fin cardCommands)) Command InstanceSet) MsgSet

-- `Commands` and `Replicas` as values, for `Cardinality` and `SUBSET`.
immutable individual Commands : CommandSet
immutable individual Replicas : ReplicaSet
immutable function FastQuorums (r : Replica) : QuorumSet
immutable function SlowQuorums (r : Replica) : QuorumSet
immutable individual MaxBallot : Nat

-- (*******************************************************************************)
-- (* Variables:                                                                  *)
-- (*                                                                             *)
-- (*          comdLog = the commands log at each replica                         *)
-- (*          proposed = command that have been proposed                         *)
-- (*          executed = the log of executed commands at each replica            *)
-- (*          sentMsg = sent (but not yet received) messages                     *)
-- (*          crtInst = the next instance available for a command                *)
-- (*                    leader                                                   *)
-- (*          leaderOfInst = the set of instances each replica has               *)
-- (*                         started but not yet finalized                       *)
-- (*          committed = maps commands to set of commit attributs               *)
-- (*                      tuples                                                 *)
-- (*          ballots = largest ballot number used by any                        *)
-- (*                    replica                                                  *)
-- (*          preparing = set of instances that each replica is                  *)
-- (*                      currently preparing (i.e. recovering)                  *)
-- (*                                                                             *)
-- (*                                                                             *)
-- (*******************************************************************************)

-- VARIABLES cmdLog, proposed, executed, sentMsg, crtInst, leaderOfInst,
--           committed, ballots, preparing
function cmdLog (r : Replica) : LogSet
individual proposed : CommandSet
individual sentMsg : MsgSet
function crtInst (r : Replica) : Nat
function leaderOfInst (r : Replica) : InstanceSet
function committed (i : Instance Replica (Fin cardCommands)) : CommitTupleSet
individual ballots : Nat
function preparing (r : Replica) : InstanceSet

set_option veil.deferVCGeneration true

veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

-- `Commands` and `Replicas` contain every command and every replica, and `cardCommands` is the
-- number of commands.
assumption [commands_complete] ∀ c : Command, c ∈ Commands
assumption [replicas_complete] ∀ r : Replica, r ∈ Replicas
assumption [card_commands] cmdSet.count Commands = cardCommands

-- ASSUME IsFiniteSet(Replicas)
-- (Every instance of this module has finitely many replicas.)

-- (***************************************************************************)
-- (* Quorum conditions:                                                      *)
-- (*  (simplified)                                                           *)
-- (***************************************************************************)

-- ASSUME \A r \in Replicas:
--   /\ SlowQuorums(r) \subseteq SUBSET Replicas
--   /\ \A SQ \in SlowQuorums(r):
--     /\ r \in SQ
--     /\ Cardinality(SQ) = (Cardinality(Replicas) \div 2) + 1
assumption [slow_quorums] ∀ r : Replica, ∀ SQ : { SQ // SQ ∈ SlowQuorums r },
  TSet.isSubset SQ.val Replicas ∧ r ∈ SQ.val ∧
  repSet.count SQ.val = (repSet.count Replicas / 2) + 1

-- ASSUME \A r \in Replicas:
--   /\ FastQuorums(r) \subseteq SUBSET Replicas
--   /\ \A FQ \in FastQuorums(r):
--     /\ r \in FQ
--     /\ Cardinality(FQ) = (Cardinality(Replicas) \div 2) +
--                          ((Cardinality(Replicas) \div 2) + 1) \div 2
assumption [fast_quorums] ∀ r : Replica, ∀ FQ : { FQ // FQ ∈ FastQuorums r },
  TSet.isSubset FQ.val Replicas ∧ r ∈ FQ.val ∧
  repSet.count FQ.val = (repSet.count Replicas / 2) + ((repSet.count Replicas / 2) + 1) / 2

-- (***************************************************************************)
-- (* Initial state predicate                                                 *)
-- (***************************************************************************)

-- Init ==
--   /\ sentMsg = {}
--   /\ cmdLog = [r \in Replicas |-> {}]
--   /\ proposed = {}
--   /\ executed = [r \in Replicas |-> {}]
--   /\ crtInst = [r \in Replicas |-> 1]
--   /\ leaderOfInst = [r \in Replicas |-> {}]
--   /\ committed = [i \in Instances |-> {}]
--   /\ ballots = 1
--   /\ preparing = [r \in Replicas |-> {}]
after_init {
  sentMsg := msgSet.empty
  cmdLog R := logSet.empty
  proposed := cmdSet.empty
  crtInst R := 1
  leaderOfInst R := instSet.empty
  committed I := tupleSet.empty
  ballots := 1
  preparing R := instSet.empty
}

-- (***************************************************************************)
-- (* Actions                                                                 *)
-- (***************************************************************************)

-- StartPhase1(C, cleader, Q, inst, ballot, oldMsg) ==
--     LET newDeps == {rec.inst: rec \in cmdLog[cleader]}
--         newSeq == 1 + Max({t.seq: t \in cmdLog[cleader]})
--         oldRecs == {rec \in cmdLog[cleader] : rec.inst = inst} IN
--         /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ oldRecs) \cup
--                                 {[inst   |-> inst,
--                                   status |-> "pre-accepted",
--                                   ballot |-> ballot,
--                                   cmd    |-> C,
--                                   deps   |-> newDeps,
--                                   seq    |-> newSeq ]}]
--         /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \cup {inst}]
--         /\ sentMsg' = (sentMsg \ oldMsg) \cup
--                                 [type  : {"pre-accept"},
--                                   src   : {cleader},
--                                   dst   : Q \ {cleader},
--                                   inst  : {inst},
--                                   ballot: {ballot},
--                                   cmd   : {C},
--                                   deps  : {newDeps},
--                                   seq   : {newSeq}]
procedure StartPhase1 (C : Option Command) (cleader : Replica) (Q : ReplicaSet)
    (inst : Instance Replica (Fin cardCommands)) (ballot : Ballot Replica) (oldMsg : MsgSet) {
  let newDeps : InstanceSet := TSet.map (cmdLog cleader) (·.inst)
  let newSeq := 1 + MaxOf ((logSet.toList (cmdLog cleader)).map (·.seq))
  let oldRecs := logSet.filter (cmdLog cleader) (fun rec => rec.inst = inst)
  cmdLog cleader := logSet.insert
    { inst := inst, status := .preAccepted, ballot := ballot, cmd := C, deps := newDeps,
      seq := newSeq }
    (logSet.diff (cmdLog cleader) oldRecs)
  leaderOfInst cleader := instSet.insert inst (leaderOfInst cleader)
  let preAccepts : MsgSet := TSet.map (repSet.remove cleader Q)
    (fun dst => Msg.preAccept cleader dst inst ballot C newDeps newSeq)
  sentMsg := msgSet.union (msgSet.diff sentMsg oldMsg) preAccepts
}

-- Propose(C, cleader) ==
--     LET newInst == <<cleader, crtInst[cleader]>>
--         newBallot == <<0, cleader>>
--     IN  /\ proposed' = proposed \cup {C}
--         /\ (\E Q \in FastQuorums(cleader):
--                  StartPhase1(C, cleader, Q, newInst, newBallot, {}))
--         /\ crtInst' = [crtInst EXCEPT ![cleader] = @ + 1]
--         /\ UNCHANGED << executed, committed, ballots, preparing >>
action Propose (C : Command) (cleader : Replica) {
  -- `C \in Commands \ proposed`, from `CommandLeaderAction`.
  require C ∉ proposed
  -- `newInst` is in `Instances`: each proposal of `cleader` uses a command not yet proposed, so
  -- `crtInst[cleader]` is at most `Cardinality(Commands)` here. The `assert` reports it otherwise.
  assert 1 ≤ crtInst cleader ∧ crtInst cleader ≤ cardCommands
  let idx : Fin cardCommands :| idx.val + 1 = crtInst cleader
  let newInst : Instance Replica (Fin cardCommands) := { leader := cleader, idx := idx }
  let newBallot : Ballot Replica := { num := 0, owner := cleader }
  proposed := cmdSet.insert C proposed
  let Q ← pick { Q // Q ∈ FastQuorums cleader }
  StartPhase1 (some C) cleader Q.val newInst newBallot msgSet.empty
  crtInst cleader := crtInst cleader + 1
}

-- Phase1Reply(replica) ==
--     \E msg \in sentMsg:
--         /\ msg.type = "pre-accept"
--         /\ msg.dst = replica
--         /\ LET oldRec == {rec \in cmdLog[replica]: rec.inst = msg.inst} IN
--             /\ (\A rec \in oldRec :
--                 (rec.ballot = msg.ballot \/rec.ballot[1] < msg.ballot[1]))
--             /\ LET newDeps == msg.deps \cup
--                             ({t.inst: t \in cmdLog[replica]} \ {msg.inst})
--                    newSeq == Max({msg.seq,
--                                   1 + Max({t.seq: t \in cmdLog[replica]})})
--                    instCom == {t.inst: t \in {tt \in cmdLog[replica] :
--                               tt.status \in {"committed", "executed"}}} IN
--                 /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ oldRec) \cup
--                                     {[inst   |-> msg.inst,
--                                       status |-> "pre-accepted",
--                                       ballot |-> msg.ballot,
--                                       cmd    |-> msg.cmd,
--                                       deps   |-> newDeps,
--                                       seq    |-> newSeq]}]
--                 /\ sentMsg' = (sentMsg \ {msg}) \cup
--                                     {[type  |-> "pre-accept-reply",
--                                       src   |-> replica,
--                                       dst   |-> msg.src,
--                                       inst  |-> msg.inst,
--                                       ballot|-> msg.ballot,
--                                       deps  |-> newDeps,
--                                       seq   |-> newSeq,
--                                       committed|-> instCom]}
--                 /\ UNCHANGED << proposed, crtInst, executed, leaderOfInst,
--                                 committed, ballots, preparing >>
action Phase1Reply (replica : Replica) {
  let msg : { m // m ∈ sentMsg } :| msg.val.type = .preAccept ∧ msg.val.dst = replica
  let msg := msg.val
  let oldRec := logSet.filter (cmdLog replica) (fun rec => rec.inst = msg.inst)
  require ∀ rec : { rec // rec ∈ oldRec },
    rec.val.ballot = msg.ballot ∨ rec.val.ballot.num < msg.ballot.num
  let newDeps := instSet.union msg.deps
    (instSet.remove msg.inst (TSet.map (cmdLog replica) (·.inst)))
  let newSeq := MaxOf [msg.seq, 1 + MaxOf ((logSet.toList (cmdLog replica)).map (·.seq))]
  let instCom : InstanceSet :=
    TSet.map (logSet.filter (cmdLog replica) (fun tt => tt.status = .committed)) (·.inst)
  cmdLog replica := logSet.insert
    { inst := msg.inst, status := .preAccepted, ballot := msg.ballot, cmd := msg.cmd,
      deps := newDeps, seq := newSeq }
    (logSet.diff (cmdLog replica) oldRec)
  sentMsg := msgSet.insert
    (.preAcceptReply replica msg.src msg.inst msg.ballot newDeps newSeq instCom)
    (msgSet.remove msg sentMsg)
}

-- Phase1Fast(cleader, i, Q) ==
--     /\ i \in leaderOfInst[cleader]
--     /\ Q \in FastQuorums(cleader)
--     /\ \E record \in cmdLog[cleader]:
--         /\ record.inst = i
--         /\ record.status = "pre-accepted"
--         /\ record.ballot[1] = 0
--         /\ LET replies == {msg \in sentMsg:
--                                 /\ msg.inst = i
--                                 /\ msg.type = "pre-accept-reply"
--                                 /\ msg.dst = cleader
--                                 /\ msg.src \in Q
--                                 /\ msg.ballot = record.ballot} IN
--             /\ (\A replica \in (Q \ {cleader}):
--                     \E msg \in replies: msg.src = replica)
--             /\ (\A r1, r2 \in replies:
--                 /\ r1.deps = r2.deps
--                 /\ r1.seq = r2.seq)
--             /\ LET r == CHOOSE r \in replies : TRUE IN
--                 /\ LET localCom == {t.inst:
--                             t \in {tt \in cmdLog[cleader] :
--                                  tt.status \in {"committed", "executed"}}}
--                        extCom == UNION {msg.committed: msg \in replies} IN
--                        (r.deps \subseteq (localCom \cup extCom))
--                 /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ {record}) \cup
--                                         {[inst   |-> i,
--                                           status |-> "committed",
--                                           ballot |-> record.ballot,
--                                           cmd    |-> record.cmd,
--                                           deps   |-> r.deps,
--                                           seq    |-> r.seq ]}]
--                 /\ sentMsg' = (sentMsg \ replies) \cup
--                             {[type  |-> "commit",
--                             inst    |-> i,
--                             ballot  |-> record.ballot,
--                             cmd     |-> record.cmd,
--                             deps    |-> r.deps,
--                             seq     |-> r.seq]}
--                 /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \ {i}]
--                 /\ committed' = [committed EXCEPT ![i] =
--                                             @ \cup {<<record.cmd, r.deps, r.seq>>}]
--                 /\ UNCHANGED << proposed, executed, crtInst, ballots, preparing >>
action Phase1Fast (cleader : Replica) (i : Instance Replica (Fin cardCommands)) (Q : ReplicaSet) {
  require i ∈ leaderOfInst cleader
  require Q ∈ FastQuorums cleader
  let record : { rec // rec ∈ cmdLog cleader } :|
    record.val.inst = i ∧ record.val.status = .preAccepted ∧ record.val.ballot.num = 0
  let record := record.val
  let replies := msgSet.filter sentMsg (fun msg =>
    msg.inst = i ∧ msg.type = .preAcceptReply ∧ msg.dst = cleader ∧ msg.src ∈ Q ∧
    msg.ballot = record.ballot)
  require ∀ replica : { r // r ∈ repSet.remove cleader Q },
    ∃ msg : { msg // msg ∈ replies }, msg.val.src = replica.val
  require ∀ r1 r2 : { r // r ∈ replies }, r1.val.deps = r2.val.deps ∧ r1.val.seq = r2.val.seq
  -- `r == CHOOSE r \in replies : TRUE`. Every reply has the same `deps` and `seq`, and only those
  -- are used, so any choice gives the same step. TLC reports an error if `replies` is empty.
  assert ¬ msgSet.isEmpty replies
  let r ← pick { r // r ∈ replies }
  let r := r.val
  let localCom : InstanceSet :=
    TSet.map (logSet.filter (cmdLog cleader) (fun tt => tt.status = .committed)) (·.inst)
  let extCom := (msgSet.toList replies).foldl (fun acc msg => instSet.union acc msg.committed)
    instSet.empty
  require TSet.isSubset r.deps (instSet.union localCom extCom)
  cmdLog cleader := logSet.insert
    { inst := i, status := .committed, ballot := record.ballot, cmd := record.cmd,
      deps := r.deps, seq := r.seq }
    (logSet.remove record (cmdLog cleader))
  sentMsg := msgSet.insert (.commit i record.ballot record.cmd r.deps r.seq)
    (msgSet.diff sentMsg replies)
  leaderOfInst cleader := instSet.remove i (leaderOfInst cleader)
  committed i := tupleSet.insert { cmd := record.cmd, deps := r.deps, seq := r.seq } (committed i)
}

-- Phase1Slow(cleader, i, Q) ==
--     /\ i \in leaderOfInst[cleader]
--     /\ Q \in SlowQuorums(cleader)
--     /\ \E record \in cmdLog[cleader]:
--         /\ record.inst = i
--         /\ record.status = "pre-accepted"
--         /\ LET replies == {msg \in sentMsg:
--                                 /\ msg.inst = i
--                                 /\ msg.type = "pre-accept-reply"
--                                 /\ msg.dst = cleader
--                                 /\ msg.src \in Q
--                                 /\ msg.ballot = record.ballot} IN
--             /\ (\A replica \in (Q \ {cleader}): \E msg \in replies: msg.src = replica)
--             /\ LET finalDeps == UNION {msg.deps : msg \in replies}
--                    finalSeq == Max({msg.seq : msg \in replies}) IN
--                 /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ {record}) \cup
--                                         {[inst   |-> i,
--                                           status |-> "accepted",
--                                           ballot |-> record.ballot,
--                                           cmd    |-> record.cmd,
--                                           deps   |-> finalDeps,
--                                           seq    |-> finalSeq ]}]
--                 /\ \E SQ \in SlowQuorums(cleader):
--                    (sentMsg' = (sentMsg \ replies) \cup
--                             [type : {"accept"},
--                             src : {cleader},
--                             dst : SQ \ {cleader},
--                             inst : {i},
--                             ballot: {record.ballot},
--                             cmd : {record.cmd},
--                             deps : {finalDeps},
--                             seq : {finalSeq}])
--                 /\ UNCHANGED << proposed, executed, crtInst, leaderOfInst,
--                                 committed, ballots, preparing >>
action Phase1Slow (cleader : Replica) (i : Instance Replica (Fin cardCommands)) (Q : ReplicaSet) {
  require i ∈ leaderOfInst cleader
  require Q ∈ SlowQuorums cleader
  let record : { rec // rec ∈ cmdLog cleader } :|
    record.val.inst = i ∧ record.val.status = .preAccepted
  let record := record.val
  let replies := msgSet.filter sentMsg (fun msg =>
    msg.inst = i ∧ msg.type = .preAcceptReply ∧ msg.dst = cleader ∧ msg.src ∈ Q ∧
    msg.ballot = record.ballot)
  require ∀ replica : { r // r ∈ repSet.remove cleader Q },
    ∃ msg : { msg // msg ∈ replies }, msg.val.src = replica.val
  let finalDeps := (msgSet.toList replies).foldl (fun acc msg => instSet.union acc msg.deps)
    instSet.empty
  let finalSeq := MaxOf ((msgSet.toList replies).map (·.seq))
  cmdLog cleader := logSet.insert
    { inst := i, status := .accepted, ballot := record.ballot, cmd := record.cmd,
      deps := finalDeps, seq := finalSeq }
    (logSet.remove record (cmdLog cleader))
  let SQ ← pick { SQ // SQ ∈ SlowQuorums cleader }
  let accepts : MsgSet := TSet.map (repSet.remove cleader SQ.val)
    (fun dst => Msg.accept cleader dst i record.ballot record.cmd finalDeps finalSeq)
  sentMsg := msgSet.union (msgSet.diff sentMsg replies) accepts
}

-- Phase2Reply(replica) ==
--     \E msg \in sentMsg:
--         /\ msg.type = "accept"
--         /\ msg.dst = replica
--         /\ LET oldRec == {rec \in cmdLog[replica]: rec.inst = msg.inst} IN
--             /\ (\A rec \in oldRec: (rec.ballot = msg.ballot \/
--                                     rec.ballot[1] < msg.ballot[1]))
--             /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ oldRec) \cup
--                                 {[inst   |-> msg.inst,
--                                   status |-> "accepted",
--                                   ballot |-> msg.ballot,
--                                   cmd    |-> msg.cmd,
--                                   deps   |-> msg.deps,
--                                   seq    |-> msg.seq]}]
--             /\ sentMsg' = (sentMsg \ {msg}) \cup
--                                 {[type  |-> "accept-reply",
--                                   src   |-> replica,
--                                   dst   |-> msg.src,
--                                   inst  |-> msg.inst,
--                                   ballot|-> msg.ballot]}
--             /\ UNCHANGED << proposed, crtInst, executed, leaderOfInst,
--                             committed, ballots, preparing >>
action Phase2Reply (replica : Replica) {
  let msg : { m // m ∈ sentMsg } :| msg.val.type = .accept ∧ msg.val.dst = replica
  let msg := msg.val
  let oldRec := logSet.filter (cmdLog replica) (fun rec => rec.inst = msg.inst)
  require ∀ rec : { rec // rec ∈ oldRec },
    rec.val.ballot = msg.ballot ∨ rec.val.ballot.num < msg.ballot.num
  cmdLog replica := logSet.insert
    { inst := msg.inst, status := .accepted, ballot := msg.ballot, cmd := msg.cmd,
      deps := msg.deps, seq := msg.seq }
    (logSet.diff (cmdLog replica) oldRec)
  sentMsg := msgSet.insert (.acceptReply replica msg.src msg.inst msg.ballot)
    (msgSet.remove msg sentMsg)
}

-- Phase2Finalize(cleader, i, Q) ==
--     /\ i \in leaderOfInst[cleader]
--     /\ Q \in SlowQuorums(cleader)
--     /\ \E record \in cmdLog[cleader]:
--         /\ record.inst = i
--         /\ record.status = "accepted"
--         /\ LET replies == {msg \in sentMsg:
--                                 /\ msg.inst = i
--                                 /\ msg.type = "accept-reply"
--                                 /\ msg.dst = cleader
--                                 /\ msg.src \in Q
--                                 /\ msg.ballot = record.ballot} IN
--             /\ (\A replica \in (Q \ {cleader}): \E msg \in replies:
--                                                         msg.src = replica)
--             /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ {record}) \cup
--                                     {[inst   |-> i,
--                                       status |-> "committed",
--                                       ballot |-> record.ballot,
--                                       cmd    |-> record.cmd,
--                                       deps   |-> record.deps,
--                                       seq    |-> record.seq ]}]
--             /\ sentMsg' = (sentMsg \ replies) \cup
--                         {[type  |-> "commit",
--                         inst    |-> i,
--                         ballot  |-> record.ballot,
--                         cmd     |-> record.cmd,
--                         deps    |-> record.deps,
--                         seq     |-> record.seq]}
--             /\ committed' = [committed EXCEPT ![i] = @ \cup
--                                {<<record.cmd, record.deps, record.seq>>}]
--             /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \ {i}]
--             /\ UNCHANGED << proposed, executed, crtInst, ballots, preparing >>
action Phase2Finalize (cleader : Replica) (i : Instance Replica (Fin cardCommands))
    (Q : ReplicaSet) {
  require i ∈ leaderOfInst cleader
  require Q ∈ SlowQuorums cleader
  let record : { rec // rec ∈ cmdLog cleader } :|
    record.val.inst = i ∧ record.val.status = .accepted
  let record := record.val
  let replies := msgSet.filter sentMsg (fun msg =>
    msg.inst = i ∧ msg.type = .acceptReply ∧ msg.dst = cleader ∧ msg.src ∈ Q ∧
    msg.ballot = record.ballot)
  require ∀ replica : { r // r ∈ repSet.remove cleader Q },
    ∃ msg : { msg // msg ∈ replies }, msg.val.src = replica.val
  cmdLog cleader := logSet.insert
    { inst := i, status := .committed, ballot := record.ballot, cmd := record.cmd,
      deps := record.deps, seq := record.seq }
    (logSet.remove record (cmdLog cleader))
  sentMsg := msgSet.insert (.commit i record.ballot record.cmd record.deps record.seq)
    (msgSet.diff sentMsg replies)
  committed i := tupleSet.insert { cmd := record.cmd, deps := record.deps, seq := record.seq }
    (committed i)
  leaderOfInst cleader := instSet.remove i (leaderOfInst cleader)
}

-- Commit(replica, cmsg) ==
--     LET oldRec == {rec \in cmdLog[replica] : rec.inst = cmsg.inst} IN
--         /\ \A rec \in oldRec : (rec.status \notin {"committed", "executed"} /\
--                                 rec.ballot[1] <= cmsg.ballot[1])
--         /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ oldRec) \cup
--                                     {[inst     |-> cmsg.inst,
--                                       status   |-> "committed",
--                                       ballot   |-> cmsg.ballot,
--                                       cmd      |-> cmsg.cmd,
--                                       deps     |-> cmsg.deps,
--                                       seq      |-> cmsg.seq]}]
--         /\ committed' = [committed EXCEPT ![cmsg.inst] = @ \cup
--                                {<<cmsg.cmd, cmsg.deps, cmsg.seq>>}]
--         /\ UNCHANGED << proposed, executed, crtInst, leaderOfInst,
--                         sentMsg, ballots, preparing >>
action Commit (replica : Replica) {
  -- `\E cmsg \in sentMsg : (cmsg.type = "commit" /\ Commit(replica, cmsg))`, from `ReplicaAction`.
  let cmsg : { m // m ∈ sentMsg } :| cmsg.val.type = .commit
  let cmsg := cmsg.val
  let oldRec := logSet.filter (cmdLog replica) (fun rec => rec.inst = cmsg.inst)
  require ∀ rec : { rec // rec ∈ oldRec },
    rec.val.status ≠ .committed ∧ rec.val.ballot.num ≤ cmsg.ballot.num
  cmdLog replica := logSet.insert
    { inst := cmsg.inst, status := .committed, ballot := cmsg.ballot, cmd := cmsg.cmd,
      deps := cmsg.deps, seq := cmsg.seq }
    (logSet.diff (cmdLog replica) oldRec)
  committed cmsg.inst := tupleSet.insert { cmd := cmsg.cmd, deps := cmsg.deps, seq := cmsg.seq }
    (committed cmsg.inst)
}

-- (***************************************************************************)
-- (* Recovery actions                                                        *)
-- (***************************************************************************)

-- SendPrepare(replica, i, Q) ==
--     /\ i \notin leaderOfInst[replica]
--     \*/\ i \notin preparing[replica]
--     /\ ballots <= MaxBallot
--     /\ ~(\E rec \in cmdLog[replica] :
--                         /\ rec.inst = i
--                         /\ rec.status \in {"committed", "executed"})
--     /\ sentMsg' = sentMsg \cup
--                     [type   : {"prepare"},
--                      src    : {replica},
--                      dst    : Q,
--                      inst   : {i},
--                      ballot : {<< ballots, replica >>}]
--     /\ ballots' = ballots + 1
--     /\ preparing' = [preparing EXCEPT ![replica] = @ \cup {i}]
--     /\ UNCHANGED << cmdLog, proposed, executed, crtInst,
--                     leaderOfInst, committed >>
action SendPrepare (replica : Replica) (i : Instance Replica (Fin cardCommands)) (Q : ReplicaSet) {
  -- `crtInst[i[1]] > i[2]` and `Q \in SlowQuorums(replica)`, from `ReplicaAction`.
  require crtInst i.leader > i.idx.val + 1
  require Q ∈ SlowQuorums replica
  require i ∉ leaderOfInst replica
  require ballots ≤ MaxBallot
  require ¬ ∃ rec : { rec // rec ∈ cmdLog replica }, rec.val.inst = i ∧ rec.val.status = .committed
  let ballot : Ballot Replica := { num := ballots, owner := replica }
  let prepares : MsgSet := TSet.map Q (fun dst => Msg.prepare replica dst i ballot)
  sentMsg := msgSet.union sentMsg prepares
  ballots := ballots + 1
  preparing replica := instSet.insert i (preparing replica)
}

-- ReplyPrepare(replica) ==
--     \E msg \in sentMsg :
--         /\ msg.type = "prepare"
--         /\ msg.dst = replica
--         /\ \/ \E rec \in cmdLog[replica] :
--                 /\ rec.inst = msg.inst
--                 /\ msg.ballot[1] > rec.ballot[1]
--                 /\ sentMsg' = (sentMsg \ {msg}) \cup
--                             {[type  |-> "prepare-reply",
--                               src   |-> replica,
--                               dst   |-> msg.src,
--                               inst  |-> rec.inst,
--                               ballot|-> msg.ballot,
--                               prev_ballot|-> rec.ballot,
--                               status|-> rec.status,
--                               cmd   |-> rec.cmd,
--                               deps  |-> rec.deps,
--                               seq   |-> rec.seq]}
--                  /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ {rec}) \cup
--                             {[inst  |-> rec.inst,
--                               status|-> rec.status,
--                               ballot|-> msg.ballot,
--                               cmd   |-> rec.cmd,
--                               deps  |-> rec.deps,
--                               seq   |-> rec.seq]}]
--                  /\ IF rec.inst \in leaderOfInst[replica] THEN
--                         /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] =
--                                                                 @ \ {rec.inst}]
--                         /\ UNCHANGED << proposed, executed, committed,
--                                         crtInst, ballots, preparing >>
--                     ELSE UNCHANGED << proposed, executed, committed, crtInst,
--                                       ballots, preparing, leaderOfInst >>
--
--            \/ /\ ~(\E rec \in cmdLog[replica] : rec.inst = msg.inst)
--               /\ sentMsg' = (sentMsg \ {msg}) \cup
--                             {[type  |-> "prepare-reply",
--                               src   |-> replica,
--                               dst   |-> msg.src,
--                               inst  |-> msg.inst,
--                               ballot|-> msg.ballot,
--                               prev_ballot|-> << 0, replica >>,
--                               status|-> "not-seen",
--                               cmd   |-> none,
--                               deps  |-> {},
--                               seq   |-> 0]}
--               /\ cmdLog' = [cmdLog EXCEPT ![replica] = @ \cup
--                             {[inst  |-> msg.inst,
--                               status|-> "not-seen",
--                               ballot|-> msg.ballot,
--                               cmd   |-> none,
--                               deps  |-> {},
--                               seq   |-> 0]}]
--               /\ UNCHANGED << proposed, executed, committed, crtInst, ballots,
--                               leaderOfInst, preparing >>
action ReplyPrepare (replica : Replica) {
  let msg : { m // m ∈ sentMsg } :| msg.val.type = .prepare ∧ msg.val.dst = replica
  let msg := msg.val
  -- The first disjunct needs a record for `msg.inst`, the second needs none.
  if ∃ rec : { rec // rec ∈ cmdLog replica }, rec.val.inst = msg.inst then
    -- The source's `rec`, renamed `record`: `let rec` declares a recursive function in Lean.
    let record : { rec // rec ∈ cmdLog replica } :|
      record.val.inst = msg.inst ∧ msg.ballot.num > record.val.ballot.num
    let record := record.val
    sentMsg := msgSet.insert
      (.prepareReply replica msg.src record.inst msg.ballot record.ballot record.status
        record.cmd record.deps record.seq)
      (msgSet.remove msg sentMsg)
    cmdLog replica := logSet.insert
      { inst := record.inst, status := record.status, ballot := msg.ballot, cmd := record.cmd,
        deps := record.deps, seq := record.seq }
      (logSet.remove record (cmdLog replica))
    if record.inst ∈ leaderOfInst replica then
      leaderOfInst replica := instSet.remove record.inst (leaderOfInst replica)
  else
    sentMsg := msgSet.insert
      (.prepareReply replica msg.src msg.inst msg.ballot { num := 0, owner := replica } .notSeen
        none instSet.empty 0)
      (msgSet.remove msg sentMsg)
    cmdLog replica := logSet.insert
      { inst := msg.inst, status := .notSeen, ballot := msg.ballot, cmd := none,
        deps := instSet.empty, seq := 0 }
      (cmdLog replica)
}

-- PrepareFinalize(replica, i, Q) ==
--     /\ i \in preparing[replica]
--     /\ \E rec \in cmdLog[replica] :
--        /\ rec.inst = i
--        /\ rec.status \notin {"committed", "executed"}
--        /\ LET replies == {msg \in sentMsg :
--                         /\ msg.inst = i
--                         /\ msg.type = "prepare-reply"
--                         /\ msg.dst = replica
--                         /\ msg.ballot = rec.ballot} IN
--             /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
--             /\  \/ \E com \in replies :
--                         /\ (com.status \in {"committed", "executed"})
--                         /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
--                         /\ sentMsg' = sentMsg \ replies
--                         /\ UNCHANGED << cmdLog, proposed, executed, crtInst, leaderOfInst,
--                                         committed, ballots >>
--                 \/ /\ ~(\E msg \in replies : msg.status \in {"committed", "executed"})
--                    /\ \E acc \in replies :
--                         /\ acc.status = "accepted"
--                         /\ (\A msg \in (replies \ {acc}) :
--                             (msg.prev_ballot[1] <= acc.prev_ballot[1] \/
--                              msg.status # "accepted"))
--                         /\ sentMsg' = (sentMsg \ replies) \cup
--                                  [type  : {"accept"},
--                                   src   : {replica},
--                                   dst   : Q \ {replica},
--                                   inst  : {i},
--                                   ballot: {rec.ballot},
--                                   cmd   : {acc.cmd},
--                                   deps  : {acc.deps},
--                                   seq   : {acc.seq}]
--                         /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ {rec}) \cup
--                                 {[inst  |-> i,
--                                   status|-> "accepted",
--                                   ballot|-> rec.ballot,
--                                   cmd   |-> acc.cmd,
--                                   deps  |-> acc.deps,
--                                   seq   |-> acc.seq]}]
--                          /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
--                          /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
--                          /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
--                 \/ /\ ~(\E msg \in replies :
--                         msg.status \in {"accepted", "committed", "executed"})
--                    /\ LET preaccepts == {msg \in replies : msg.status = "pre-accepted"} IN
--                        (\/  /\ \A p1, p2 \in preaccepts :
--                                     p1.cmd = p2.cmd /\ p1.deps = p2.deps /\ p1.seq = p2.seq
--                             /\ ~(\E pl \in preaccepts : pl.src = i[1])
--                             /\ Cardinality(preaccepts) >= Cardinality(Q) - 1
--                             /\ LET pac == CHOOSE pac \in preaccepts : TRUE IN
--                                 /\ sentMsg' = (sentMsg \ replies) \cup
--                                          [type  : {"accept"},
--                                           src   : {replica},
--                                           dst   : Q \ {replica},
--                                           inst  : {i},
--                                           ballot: {rec.ballot},
--                                           cmd   : {pac.cmd},
--                                           deps  : {pac.deps},
--                                           seq   : {pac.seq}]
--                                 /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ {rec}) \cup
--                                         {[inst  |-> i,
--                                           status|-> "accepted",
--                                           ballot|-> rec.ballot,
--                                           cmd   |-> pac.cmd,
--                                           deps  |-> pac.deps,
--                                           seq   |-> pac.seq]}]
--                                  /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
--                                  /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
--                                  /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
--                         \/  /\ \A p1, p2 \in preaccepts : p1.cmd = p2.cmd /\
--                                                           p1.deps = p2.deps /\
--                                                           p1.seq = p2.seq
--                             /\ ~(\E pl \in preaccepts : pl.src = i[1])
--                             /\ Cardinality(preaccepts) < Cardinality(Q) - 1
--                             /\ Cardinality(preaccepts) >= Cardinality(Q) \div 2
--                             /\ LET pac == CHOOSE pac \in preaccepts : TRUE IN
--                                 /\ sentMsg' = (sentMsg \ replies) \cup
--                                          [type  : {"try-pre-accept"},
--                                           src   : {replica},
--                                           dst   : Q,
--                                           inst  : {i},
--                                           ballot: {rec.ballot},
--                                           cmd   : {pac.cmd},
--                                           deps  : {pac.deps},
--                                           seq   : {pac.seq}]
--                                 /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
--                                 /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
--                                 /\ UNCHANGED << cmdLog, proposed, executed,
--                                                 crtInst, committed, ballots >>
--                         \/  /\ \/ \E p1, p2 \in preaccepts : p1.cmd # p2.cmd \/
--                                                              p1.deps # p2.deps \/
--                                                              p1.seq # p2.seq
--                                \/ \E pl \in preaccepts : pl.src = i[1]
--                                \/ Cardinality(preaccepts) < Cardinality(Q) \div 2
--                             /\ preaccepts # {}
--                             /\ LET pac == CHOOSE pac \in preaccepts : pac.cmd # none IN
--                                 /\ StartPhase1(pac.cmd, replica, Q, i, rec.ballot, replies)
--                                 /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
--                                 /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>)
--                 \/  /\ \A msg \in replies : msg.status = "not-seen"
--                     /\ StartPhase1(none, replica, Q, i, rec.ballot, replies)
--                     /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
--                     /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
action PrepareFinalize (replica : Replica) (i : Instance Replica (Fin cardCommands))
    (Q : ReplicaSet) {
  -- `Q \in SlowQuorums(replica)`, from `ReplicaAction`.
  require Q ∈ SlowQuorums replica
  require i ∈ preparing replica
  -- The source's `rec`, renamed `record`: `let rec` declares a recursive function in Lean.
  let record : { rec // rec ∈ cmdLog replica } :|
    record.val.inst = i ∧ record.val.status ≠ .committed
  let record := record.val
  let replies := msgSet.filter sentMsg (fun msg =>
    msg.inst = i ∧ msg.type = .prepareReply ∧ msg.dst = replica ∧ msg.ballot = record.ballot)
  require ∀ rep : { rep // rep ∈ Q }, ∃ msg : { msg // msg ∈ replies }, msg.val.src = rep.val
  -- `branch` picks one of the four disjuncts, and `assume` checks its guard.
  let branch ← pick (Fin 4)
  if branch = 0 then
    assume ∃ com : { com // com ∈ replies }, com.val.status = .committed
    preparing replica := instSet.remove i (preparing replica)
    sentMsg := msgSet.diff sentMsg replies
  else if branch = 1 then
    assume ¬ ∃ msg : { msg // msg ∈ replies }, msg.val.status = .committed
    let acc : { acc // acc ∈ replies } :| acc.val.status = .accepted ∧
      ∀ msg : { msg // msg ∈ msgSet.remove acc.val replies },
        msg.val.prevBallot.num ≤ acc.val.prevBallot.num ∨ msg.val.status ≠ .accepted
    let acc := acc.val
    let accepts : MsgSet := TSet.map (repSet.remove replica Q)
      (fun dst => Msg.accept replica dst i record.ballot acc.cmd acc.deps acc.seq)
    sentMsg := msgSet.union (msgSet.diff sentMsg replies) accepts
    cmdLog replica := logSet.insert
      { inst := i, status := .accepted, ballot := record.ballot, cmd := acc.cmd,
        deps := acc.deps, seq := acc.seq }
      (logSet.remove record (cmdLog replica))
    preparing replica := instSet.remove i (preparing replica)
    leaderOfInst replica := instSet.insert i (leaderOfInst replica)
  else if branch = 2 then
    assume ¬ ∃ msg : { msg // msg ∈ replies },
      msg.val.status = .accepted ∨ msg.val.status = .committed
    let preaccepts := msgSet.filter replies (fun msg => msg.status = .preAccepted)
    -- `sub` picks one of the three inner disjuncts.
    let sub ← pick (Fin 3)
    if sub = 0 then
      assume ∀ p1 p2 : { p // p ∈ preaccepts },
        p1.val.cmd = p2.val.cmd ∧ p1.val.deps = p2.val.deps ∧ p1.val.seq = p2.val.seq
      assume ¬ ∃ pl : { pl // pl ∈ preaccepts }, pl.val.src = i.leader
      assume msgSet.count preaccepts ≥ repSet.count Q - 1
      -- `pac == CHOOSE pac \in preaccepts : TRUE`. Every element of `preaccepts` has the same
      -- `cmd`, `deps` and `seq`, so any choice gives the same step. TLC reports an error if
      -- `preaccepts` is empty.
      assert ¬ msgSet.isEmpty preaccepts
      let pac ← pick { pac // pac ∈ preaccepts }
      let pac := pac.val
      let accepts : MsgSet := TSet.map (repSet.remove replica Q)
        (fun dst => Msg.accept replica dst i record.ballot pac.cmd pac.deps pac.seq)
      sentMsg := msgSet.union (msgSet.diff sentMsg replies) accepts
      cmdLog replica := logSet.insert
        { inst := i, status := .accepted, ballot := record.ballot, cmd := pac.cmd,
          deps := pac.deps, seq := pac.seq }
        (logSet.remove record (cmdLog replica))
      preparing replica := instSet.remove i (preparing replica)
      leaderOfInst replica := instSet.insert i (leaderOfInst replica)
    else if sub = 1 then
      assume ∀ p1 p2 : { p // p ∈ preaccepts },
        p1.val.cmd = p2.val.cmd ∧ p1.val.deps = p2.val.deps ∧ p1.val.seq = p2.val.seq
      assume ¬ ∃ pl : { pl // pl ∈ preaccepts }, pl.val.src = i.leader
      assume msgSet.count preaccepts < repSet.count Q - 1
      assume msgSet.count preaccepts ≥ repSet.count Q / 2
      -- As in the first inner disjunct.
      assert ¬ msgSet.isEmpty preaccepts
      let pac ← pick { pac // pac ∈ preaccepts }
      let pac := pac.val
      let tryPreAccepts : MsgSet := TSet.map Q
        (fun dst => Msg.tryPreAccept replica dst i record.ballot pac.cmd pac.deps pac.seq)
      sentMsg := msgSet.union (msgSet.diff sentMsg replies) tryPreAccepts
      preparing replica := instSet.remove i (preparing replica)
      leaderOfInst replica := instSet.insert i (leaderOfInst replica)
    else
      assume (∃ p1 p2 : { p // p ∈ preaccepts },
          p1.val.cmd ≠ p2.val.cmd ∨ p1.val.deps ≠ p2.val.deps ∨ p1.val.seq ≠ p2.val.seq) ∨
        (∃ pl : { pl // pl ∈ preaccepts }, pl.val.src = i.leader) ∨
        msgSet.count preaccepts < repSet.count Q / 2
      assume ¬ msgSet.isEmpty preaccepts
      -- `pac == CHOOSE pac \in preaccepts : pac.cmd # none`, of which only `pac.cmd` is used.
      -- TLC takes the first such element in its order of values. All elements have the same
      -- `ballot`, and TLC compares records field by field in the order of the field names, so
      -- their first difference is in `cmd`: TLC takes one with the smallest command.
      -- `cmdSet.toList` lists the commands in increasing order.
      let pacCmds : CommandSet := TSet.filterMap preaccepts (·.cmd)
      -- TLC reports an error if no element has a command.
      assert h : cmdSet.toList pacCmds ≠ []
      let pacCmd := (cmdSet.toList pacCmds).head h
      StartPhase1 (some pacCmd) replica Q i record.ballot replies
      preparing replica := instSet.remove i (preparing replica)
  else
    assume ∀ msg : { msg // msg ∈ replies }, msg.val.status = .notSeen
    StartPhase1 none replica Q i record.ballot replies
    preparing replica := instSet.remove i (preparing replica)
}

-- ReplyTryPreaccept(replica) ==
--     \E tpa \in sentMsg :
--         /\ tpa.type = "try-pre-accept"
--         /\ tpa.dst = replica
--         /\ LET oldRec == {rec \in cmdLog[replica] : rec.inst = tpa.inst} IN
--             /\ \A rec \in oldRec : rec.ballot[1] <= tpa.ballot[1] /\
--                                    rec.status \notin {"accepted", "committed", "executed"}
--             /\ \/ (\E rec \in cmdLog[replica] \ oldRec:
--                         /\ tpa.inst \notin rec.deps
--                         /\ \/ rec.inst \notin tpa.deps
--                            \/ rec.seq >= tpa.seq
--                         /\ sentMsg' = (sentMsg \ {tpa}) \cup
--                                     {[type  |-> "try-pre-accept-reply",
--                                       src   |-> replica,
--                                       dst   |-> tpa.src,
--                                       inst  |-> tpa.inst,
--                                       ballot|-> tpa.ballot,
--                                       status|-> rec.status]})
--                         /\ UNCHANGED << cmdLog, proposed, executed, committed, crtInst,
--                                         ballots, leaderOfInst, preparing >>
--                \/ /\ (\A rec \in cmdLog[replica] \ oldRec:
--                             tpa.inst \in rec.deps \/ (rec.inst \in tpa.deps /\
--                                                       rec.seq < tpa.seq))
--                   /\ sentMsg' = (sentMsg \ {tpa}) \cup
--                                     {[type  |-> "try-pre-accept-reply",
--                                       src   |-> replica,
--                                       dst   |-> tpa.src,
--                                       inst  |-> tpa.inst,
--                                       ballot|-> tpa.ballot,
--                                       status|-> "OK"]}
--                   /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ oldRec) \cup
--                                     {[inst  |-> tpa.inst,
--                                       status|-> "pre-accepted",
--                                       ballot|-> tpa.ballot,
--                                       cmd   |-> tpa.cmd,
--                                       deps  |-> tpa.deps,
--                                       seq   |-> tpa.seq]}]
--                   /\ UNCHANGED << proposed, executed, committed, crtInst, ballots,
--                                   leaderOfInst, preparing >>
action ReplyTryPreaccept (replica : Replica) {
  let tpa : { m // m ∈ sentMsg } :| tpa.val.type = .tryPreAccept ∧ tpa.val.dst = replica
  let tpa := tpa.val
  let oldRec := logSet.filter (cmdLog replica) (fun rec => rec.inst = tpa.inst)
  require ∀ rec : { rec // rec ∈ oldRec }, rec.val.ballot.num ≤ tpa.ballot.num ∧
    rec.val.status ≠ .accepted ∧ rec.val.status ≠ .committed
  let others := logSet.diff (cmdLog replica) oldRec
  -- The guard of the second disjunct is the negation of the existential in the first.
  if ∃ rec : { rec // rec ∈ others },
      tpa.inst ∉ rec.val.deps ∧ (rec.val.inst ∉ tpa.deps ∨ rec.val.seq ≥ tpa.seq) then
    -- The source's `rec`, renamed `record`: `let rec` declares a recursive function in Lean.
    let record : { rec // rec ∈ others } :|
      tpa.inst ∉ record.val.deps ∧ (record.val.inst ∉ tpa.deps ∨ record.val.seq ≥ tpa.seq)
    sentMsg := msgSet.insert
      (.tryPreAcceptReply replica tpa.src tpa.inst tpa.ballot (.status record.val.status))
      (msgSet.remove tpa sentMsg)
  else
    sentMsg := msgSet.insert (.tryPreAcceptReply replica tpa.src tpa.inst tpa.ballot .ok)
      (msgSet.remove tpa sentMsg)
    cmdLog replica := logSet.insert
      { inst := tpa.inst, status := .preAccepted, ballot := tpa.ballot, cmd := tpa.cmd,
        deps := tpa.deps, seq := tpa.seq }
      others
}

-- FinalizeTryPreAccept(cleader, i, Q) ==
--     \E rec \in cmdLog[cleader]:
--         /\ rec.inst = i
--         /\ LET tprs == {msg \in sentMsg : msg.type = "try-pre-accept-reply" /\
--                             msg.dst = cleader /\ msg.inst = i /\
--                             msg.ballot = rec.ballot} IN
--             /\ \A r \in Q: \E tpr \in tprs : tpr.src = r
--             /\ \/ /\ \A tpr \in tprs: tpr.status = "OK"
--                   /\ sentMsg' = (sentMsg \ tprs) \cup
--                              [type  : {"accept"},
--                               src   : {cleader},
--                               dst   : Q \ {cleader},
--                               inst  : {i},
--                               ballot: {rec.ballot},
--                               cmd   : {rec.cmd},
--                               deps  : {rec.deps},
--                               seq   : {rec.seq}]
--                   /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ {rec}) \cup
--                             {[inst  |-> i,
--                               status|-> "accepted",
--                               ballot|-> rec.ballot,
--                               cmd   |-> rec.cmd,
--                               deps  |-> rec.deps,
--                               seq   |-> rec.seq]}]
--                   /\ UNCHANGED << proposed, executed, committed, crtInst, ballots,
--                                   leaderOfInst, preparing >>
--                \/ /\ \E tpr \in tprs: tpr.status \in {"accepted", "committed", "executed"}
--                   /\ StartPhase1(rec.cmd, cleader, Q, i, rec.ballot, tprs)
--                   /\ UNCHANGED << proposed, executed, committed, crtInst, ballots,
--                                   leaderOfInst, preparing >>
--                \/ /\ \E tpr \in tprs: tpr.status = "pre-accepted"
--                   /\ \A tpr \in tprs: tpr.status \in {"OK", "pre-accepted"}
--                   /\ sentMsg' = sentMsg \ tprs
--                   /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \ {i}]
--                   /\ UNCHANGED << cmdLog, proposed, executed, committed, crtInst,
--                                   ballots, preparing >>
action FinalizeTryPreAccept (cleader : Replica) (i : Instance Replica (Fin cardCommands))
    (Q : ReplicaSet) {
  -- `i \in leaderOfInst[cleader]` and `Q \in SlowQuorums(cleader)`, from `CommandLeaderAction`.
  require i ∈ leaderOfInst cleader
  require Q ∈ SlowQuorums cleader
  -- The source's `rec`, renamed `record`: `let rec` declares a recursive function in Lean.
  let record : { rec // rec ∈ cmdLog cleader } :| record.val.inst = i
  let record := record.val
  let tprs := msgSet.filter sentMsg (fun msg =>
    msg.type = .tryPreAcceptReply ∧ msg.dst = cleader ∧ msg.inst = i ∧
    msg.ballot = record.ballot)
  require ∀ r : { r // r ∈ Q }, ∃ tpr : { tpr // tpr ∈ tprs }, tpr.val.src = r.val
  -- `branch` picks one of the three disjuncts, and `assume` checks its guard.
  let branch ← pick (Fin 3)
  if branch = 0 then
    assume ∀ tpr : { tpr // tpr ∈ tprs }, tpr.val.replyStatus = .ok
    let accepts : MsgSet := TSet.map (repSet.remove cleader Q)
      (fun dst => Msg.accept cleader dst i record.ballot record.cmd record.deps record.seq)
    sentMsg := msgSet.union (msgSet.diff sentMsg tprs) accepts
    cmdLog cleader := logSet.insert
      { inst := i, status := .accepted, ballot := record.ballot, cmd := record.cmd,
        deps := record.deps, seq := record.seq }
      (logSet.remove record (cmdLog cleader))
  else if branch = 1 then
    assume ∃ tpr : { tpr // tpr ∈ tprs },
      tpr.val.replyStatus = .status .accepted ∨ tpr.val.replyStatus = .status .committed
    -- `StartPhase1` adds `i` to `leaderOfInst[cleader]`, which already contains it, so this
    -- agrees with `UNCHANGED leaderOfInst`.
    StartPhase1 record.cmd cleader Q i record.ballot tprs
  else
    assume ∃ tpr : { tpr // tpr ∈ tprs }, tpr.val.replyStatus = .status .preAccepted
    assume ∀ tpr : { tpr // tpr ∈ tprs },
      tpr.val.replyStatus = .ok ∨ tpr.val.replyStatus = .status .preAccepted
    sentMsg := msgSet.diff sentMsg tprs
    leaderOfInst cleader := instSet.remove i (leaderOfInst cleader)
}

-- (***************************************************************************)
-- (* Action groups                                                           *)
-- (***************************************************************************)

-- CommandLeaderAction ==
--     \/ (\E C \in (Commands \ proposed) :
--             \E cleader \in Replicas : Propose(C, cleader))
--     \/ (\E cleader \in Replicas : \E inst \in leaderOfInst[cleader] :
--             \/ (\E Q \in FastQuorums(cleader) : Phase1Fast(cleader, inst, Q))
--             \/ (\E Q \in SlowQuorums(cleader) : Phase1Slow(cleader, inst, Q))
--             \/ (\E Q \in SlowQuorums(cleader) : Phase2Finalize(cleader, inst, Q))
--             \/ (\E Q \in SlowQuorums(cleader) : FinalizeTryPreAccept(cleader, inst, Q)))

-- ReplicaAction ==
--     \E replica \in Replicas :
--         (\/ Phase1Reply(replica)
--          \/ Phase2Reply(replica)
--          \/ \E cmsg \in sentMsg : (cmsg.type = "commit" /\ Commit(replica, cmsg))
--          \/ \E i \in Instances :
--             /\ crtInst[i[1]] > i[2] (* This condition states that the instance has *)
--                                     (* been started by its original owner          *)
--             /\ \E Q \in SlowQuorums(replica) : SendPrepare(replica, i, Q)
--          \/ ReplyPrepare(replica)
--          \/ \E i \in preparing[replica] :
--             \E Q \in SlowQuorums(replica) : PrepareFinalize(replica, i, Q)
--          \/ ReplyTryPreaccept(replica))

-- Next ==
--     \/ CommandLeaderAction
--     \/ ReplicaAction

-- Spec == Init /\ [][Next]_vars

-- Each disjunct of `CommandLeaderAction` and `ReplicaAction` is the action of the same name
-- above. The quantifiers around it are its parameters, or a choice at its start for the
-- quantifiers over messages (`Commit`); the conditions on them are its first `require`s.

-- (***************************************************************************)
-- (* Theorems                                                                *)
-- (***************************************************************************)

-- Nontriviality ==
--     \A i \in Instances :
--         [](\A C \in committed[i] : C \in proposed \/ C = none)
-- `C` ranges over the tuples <<cmd, deps, seq>> in committed[i]. A tuple is neither in `proposed`
-- nor equal to `none`, so the formula as written says that nothing is ever committed, and TLC
-- reports its violation at the first commit. This invariant checks the command of each tuple
-- instead, as the TLC model's `NontrivialityCmdInv` does.
invariant [Nontriviality] ∀ i : Instance Replica (Fin cardCommands), ∀ C : { C // C ∈ committed i },
  (∃ c : { c // c ∈ proposed }, C.val.cmd = some c.val) ∨ C.val.cmd = none

-- The formula as written, which says that `committed[i]` stays empty. Uncomment it to reproduce
-- TLC's violation with `Nontriviality.cfg`: `#model_check` reports it after the same three steps
-- as TLC (`Propose`, `Phase1Reply`, `Phase1Fast`). Set `veil.violationIsError` to `false` to keep
-- the file building.
-- invariant [NontrivialityAsWritten]
--   ∀ i : Instance Replica (Fin cardCommands), tupleSet.isEmpty (committed i)

-- Stability ==
--     \A replica \in Replicas :
--         \A i \in Instances :
--             \A C \in Commands :
--                 []((\E rec1 \in cmdLog[replica] :
--                     /\ rec1.inst = i
--                     /\ rec1.cmd = C
--                     /\ rec1.status \in {"committed", "executed"}) =>
--                     [](\E rec2 \in cmdLog[replica] :
--                         /\ rec2.inst = i
--                         /\ rec2.cmd = C
--                         /\ rec2.status \in {"committed", "executed"}))
temporal (only := check) [Stability]
  ∀ replica : Replica, ∀ i : Instance Replica (Fin cardCommands), ∀ C : Command,
    □ (⌜ ∃ rec1 : { r // r ∈ cmdLog replica },
          rec1.val.inst = i ∧ rec1.val.cmd = some C ∧ rec1.val.status = .committed ⌝ →
      □ ⌜ ∃ rec2 : { r // r ∈ cmdLog replica },
          rec2.val.inst = i ∧ rec2.val.cmd = some C ∧ rec2.val.status = .committed ⌝)

-- Consistency ==
--     \A i \in Instances :
--         [](Cardinality(committed[i]) <= 1)
safety [Consistency] ∀ i : Instance Replica (Fin cardCommands), tupleSet.count (committed i) ≤ 1

-- THEOREM Spec => ([]TypeOK) /\ Nontriviality /\ Stability /\ Consistency
-- Lean's types ensure `TypeOK`.

#gen_spec
#gen_executable

-- =============================================================================
-- \* Modification History
-- \* Last modified Sat Aug 24 12:25:28 EDT 2013 by iulian
-- \* Created Tue Apr 30 11:49:57 EDT 2013 by iulian

-- `MCFastQuorums` and `MCSlowQuorums` of the TLC model, for replicas `0..n-1`: the quorums of `r`
-- are the sets of `size` replicas that contain `r`.
def quorumsContaining (n size : Nat) (r : Fin n) : OrdList (OrdList (Fin n)) :=
  OrdList.ofList ((TSet.subsets (OrdList.ofList (List.finRange n))).filter fun q =>
    TSet.contains r q && TSet.count q == size)

-- TLC checks this spec with the cfg files in `Benchmarks/TLA/EPaxos/`, on
-- `MCEgalitarianPaxos.tla`. The check below uses the instance of `R2C1B1.cfg`.
-- All checks of this file are commented out, so that building it does not run them; uncomment one
-- to run it. Lean then runs it when it elaborates this file. In VS Code, the result appears in the
-- InfoView while the cursor is on `#model_check`. From the project root,
-- `lake env lean Examples/TLA/EPaxos.lean` prints it.
-- It finds no violation, in as many distinct states as TLC (115).
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s:
-- * `Command := Fin 1`: one command, `0` (cfg: `Commands <- C1`, where `C1 == {c1}`).
-- * `Replica := Fin 2`: the replicas are `0` and `1` (cfg: `Replicas <- R2`, where
--   `R2 == {r1, r2}`).
-- * `cardCommands := 1`: TLA+'s `Cardinality(Commands)`. The `assumption [card_commands]` above
--   checks it against `Commands`.
-- * `CommandSet := OrdList _` and the other set types: `OrdList` has the `TSet` instances that the
--   `instantiate` lines above require.
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields:
-- * `Commands` and `Replicas`: the sets of all commands and all replicas. The assumptions
--   `commands_complete` and `replicas_complete` check that they contain every command and every
--   replica.
-- * `FastQuorums := quorumsContaining 2 2`, `SlowQuorums := quorumsContaining 2 2`: the quorums of
--   each replica are the sets of 2 replicas that contain it, here only `{0, 1}`
--   (cfg: `FastQuorums <- MCFastQuorums`, `SlowQuorums <- MCSlowQuorums`).
-- * `MaxBallot := 1` (cfg: `MaxBallot = 1`).
-- Before searching, `#model_check` checks these values against the `assumption`s above. Two of them
-- translate the spec's quorum `ASSUME`s.
--
-- The other settings of the cfg:
-- * `r1 = r1`, `c1 = c1`, ...: model values for the replicas and commands. Here they are the
--   values of `Fin 2` and `Fin 1`.
-- * `none = none`: a model value for the spec's `none`. Here command fields have type
--   `Option Command`, where `none` stands for it.
-- * `INVARIANT ConsistencyInv`: the `safety [Consistency]` above.
-- * `INVARIANT NontrivialityCmdInv`: the `invariant [Nontriviality]` above.
-- * `PROPERTY Stability`: the temporal property `[Stability]` above, which the `#temporal_check`
--   below checks.
-- * `CHECK_DEADLOCK FALSE`: this module has no `termination` clause, so Veil reports no deadlocks
--   either.
-- Options:
-- * `interpreted` runs the search only in Lean's interpreter, without compiling a checker.
-- #model_check interpreted
--   { Command := Fin 1, Replica := Fin 2, cardCommands := 1,
--     CommandSet := OrdList _, ReplicaSet := OrdList _, QuorumSet := OrdList _,
--     InstanceSet := OrdList _, LogSet := OrdList _, CommitTupleSet := OrdList _,
--     MsgSet := OrdList _ }
--   { Commands := OrdList.ofList (List.finRange 1), Replicas := OrdList.ofList (List.finRange 2),
--     FastQuorums := quorumsContaining 2 2, SlowQuorums := quorumsContaining 2 2,
--     MaxBallot := 1 }

-- `#temporal_check` checks the temporal property `[Stability]` (cfg: `PROPERTY Stability`) on the
-- same instance. It finds no violation; TLC finds none either. `Stability` is a safety property,
-- so the stuttering steps of `[][Next]_vars`, which `#temporal_check` does not add, do not
-- change its result.
-- Options:
-- * `interpreted` runs the search only in Lean's interpreter, without compiling a checker.
-- #temporal_check [Stability] interpreted
--   { Command := Fin 1, Replica := Fin 2, cardCommands := 1,
--     CommandSet := OrdList _, ReplicaSet := OrdList _, QuorumSet := OrdList _,
--     InstanceSet := OrdList _, LogSet := OrdList _, CommitTupleSet := OrdList _,
--     MsgSet := OrdList _ }
--   { Commands := OrdList.ofList (List.finRange 1), Replicas := OrdList.ofList (List.finRange 2),
--     FastQuorums := quorumsContaining 2 2, SlowQuorums := quorumsContaining 2 2,
--     MaxBallot := 1 }

-- The checks below, commented out, use the instances of the other cfg files; uncomment them to
-- run them. They take longer. Each finds no violation, in as many distinct states as TLC:
-- * `R2C1B2.cfg`, with `MaxBallot = 2`: 1,135 states.
-- * `R3C1B1.cfg`, with 3 replicas: 2,302 states. The quorums are the sets of 2 replicas.
-- * `R2C2B1.cfg`, with 2 commands: 12,385 states.
-- * `R4C1B1.cfg`, with 4 replicas: 45,509 states. The quorums are the sets of 3 replicas.
-- The last check runs `#temporal_check` on the instance of `R3C1B1.cfg`; it finds no violation.
-- Together these instances take every action and every disjunct of the spec, except three that
-- need try-pre-accept messages and two commands: the first disjunct of `ReplyTryPreaccept`, and
-- the second and third of `FinalizeTryPreAccept`. The smallest such instance has 4 replicas and
-- 2 commands, which TLC did not finish exploring in a few minutes.
-- Options:
-- * The checks name no mode, so their search starts in Lean's interpreter and moves to a compiled
--   checker once that is built.

-- #model_check
--   { Command := Fin 1, Replica := Fin 2, cardCommands := 1,
--     CommandSet := OrdList _, ReplicaSet := OrdList _, QuorumSet := OrdList _,
--     InstanceSet := OrdList _, LogSet := OrdList _, CommitTupleSet := OrdList _,
--     MsgSet := OrdList _ }
--   { Commands := OrdList.ofList (List.finRange 1), Replicas := OrdList.ofList (List.finRange 2),
--     FastQuorums := quorumsContaining 2 2, SlowQuorums := quorumsContaining 2 2,
--     MaxBallot := 2 }

-- #model_check
--   { Command := Fin 1, Replica := Fin 3, cardCommands := 1,
--     CommandSet := OrdList _, ReplicaSet := OrdList _, QuorumSet := OrdList _,
--     InstanceSet := OrdList _, LogSet := OrdList _, CommitTupleSet := OrdList _,
--     MsgSet := OrdList _ }
--   { Commands := OrdList.ofList (List.finRange 1), Replicas := OrdList.ofList (List.finRange 3),
--     FastQuorums := quorumsContaining 3 2, SlowQuorums := quorumsContaining 3 2,
--     MaxBallot := 1 }

-- #model_check
--   { Command := Fin 2, Replica := Fin 2, cardCommands := 2,
--     CommandSet := OrdList _, ReplicaSet := OrdList _, QuorumSet := OrdList _,
--     InstanceSet := OrdList _, LogSet := OrdList _, CommitTupleSet := OrdList _,
--     MsgSet := OrdList _ }
--   { Commands := OrdList.ofList (List.finRange 2), Replicas := OrdList.ofList (List.finRange 2),
--     FastQuorums := quorumsContaining 2 2, SlowQuorums := quorumsContaining 2 2,
--     MaxBallot := 1 }

-- #model_check
--   { Command := Fin 1, Replica := Fin 4, cardCommands := 1,
--     CommandSet := OrdList _, ReplicaSet := OrdList _, QuorumSet := OrdList _,
--     InstanceSet := OrdList _, LogSet := OrdList _, CommitTupleSet := OrdList _,
--     MsgSet := OrdList _ }
--   { Commands := OrdList.ofList (List.finRange 1), Replicas := OrdList.ofList (List.finRange 4),
--     FastQuorums := quorumsContaining 4 3, SlowQuorums := quorumsContaining 4 3,
--     MaxBallot := 1 }

-- #temporal_check [Stability]
--   { Command := Fin 1, Replica := Fin 3, cardCommands := 1,
--     CommandSet := OrdList _, ReplicaSet := OrdList _, QuorumSet := OrdList _,
--     InstanceSet := OrdList _, LogSet := OrdList _, CommitTupleSet := OrdList _,
--     MsgSet := OrdList _ }
--   { Commands := OrdList.ofList (List.finRange 1), Replicas := OrdList.ofList (List.finRange 3),
--     FastQuorums := quorumsContaining 3 2, SlowQuorums := quorumsContaining 3 2,
--     MaxBallot := 1 }

end EPaxos
