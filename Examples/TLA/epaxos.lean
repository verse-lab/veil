import veil

-- -------------------------- MODULE EgalitarianPaxos --------------------------

-- EXTENDS Naturals, FiniteSets

-- -----------------------------------------------------------------------------

-- Max(S) == IF S = {} THEN 0 ELSE CHOOSE i \in S : \A j \in S : j <= i


-- (*********************************************************************************)
-- (* Constant parameters:                                                          *)
-- (*       Commands: the set of all possible commands                              *)
-- (*       Replicas: the set of all EPaxos replicas                                *)
-- (*       FastQuorums(r): the set of all fast quorums where r is a command leader *)
-- (*       SlowQuorums(r): the set of all slow quorums where r is a command leader *)
-- (*********************************************************************************)

-- CONSTANTS Commands, Replicas, FastQuorums(_), SlowQuorums(_), MaxBallot

-- ASSUME IsFiniteSet(Replicas)

-- (***************************************************************************)
-- (* Quorum conditions:                                                      *)
-- (*  (simplified)                                                           *)
-- (***************************************************************************)

-- ASSUME \A r \in Replicas:
--   /\ SlowQuorums(r) \subseteq SUBSET Replicas
--   /\ \A SQ \in SlowQuorums(r):
--     /\ r \in SQ
--     /\ Cardinality(SQ) = (Cardinality(Replicas) \div 2) + 1

-- ASSUME \A r \in Replicas:
--   /\ FastQuorums(r) \subseteq SUBSET Replicas
--   /\ \A FQ \in FastQuorums(r):
--     /\ r \in FQ
--     /\ Cardinality(FQ) = (Cardinality(Replicas) \div 2) +
--                          ((Cardinality(Replicas) \div 2) + 1) \div 2


-- (***************************************************************************)
-- (* Special none command                                                    *)
-- (***************************************************************************)

-- none == CHOOSE c : c \notin Commands


-- (***************************************************************************)
-- (* The instance space                                                      *)
-- (***************************************************************************)

-- Instances == Replicas \X (1..Cardinality(Commands))

-- (***************************************************************************)
-- (* The possible status of a command in the log of a replica.               *)
-- (***************************************************************************)

-- Status == {"not-seen", "pre-accepted", "accepted", "committed"}

veil module EPaxos

-- Type declarations
type command
type replica
type seqNum      -- sequence number for instances (second component of instance)
type ballot_num  -- ballot number (first component of ballot)

-- Instance is a pair (replica, seqNum)
@[veil_decl]
structure Instance (r s : Type) where
  leader : r
  idx : s
deriving instance Veil.Enumeration for Instance

-- Ballot is a pair (ballot_num, replica)
@[veil_decl]
structure Ballot (n r : Type) where
  num : n
  owner : r
deriving instance Veil.Enumeration for Ballot

-- Status enumeration
enum Status = { NotSeen, PreAccepted, Accepted, Committed }

-- (***************************************************************************)
-- (* All possible protocol messages:                                         *)
-- (***************************************************************************)

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
inductive MsgType where
  | PreAccept
  | Accept
  | Commit
  | Prepare
  | PreAcceptReply
  | AcceptReply
  | PrepareReply
  | TryPreAccept
  | TryPreAcceptReply
deriving instance Veil.Enumeration for MsgType

-- Extended status for try-pre-accept-reply (includes "OK")
@[veil_decl]
inductive ExtStatus where
  | NotSeen
  | PreAccepted
  | Accepted
  | Committed
  | OK
deriving instance Veil.Enumeration for ExtStatus

-- Container types
type InstanceSet
type CommandSet
type ReplicaSet
type SeqNumSet

-- Log entry record
@[veil_decl]
structure LogEntry (inst cmd dps blt seq : Type) where
  inst : inst
  status : ExtStatus
  ballot : blt
  cmd : cmd
  deps : dps
  seq : seq
deriving instance Veil.Enumeration for LogEntry

type LogEntrySet

-- Committed tuple: (command, deps, seq)
@[veil_decl]
structure CommittedTuple (cmd deps seq : Type) where
  cmd : cmd
  deps : deps
  seq : seq
deriving instance Veil.Enumeration for CommittedTuple

type CommittedTupleSet

-- Message structure
@[veil_decl]
structure Msg (rep inst blt cmd dps seq stat : Type) where
  msgType : MsgType
  src : rep
  dst : rep
  inst : inst
  ballot : blt
  prevBallot : blt      -- for prepare-reply
  cmd : cmd
  deps : dps
  seq : seq
  committed : dps      -- for pre-accept-reply (committed instances)
  extStatus : stat      -- for try-pre-accept-reply and prepare-reply
deriving instance Veil.Enumeration for Msg

type MsgSet

-- Order relations for seqNum and ballot_num
instantiate seqOrd : TotalOrderWithZero seqNum
instantiate ballotOrd : TotalOrderWithZero ballot_num

-- Set instantiations
instantiate instSet : TSet (Instance replica seqNum) InstanceSet
instantiate cmdSet : TSet command CommandSet
instantiate repSet : TSet replica ReplicaSet
instantiate seqSet : TSet seqNum SeqNumSet
instantiate logSet : TSet (LogEntry (Instance replica seqNum) command InstanceSet (Ballot ballot_num replica) seqNum) LogEntrySet
instantiate commitSet : TSet (CommittedTuple command InstanceSet seqNum) CommittedTupleSet
instantiate msgTSet : TSet (Msg replica (Instance replica seqNum) (Ballot ballot_num replica) command InstanceSet seqNum ExtStatus) MsgSet

-- Immutable constants
immutable individual none : command
immutable individual maxBallot : ballot_num
immutable individual one : ballot_num
immutable individual oneSeq : seqNum

-- Quorum membership relations
immutable relation fastQuorumMember (r : replica) (q : replica) (leader : replica)  -- q is in FastQuorum of leader, r is the replica
immutable relation slowQuorumMember (r : replica) (q : replica) (leader : replica)  -- q is in SlowQuorum of leader, r is the replica

-- Simplified: we use relations to indicate quorum membership
immutable relation inFastQuorum (q : replica) (leader : replica)
immutable relation inSlowQuorum (q : replica) (leader : replica)

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

-- TypeOK ==
--     /\ cmdLog \in [Replicas -> SUBSET [inst: Instances,
--                                        status: Status,
--                                        ballot: Nat \X Replicas,
--                                        cmd: Commands \cup {none},
--                                        deps: SUBSET Instances,
--                                        seq: Nat]]
--     /\ proposed \in SUBSET Commands
--     /\ executed \in [Replicas -> SUBSET (Nat \X Commands)]
--     /\ sentMsg \in SUBSET Message
--     /\ crtInst \in [Replicas -> Nat]
--     /\ leaderOfInst \in [Replicas -> SUBSET Instances]
--     /\ committed \in [Instances -> SUBSET ((Commands \cup {none}) \X
--                                            (SUBSET Instances) \X
--                                            Nat)]
--     /\ ballots \in Nat
--     /\ preparing \in [Replicas -> SUBSET Instances]

-- vars == << cmdLog, proposed, executed, sentMsg, crtInst, leaderOfInst,
--            committed, ballots, preparing >>

-- State variables
function cmdLog (r : replica) : LogEntrySet
individual proposed : CommandSet
individual sentMsg : MsgSet
function crtInst (r : replica) : seqNum
function leaderOfInst (r : replica) : InstanceSet
function committedMap (i : Instance replica seqNum) : CommittedTupleSet
individual ballots : ballot_num
function preparing (r : replica) : InstanceSet

#gen_state

-- Ghost relations for ordering
theory ghost relation ltBallot (x y : ballot_num) := (ballotOrd.le x y ∧ x ≠ y)
theory ghost relation leBallot (x y : ballot_num) := ballotOrd.le x y
theory ghost relation gtBallot (x y : ballot_num) := (ballotOrd.le y x ∧ x ≠ y)
theory ghost relation geBallot (x y : ballot_num) := ballotOrd.le y x

theory ghost relation ltSeq (x y : seqNum) := (seqOrd.le x y ∧ x ≠ y)
theory ghost relation leSeq (x y : seqNum) := seqOrd.le x y
theory ghost relation gtSeq (x y : seqNum) := (seqOrd.le y x ∧ x ≠ y)
theory ghost relation geSeq (x y : seqNum) := seqOrd.le y x

-- Successor relations
theory ghost relation nextBallot (x y : ballot_num) := (ltBallot x y ∧ ∀ z, ltBallot x z → ballotOrd.le y z)
theory ghost relation nextSeq (x y : seqNum) := (ltSeq x y ∧ ∀ z, ltSeq x z → seqOrd.le y z)

-- Assumptions
assumption [zero_one_ballot] nextBallot ballotOrd.zero one
assumption [zero_one_seq] nextSeq seqOrd.zero oneSeq

-- Quorum assumptions: every two quorums intersect
assumption [fast_quorum_intersect]
  ∀ (leader : replica) (r1 r2 : replica),
    inFastQuorum r1 leader → inFastQuorum r2 leader →
    ∃ (r : replica), inFastQuorum r leader

assumption [slow_quorum_intersect]
  ∀ (leader : replica) (r1 r2 : replica),
    inSlowQuorum r1 leader → inSlowQuorum r2 leader →
    ∃ (r : replica), inSlowQuorum r leader

-- Leader is in its own quorums
assumption [leader_in_fast_quorum]
  ∀ (leader : replica), inFastQuorum leader leader

assumption [leader_in_slow_quorum]
  ∀ (leader : replica), inSlowQuorum leader leader

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
  sentMsg := msgTSet.empty
  cmdLog R := logSet.empty
  proposed := cmdSet.empty
  crtInst R := oneSeq
  leaderOfInst R := instSet.empty
  committedMap I := commitSet.empty
  ballots := one
  preparing R := instSet.empty
}

-- Helper: Max of sequence numbers in a set
procedure maxSeqInLog (entries : LogEntrySet) {
  let seqs := logSet.toList entries |>.map (fun e => e.seq)
  let result := seqs.foldl (fun acc s => if seqOrd.le acc s then s else acc) seqOrd.zero
  return result
}

-- Helper: Get all instances from log entries
procedure depsFromLog (entries : LogEntrySet) {
  let insts := logSet.toList entries |>.map (fun e => e.inst)
  let result := insts.foldl (fun acc i => instSet.insert i acc) instSet.empty
  return result
}

-- Helper: Get old records for an instance
procedure getOldRecs (entries : LogEntrySet) (inst : Instance replica seqNum) {
  let oldRecs := logSet.filter entries (fun rec => rec.inst = inst)
  return oldRecs
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

procedure succSeq (s : seqNum) {
  let k :| nextSeq s k
  return k
}

procedure succBallot (b : ballot_num) {
  let k :| nextBallot b k
  return k
}

-- Simplified StartPhase1: updates cmdLog, leaderOfInst, and sends pre-accept messages
action StartPhase1 (C : command) (cleader : replica) (inst : Instance replica seqNum)
                   (ballot : Ballot ballot_num replica) (oldMsgToRemove : MsgSet) {
  let newDeps ← depsFromLog (cmdLog cleader)
  let maxS ← maxSeqInLog (cmdLog cleader)
  let newSeq ← succSeq maxS
  let oldRecs ← getOldRecs (cmdLog cleader) inst

  -- Update cmdLog: remove old records and add new one
  let logWithoutOld := logSet.toList oldRecs |>.foldl (fun acc rec => logSet.remove rec acc) (cmdLog cleader)
  let newEntry : LogEntry (Instance replica seqNum) command InstanceSet (Ballot ballot_num replica) seqNum := {
    inst := inst,
    status := .PreAccepted,
    ballot := ballot,
    cmd := C,
    deps := newDeps,
    seq := newSeq
  }
  cmdLog cleader := logSet.insert newEntry logWithoutOld

  -- Update leaderOfInst
  leaderOfInst cleader := instSet.insert inst (leaderOfInst cleader)

  -- Send pre-accept messages to all replicas in quorum except leader
  -- (simplified: we send to all replicas and the receiver will check)
  let dstReplica ← pick replica
  require dstReplica ≠ cleader
  require inFastQuorum dstReplica cleader

  let preAcceptMsg : Msg replica (Instance replica seqNum) (Ballot ballot_num replica) command InstanceSet seqNum ExtStatus := {
    msgType := MsgType.PreAccept,
    src := cleader,
    dst := dstReplica,
    inst := inst,
    ballot := ballot,
    prevBallot := default,
    cmd := C,
    deps := newDeps,
    seq := newSeq,
    committed := instSet.empty,
    extStatus := default
  }

  -- Remove old messages and add new ones
  let msgWithoutOld := msgTSet.toList oldMsgToRemove |>.foldl (fun acc m => msgTSet.remove m acc) sentMsg
  sentMsg := msgTSet.insert preAcceptMsg msgWithoutOld
}

-- Propose(C, cleader) ==
--     LET newInst == <<cleader, crtInst[cleader]>>
--         newBallot == <<0, cleader>>
--     IN  /\ proposed' = proposed \cup {C}
--         /\ (\E Q \in FastQuorums(cleader):
--                  StartPhase1(C, cleader, Q, newInst, newBallot, {}))
--         /\ crtInst' = [crtInst EXCEPT ![cleader] = @ + 1]
--         /\ UNCHANGED << executed, committed, ballots, preparing >>

action Propose (C : command) (cleader : replica) {
  require ¬ cmdSet.contains C proposed
  let newInst : Instance replica seqNum := { leader := cleader, idx := crtInst cleader }
  let newBallot : Ballot ballot_num replica := { num := ballotOrd.zero, owner := cleader }

  proposed := cmdSet.insert C proposed

  -- Increment crtInst
  let nextIdx ← succSeq (crtInst cleader)
  crtInst cleader := nextIdx

  -- Call StartPhase1
  StartPhase1 C cleader newInst newBallot msgTSet.empty
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

action Phase1Reply (rep : replica) {
  let msg :| msgTSet.contains msg sentMsg ∧ msg.msgType = MsgType.PreAccept ∧ msg.dst = rep

  let oldRecs ← getOldRecs (cmdLog rep) msg.inst

  -- Check ballot condition: all old records have ballot <= msg.ballot
  -- require logSet.toList oldRecs |>.all (fun rec =>
  --   rec.ballot = msg.ballot ∨ ltBallot rec.ballot.num msg.ballot.num)

  -- Compute newDeps: msg.deps ∪ (instances in cmdLog \ {msg.inst})
  let localDeps ← depsFromLog (cmdLog rep)
  let localDepsWithoutMsgInst := instSet.remove msg.inst localDeps
  let newDeps := instSet.toList localDepsWithoutMsgInst |>.foldl
    (fun acc i => instSet.insert i acc) msg.deps

  -- Compute newSeq: max(msg.seq, 1 + max(log seqs))
  let maxLocalSeq ← maxSeqInLog (cmdLog rep)
  let succMaxLocal ← succSeq maxLocalSeq
  let newSeq := if seqOrd.le msg.seq succMaxLocal then succMaxLocal else msg.seq

  -- Compute instCom: instances with committed status
  let committedEntries := logSet.filter (cmdLog rep) (fun rec => rec.status = .Committed)
  let instCom ← depsFromLog committedEntries

  -- Update cmdLog
  let logWithoutOld := logSet.toList oldRecs |>.foldl (fun acc rec => logSet.remove rec acc) (cmdLog rep)
  let newEntry : LogEntry (Instance replica seqNum) command InstanceSet (Ballot ballot_num replica) seqNum := {
    inst := msg.inst,
    status := .PreAccepted,
    ballot := msg.ballot,
    cmd := msg.cmd,
    deps := newDeps,
    seq := newSeq
  }
  cmdLog rep := logSet.insert newEntry logWithoutOld

  -- Update sentMsg: remove msg, add reply
  let replyMsg : Msg replica (Instance replica seqNum) (Ballot ballot_num replica) command InstanceSet seqNum ExtStatus := {
    msgType := MsgType.PreAcceptReply,
    src := rep,
    dst := msg.src,
    inst := msg.inst,
    ballot := msg.ballot,
    prevBallot := default,
    cmd := default,
    deps := newDeps,
    seq := newSeq,
    committed := instCom,
    extStatus := default
  }
  sentMsg := msgTSet.insert replyMsg (msgTSet.remove msg sentMsg)
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

action Phase1Fast (cleader : replica) (i : Instance replica seqNum) {
  require instSet.contains i (leaderOfInst cleader)

  -- Find record in cmdLog
  let record :| logSet.contains record (cmdLog cleader) ∧
                record.inst = i ∧
                record.status = .PreAccepted ∧
                record.ballot.num = ballotOrd.zero

  -- Get all pre-accept replies for this instance
  let replies := msgTSet.filter sentMsg (fun msg =>
    msg.inst = i ∧
    msg.msgType = MsgType.PreAcceptReply ∧
    msg.dst = cleader ∧
    inFastQuorum msg.src cleader ∧
    msg.ballot = record.ballot)

  -- All replicas in fast quorum (except leader) have replied
  -- require ∀ rep, inFastQuorum rep cleader → rep ≠ cleader →
  --   msgTSet.toList replies |>.any (fun msg => msg.src = rep)

  -- All replies have same deps and seq
  let replyList := msgTSet.toList replies
  require replyList.all (fun r1 => replyList.all (fun r2 => r1.deps = r2.deps ∧ r1.seq = r2.seq))

  -- Pick a reply
  let r :| msgTSet.contains r replies

  -- Check deps subset condition (simplified)
  let committedEntries := logSet.filter (cmdLog cleader) (fun rec => rec.status = .Committed)
  let localCom ← depsFromLog committedEntries

  -- Update cmdLog
  let logWithoutRecord := logSet.remove record (cmdLog cleader)
  let newEntry : LogEntry (Instance replica seqNum) command InstanceSet (Ballot ballot_num replica) seqNum := {
    inst := i,
    status := .Committed,
    ballot := record.ballot,
    cmd := record.cmd,
    deps := r.deps,
    seq := r.seq
  }
  cmdLog cleader := logSet.insert newEntry logWithoutRecord

  -- Update sentMsg: remove replies, add commit
  let msgWithoutReplies := msgTSet.toList replies |>.foldl (fun acc m => msgTSet.remove m acc) sentMsg
  let commitMsg : Msg replica (Instance replica seqNum) (Ballot ballot_num replica) command InstanceSet seqNum ExtStatus := {
    msgType := MsgType.Commit,
    src := cleader,
    dst := default,
    inst := i,
    ballot := record.ballot,
    prevBallot := default,
    cmd := record.cmd,
    deps := r.deps,
    seq := r.seq,
    committed := instSet.empty,
    extStatus := default
  }
  sentMsg := msgTSet.insert commitMsg msgWithoutReplies

  -- Update leaderOfInst
  leaderOfInst cleader := instSet.remove i (leaderOfInst cleader)

  -- Update committed map
  let commitTuple : CommittedTuple command InstanceSet seqNum := {
    cmd := record.cmd,
    deps := r.deps,
    seq := r.seq
  }
  committedMap i := commitSet.insert commitTuple (committedMap i)
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

action Phase1Slow (cleader : replica) (i : Instance replica seqNum) {
  require instSet.contains i (leaderOfInst cleader)

  -- Find record in cmdLog
  let record :| logSet.contains record (cmdLog cleader) ∧
                record.inst = i ∧
                record.status = .PreAccepted

  -- Get all pre-accept replies for this instance from slow quorum
  let replies := msgTSet.filter sentMsg (fun msg =>
    msg.inst = i ∧
    msg.msgType = .PreAcceptReply ∧
    msg.dst = cleader ∧
    inSlowQuorum msg.src cleader ∧
    msg.ballot = record.ballot)

  -- All replicas in slow quorum (except leader) have replied
  -- require ∀ rep, inSlowQuorum rep cleader → rep ≠ cleader →
  --   msgTSet.toList replies |>.any (fun msg => msg.src = rep)

  -- Compute finalDeps: union of all deps
  let replyList := msgTSet.toList replies
  let finalDeps := replyList.foldl (fun acc r =>
    instSet.toList r.deps |>.foldl (fun acc2 i => instSet.insert i acc2) acc
  ) instSet.empty

  -- Compute finalSeq: max of all seqs
  let finalSeq := replyList.foldl (fun acc r =>
    if seqOrd.le acc r.seq then r.seq else acc
  ) seqOrd.zero

  -- Update cmdLog
  let logWithoutRecord := logSet.remove record (cmdLog cleader)
  let newEntry : LogEntry (Instance replica seqNum) command InstanceSet (Ballot ballot_num replica) seqNum := {
    inst := i,
    status := .Accepted,
    ballot := record.ballot,
    cmd := record.cmd,
    deps := finalDeps,
    seq := finalSeq
  }
  cmdLog cleader := logSet.insert newEntry logWithoutRecord

  -- Send accept messages
  let dstReplica ← pick replica
  require dstReplica ≠ cleader
  require inSlowQuorum dstReplica cleader

  let acceptMsg : Msg replica (Instance replica seqNum) (Ballot ballot_num replica) command InstanceSet seqNum ExtStatus := {
    msgType := MsgType.Accept,
    src := cleader,
    dst := dstReplica,
    inst := i,
    ballot := record.ballot,
    prevBallot := default,
    cmd := record.cmd,
    deps := finalDeps,
    seq := finalSeq,
    committed := instSet.empty,
    extStatus := default
  }
  let msgWithoutReplies := msgTSet.toList replies |>.foldl (fun acc m => msgTSet.remove m acc) sentMsg
  sentMsg := msgTSet.insert acceptMsg msgWithoutReplies
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

-- action Phase2Reply (rep : replica) {
--   let msg :| msgTSet.contains msg sentMsg ∧ msg.msgType = MsgType.Accept ∧ msg.dst = rep
--   let oldRecs ← getOldRecs (cmdLog rep) msg.inst

--   -- Check ballot condition
--   require logSet.toList oldRecs |>.all (fun rec =>
--     rec.ballot = (msg.ballot ∨ ltBallot rec.ballot.num msg.ballot.num))

--   -- Update cmdLog
--   let logWithoutOld := logSet.toList oldRecs |>.foldl (fun acc rec => logSet.remove rec acc) (cmdLog rep)
--   let newEntry : LogEntry (Instance replica seqNum) command InstanceSet (Ballot ballot_num replica) seqNum := {
--     inst := msg.inst,
--     status := Status.Accepted,
--     ballot := msg.ballot,
--     cmd := msg.cmd,
--     deps := msg.deps,
--     seq := msg.seq
--   }
--   cmdLog rep := logSet.insert newEntry logWithoutOld

--   -- Update sentMsg
--   let replyMsg : Msg replica (Instance replica seqNum) (Ballot ballot_num replica) command InstanceSet seqNum ExtStatus := {
--     msgType := MsgType.AcceptReply,
--     src := rep,
--     dst := msg.src,
--     inst := msg.inst,
--     ballot := msg.ballot,
--     prevBallot := default,
--     cmd := default,
--     deps := instSet.empty,
--     seq := default,
--     committed := instSet.empty,
--     extStatus := default
--   }
--   sentMsg := msgTSet.insert replyMsg (msgTSet.remove msg sentMsg)
-- }


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

action Phase2Finalize (cleader : replica) (i : Instance replica seqNum) {
  require instSet.contains i (leaderOfInst cleader)

  -- Find record in cmdLog
  let record :| logSet.contains record (cmdLog cleader) ∧
                record.inst = i ∧
                record.status = .Accepted

  -- Get all accept replies
  let replies := msgTSet.filter sentMsg (fun msg =>
    msg.inst = i ∧
    msg.msgType = MsgType.AcceptReply ∧
    msg.dst = cleader ∧
    inSlowQuorum msg.src cleader ∧
    msg.ballot = record.ballot)

  -- All replicas in slow quorum (except leader) have replied
  -- require ∀ rep, inSlowQuorum rep cleader → rep ≠ cleader →
  --   msgTSet.toList replies |>.any (fun msg => msg.src = rep)

  -- Update cmdLog
  let logWithoutRecord := logSet.remove record (cmdLog cleader)
  let newEntry : LogEntry (Instance replica seqNum) command InstanceSet (Ballot ballot_num replica) seqNum := {
    inst := i,
    status := .Committed,
    ballot := record.ballot,
    cmd := record.cmd,
    deps := record.deps,
    seq := record.seq
  }
  cmdLog cleader := logSet.insert newEntry logWithoutRecord

  -- Update sentMsg
  let msgWithoutReplies := msgTSet.toList replies |>.foldl (fun acc m => msgTSet.remove m acc) sentMsg
  let commitMsg : Msg replica (Instance replica seqNum) (Ballot ballot_num replica) command InstanceSet seqNum ExtStatus := {
    msgType := MsgType.Commit,
    src := cleader,
    dst := default,
    inst := i,
    ballot := record.ballot,
    prevBallot := default,
    cmd := record.cmd,
    deps := record.deps,
    seq := record.seq,
    committed := instSet.empty,
    extStatus := default
  }
  sentMsg := msgTSet.insert commitMsg msgWithoutReplies

  -- Update leaderOfInst
  leaderOfInst cleader := instSet.remove i (leaderOfInst cleader)

  -- Update committed map
  let commitTuple : CommittedTuple command InstanceSet seqNum := {
    cmd := record.cmd,
    deps := record.deps,
    seq := record.seq
  }
  committedMap i := commitSet.insert commitTuple (committedMap i)
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

action Commit (rep : replica) {
  let cmsg :| msgTSet.contains cmsg sentMsg ∧ cmsg.msgType = MsgType.Commit

  let oldRecs ← getOldRecs (cmdLog rep) cmsg.inst

  -- Check conditions on old records
  -- require logSet.toList oldRecs |>.all (fun rec =>
  --   rec.status ≠ .Committed ∧ leBallot rec.ballot.num cmsg.ballot.num)

  -- Update cmdLog
  let logWithoutOld := logSet.toList oldRecs |>.foldl (fun acc rec => logSet.remove rec acc) (cmdLog rep)
  let newEntry : LogEntry (Instance replica seqNum) command InstanceSet (Ballot ballot_num replica) seqNum := {
    inst := cmsg.inst,
    status := .Committed,
    ballot := cmsg.ballot,
    cmd := cmsg.cmd,
    deps := cmsg.deps,
    seq := cmsg.seq
  }
  cmdLog rep := logSet.insert newEntry logWithoutOld

  -- Update committed map
  let commitTuple : CommittedTuple command InstanceSet seqNum := {
    cmd := cmsg.cmd,
    deps := cmsg.deps,
    seq := cmsg.seq
  }
  committedMap cmsg.inst := commitSet.insert commitTuple (committedMap cmsg.inst)
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

action SendPrepare (rep : replica) (i : Instance replica seqNum) {
  require ¬ instSet.contains i (leaderOfInst rep)
  require leBallot ballots maxBallot

  -- Check no committed record for this instance
  -- require ¬ (logSet.toList (cmdLog rep) |>.any (fun rec =>
  --   rec.inst = i ∧ rec.status = Status.Committed))

  -- Send prepare messages
  let dstReplica ← pick replica
  require inSlowQuorum dstReplica rep

  let prepareMsg : Msg replica (Instance replica seqNum) (Ballot ballot_num replica) command InstanceSet seqNum ExtStatus := {
    msgType := MsgType.Prepare,
    src := rep,
    dst := dstReplica,
    inst := i,
    ballot := { num := ballots, owner := rep },
    prevBallot := default,
    cmd := default,
    deps := instSet.empty,
    seq := default,
    committed := instSet.empty,
    extStatus := default
  }
  sentMsg := msgTSet.insert prepareMsg sentMsg

  -- Increment ballots
  let nextBal ← succBallot ballots
  ballots := nextBal

  -- Add to preparing
  preparing rep := instSet.insert i (preparing rep)
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

-- Helper to convert Status to ExtStatus
-- procedure statusToExtStatus (s : Status) {
--   if s == .NotSeen then
--     return .NotSeen
--   else if s == .PreAccepted then
--     return .PreAccepted
--   else if s == .Accepted then
--     return .Accepted
--   else
--     return .Committed
-- }

action ReplyPrepareWithRecord (rep : replica) {
  let msg :| msgTSet.contains msg sentMsg ∧ msg.msgType = MsgType.Prepare ∧ msg.dst = rep

  -- Case 1: There is an existing record with lower ballot
  let rec :| logSet.contains rec (cmdLog rep) ∧
             rec.inst = msg.inst ∧
             gtBallot msg.ballot.num rec.ballot.num

  -- let extStat ← statusToExtStatus rec.status

  let replyMsg : Msg replica (Instance replica seqNum) (Ballot ballot_num replica) command InstanceSet seqNum ExtStatus := {
    msgType := MsgType.PrepareReply,
    src := rep,
    dst := msg.src,
    inst := rec.inst,
    ballot := msg.ballot,
    prevBallot := rec.ballot,
    cmd := rec.cmd,
    deps := rec.deps,
    seq := rec.seq,
    committed := instSet.empty,
    /- extStatus := extStat -/
    extStatus := default -- TODO
  }
  sentMsg := msgTSet.insert replyMsg (msgTSet.remove msg sentMsg)

  -- Update cmdLog with new ballot
  let logWithoutRec := logSet.remove rec (cmdLog rep)
  let newEntry : LogEntry (Instance replica seqNum) command InstanceSet (Ballot ballot_num replica) seqNum := {
    inst := rec.inst,
    status := rec.status,
    ballot := msg.ballot,
    cmd := rec.cmd,
    deps := rec.deps,
    seq := rec.seq
  }
  cmdLog rep := logSet.insert newEntry logWithoutRec

  -- Remove from leaderOfInst if present
  if instSet.contains rec.inst (leaderOfInst rep) then
    leaderOfInst rep := instSet.remove rec.inst (leaderOfInst rep)
}

action ReplyPrepareNoRecord (rep : replica) {
  let msg :| msgTSet.contains msg sentMsg ∧ msg.msgType = MsgType.Prepare ∧ msg.dst = rep

  -- Case 2: No existing record for this instance
  require ¬ (logSet.toList (cmdLog rep) |>.any (fun rec => rec.inst = msg.inst))

  let replyMsg : Msg replica (Instance replica seqNum) (Ballot ballot_num replica) command InstanceSet seqNum ExtStatus := {
    msgType := MsgType.PrepareReply,
    src := rep,
    dst := msg.src,
    inst := msg.inst,
    ballot := msg.ballot,
    prevBallot := { num := ballotOrd.zero, owner := rep },
    cmd := none,
    deps := instSet.empty,
    seq := seqOrd.zero,
    committed := instSet.empty,
    extStatus := .NotSeen
  }
  sentMsg := msgTSet.insert replyMsg (msgTSet.remove msg sentMsg)

  -- Add not-seen entry to cmdLog
  let newEntry : LogEntry (Instance replica seqNum) command InstanceSet (Ballot ballot_num replica) seqNum := {
    inst := msg.inst,
    status := .NotSeen,
    ballot := msg.ballot,
    cmd := none,
    deps := instSet.empty,
    seq := seqOrd.zero
  }
  cmdLog rep := logSet.insert newEntry (cmdLog rep)
}


-- Note: PrepareFinalize, ReplyTryPreaccept, and FinalizeTryPreAccept are complex
-- recovery actions. Here we provide simplified versions.

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

action ReplyTryPreacceptOK (rep : replica) {
  let tpa :| msgTSet.contains tpa sentMsg ∧ tpa.msgType = .TryPreAccept ∧ tpa.dst = rep

  let oldRecs ← getOldRecs (cmdLog rep) tpa.inst

  -- Check ballot and status conditions
  -- require logSet.toList oldRecs |>.all (fun rec =>
  --   leBallot rec.ballot.num tpa.ballot.num ∧
  --   rec.status ≠ Status.Accepted ∧ rec.status ≠ Status.Committed)

  -- Check compatibility with other records
  let otherRecs := logSet.filter (cmdLog rep) (fun rec => rec.inst ≠ tpa.inst)

  -- require logSet.toList otherRecs |>.all (fun rec =>
  --   instSet.contains tpa.inst rec.deps ∨
  --   (instSet.contains rec.inst tpa.deps ∧ ltSeq rec.seq tpa.seq))

  -- Send OK reply
  let replyMsg : Msg replica (Instance replica seqNum) (Ballot ballot_num replica) command InstanceSet seqNum ExtStatus := {
    msgType := MsgType.TryPreAcceptReply,
    src := rep,
    dst := tpa.src,
    inst := tpa.inst,
    ballot := tpa.ballot,
    prevBallot := default,
    cmd := default,
    deps := instSet.empty,
    seq := default,
    committed := instSet.empty,
    extStatus := .OK
  }
  sentMsg := msgTSet.insert replyMsg (msgTSet.remove tpa sentMsg)

  -- Update cmdLog
  let logWithoutOld := logSet.toList oldRecs |>.foldl (fun acc rec => logSet.remove rec acc) (cmdLog rep)
  let newEntry : LogEntry (Instance replica seqNum) command InstanceSet (Ballot ballot_num replica) seqNum := {
    inst := tpa.inst,
    status := .PreAccepted,
    ballot := tpa.ballot,
    cmd := tpa.cmd,
    deps := tpa.deps,
    seq := tpa.seq
  }
  cmdLog rep := logSet.insert newEntry logWithoutOld
}

action ReplyTryPreacceptConflict (rep : replica) {
  let tpa :| msgTSet.contains tpa sentMsg ∧ tpa.msgType = MsgType.TryPreAccept ∧ tpa.dst = rep

  let oldRecs ← getOldRecs (cmdLog rep) tpa.inst

  -- Check ballot and status conditions
  -- require logSet.toList oldRecs |>.all (fun rec =>
  --   leBallot rec.ballot.num tpa.ballot.num ∧
  --   rec.status ≠ .Accepted ∧ rec.status ≠ .Committed)

  -- Find a conflicting record
  let conflictRec :| logSet.contains conflictRec (cmdLog rep) ∧
                     conflictRec.inst ≠ tpa.inst ∧
                     ¬ instSet.contains tpa.inst conflictRec.deps ∧
                     (¬ instSet.contains conflictRec.inst tpa.deps ∨ geSeq conflictRec.seq tpa.seq)

  -- let extStat ← statusToExtStatus conflictRec.status

  -- Send conflict reply with the status
  let replyMsg : Msg replica (Instance replica seqNum) (Ballot ballot_num replica) command InstanceSet seqNum ExtStatus := {
    msgType := MsgType.TryPreAcceptReply,
    src := rep,
    dst := tpa.src,
    inst := tpa.inst,
    ballot := tpa.ballot,
    prevBallot := default,
    cmd := default,
    deps := instSet.empty,
    seq := default,
    committed := instSet.empty,
    -- extStatus := extStat
    extStatus := default -- TODO
  }
  sentMsg := msgTSet.insert replyMsg (msgTSet.remove tpa sentMsg)
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


-- (***************************************************************************)
-- (* Next action                                                             *)
-- (***************************************************************************)

-- Next ==
--     \/ CommandLeaderAction
--     \/ ReplicaAction


-- (***************************************************************************)
-- (* The complete definition of the algorithm                                *)
-- (***************************************************************************)

-- Spec == Init /\ [][Next]_vars


-- (***************************************************************************)
-- (* Theorems                                                                *)
-- (***************************************************************************)

-- Nontriviality ==
--     \A i \in Instances :
--         [](\A C \in committed[i] : C \in proposed \/ C = none)

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

-- Consistency ==
--     \A i \in Instances :
--         [](Cardinality(committed[i]) <= 1)

-- THEOREM Spec => ([]TypeOK) /\ Nontriviality /\ Stability /\ Consistency

-- Invariants

-- Consistency: At most one value can be committed for each instance
invariant [Consistency]
  ∀ i : Instance replica seqNum, commitSet.count (committedMap i) <= 1

-- Nontriviality: Committed commands are either proposed or none
ghost relation isProposedOrNone (c : command) :=
  cmdSet.contains c proposed ∨ c = none

invariant [Nontriviality]
  ∀ i : Instance replica seqNum,
    commitSet.toList (committedMap i) |>.all (fun ct => isProposedOrNone ct.cmd)
#exit
#gen_spec

-- =============================================================================
-- \* Modification History
-- \* Last modified Sat Aug 24 12:25:28 EDT 2013 by iulian
-- \* Created Tue Apr 30 11:49:57 EDT 2013 by iulian

-- Model checking configuration
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2000

#model_check
{
  command := Fin 1,
  replica := Fin 2,
  seqNum := Fin 2,
  ballot_num := Fin 2,
  InstanceSet := Std.ExtTreeSet (Instance (Fin 2) (Fin 2)) compare,
  CommandSet := Std.ExtTreeSet (Fin 1) compare,
  ReplicaSet := Std.ExtTreeSet (Fin 2) compare,
  SeqNumSet := Std.ExtTreeSet (Fin 2) compare,
  LogEntrySet := Std.ExtTreeSet (LogEntry (Instance (Fin 2) (Fin 2)) (Fin 1) (Std.ExtTreeSet (Instance (Fin 2) (Fin 2)) compare) (Ballot (Fin 2) (Fin 2)) (Fin 2)) compare,
  CommittedTupleSet := Std.ExtTreeSet (CommittedTuple (Fin 1) (Std.ExtTreeSet (Instance (Fin 2) (Fin 2)) compare) (Fin 2)) compare,
  MsgSet := Std.ExtTreeSet (Msg (Fin 2) (Instance (Fin 2) (Fin 2)) (Ballot (Fin 2) (Fin 2)) (Fin 1) (Std.ExtTreeSet (Instance (Fin 2) (Fin 2)) compare) (Fin 2) ExtStatus) compare
}
{
  none := 0,
  maxBallot := 1,
  one := 1,
  oneSeq := 1,
  inFastQuorum := fun q leader => true,
  inSlowQuorum := fun q leader => true
}

end EPaxos
