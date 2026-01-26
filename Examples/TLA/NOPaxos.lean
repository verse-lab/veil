import Veil
veil module NOPaxosTLA
-- ------------------------------ MODULE NOPaxos ----------------------------------
-- (*

--   Specifies the NOPaxos protocol.

-- *)


-- EXTENDS Naturals, FiniteSets, Sequences

-- --------------------------------------------------------------------------------
-- (* `^\textbf{\large Constants}^' *)

-- \* The set of replicas and an ordering of them
-- CONSTANTS Replicas, ReplicaOrder
-- ASSUME IsFiniteSet(Replicas) /\ ReplicaOrder \in Seq(Replicas)

-- \* Message sequencers
-- CONSTANT NumSequencers \* Normally infinite, assumed finite for model checking
-- Sequencers == (1..NumSequencers)

-- \* Set of possible values in a client request and a special null value
-- CONSTANTS Values, NoOp
type replica
type replicaSet

instantiate rSet : TSet replica replicaSet

enum value = {a, b, c, d, e, NoOp}

-- instantiate ballotOrd : TotalOrderWithZero ballot_num
-- instantiate ballotOrdLeDec : DecidableRel (ballotOrd.le)
-- \* Replica Statuses
-- CONSTANTS StNormal, StViewChange, StGapCommit
enum ReplicaStatus = {StNormal, StViewChange, StGapCommit}

-- \* Message Types
-- CONSTANTS MClientRequest,       \* Sent by client to sequencer
--           MMarkedClientRequest, \* Sent by sequencer to replicas
--           MRequestReply,        \* Sent by replicas to client
--           MSlotLookup,          \* Sent by followes to get the value of a slot
--           MSlotLookupRep,       \* Sent by the leader with a value/NoOp
--           MGapCommit,           \* Sent by the leader to commit a gap
--           MGapCommitRep,        \* Sent by the followers to ACK a gap commit
--           MViewChangeReq,       \* Sent when leader/sequencer failure detected
--           MViewChange,          \* Sent to ACK view change
--           MStartView,           \* Sent by new leader to start view
--           MSyncPrepare,         \* Sent by the leader to ensure log durability
--           MSyncRep,             \* Sent by followers as ACK
--           MSyncCommit           \* Sent by leaders to indicate stable log
@[veil_decl]
inductive MsgType where
  | MClientRequest
  | MMarkedClientRequest
  | MRequestReply
  | MSlotLookup
  | MSlotLookupRep
  | MGapCommit
  | MGapCommitRep
  | MViewChangeReq
  | MViewChange
  | MStartView
  | MSyncPrepare
  | MSyncRep
  | MSyncCommit
deriving instance Veil.Enumeration for MsgType
-- (*
--   `^\textbf{Message Schemas}^'

-- ViewIDs == [ leaderNum |-> n \in (1..), sessNum |-> n \in (1..) ]
@[veil_decl]
structure View (seq: Type) where
  leaderNum : Nat
  sessNum   : seq
deriving instance Nonempty for View
--   ClientRequest
--       [ mtype |-> MClientRequest,
--         value |-> v \in Values ]

--   MarkedClientRequest
--       [ mtype      |-> MMarkedClientRequest,
--         dest       |-> r \in Replicas,
--         value      |-> v \in Values,
--         sessNum    |-> s \in Sequencers,
--         sessMsgNum |-> n \in (1..) ]

--   RequestReply
--       [ mtype      |-> MRequestReply,
--         sender     |-> r \in Replicas,
--         viewID     |-> v \in ViewIDs,
--         request    |-> v \in Values \cup {NoOp},
--         logSlotNum |-> n \in (1..) ]

--   SlotLookup
--       [ mtype      |-> MSlotLookup,
--         dest       |-> r \in Replicas,
--         sender     |-> r \in Replicas,
--         viewID     |-> v \in ViewIDs,
--         sessMsgNum |-> n \in (1..) ]

--   GapCommit
--       [ mtype      |-> MGapCommit,
--         dest       |-> r \in Replicas,
--         viewID     |-> v \in ViewIDs,
--         slotNumber |-> n \in (1..) ]

--   GapCommitRep
--       [ mtype      |-> MGapCommitRep,
--         dest       |-> r \in Replicas,
--         sender     |-> r \in Replicas,
--         viewID     |-> v \in ViewIDs,
--         slotNumber |-> n \in (1..) ]

--   ViewChangeReq
--       [ mtype  |-> MViewChangeReq,
--         dest   |-> r \in Replicas,
--         viewID |-> v \in ViewIDs ]

--   ViewChange
--       [ mtype      |-> MViewChange,
--         dest       |-> r \in Replicas,
--         sender     |-> r \in Replicas,
--         viewID     |-> v \in ViewIDs,
--         lastNormal |-> v \in ViewIDs,
--         sessMsgNum |-> n \in (1..),
--         log        |-> l \in (1..) \times (Values \cup {NoOp}) ]

--   StartView
--       [ mtype      |-> MStartView,
--         dest       |-> r \in Replicas,
--         viewID     |-> v \in ViewIDs,
--         log        |-> l \in (1..) \times (Values \cup {NoOp}),
--         sessMsgNum |-> n \in (1..) ]

--   SyncPrepare
--       [ mtype      |-> MSyncPrepare,
--         dest       |-> r \in Replicas,
--         sender     |-> r \in Replicas,
--         viewID     |-> v \in ViewIDs,
--         sessMsgNum |-> n \in (1..),
--         log        |-> l \in (1..) \times (Values \cup {NoOp}) ]

--   SyncRep
--       [ mtype         |-> MSyncRep,
--         dest          |-> r \in Replicas,
--         sender        |-> r \in Replicas,
--         viewID        |-> v \in ViewIDs,
--         logSlotNumber |-> n \in (1..) ]

--   SyncCommit
--       [ mtype         |-> MSyncCommit,
--         dest          |-> r \in Replicas,
--         sender        |-> r \in Replicas,
--         viewID        |-> v \in ViewIDs,
--         log           |-> l \in (1..) \times (Values \cup {NoOp}),
--         sessMsgNum    |-> n \in (1..) ]

-- *)
@[veil_decl]
structure Message (rep val seq: Type) where
  mtype         : MsgType
  dest          : rep
  sender        : rep
  value         : val
  viewID        : View seq
  request       : val
  logSlotNum    : Nat
  sessNum       : seq
  sessMsgNum    : Nat
  slotNumber    : Nat
  lastNormal    : View seq
  log           : List val
deriving instance Nonempty for Message

-- --------------------------------------------------------------------------------
-- (* `^\textbf{\large Variables}^' *)

-- \* `^\textbf{Network State}^'
-- VARIABLE messages \* Set of all messages sent

-- networkVars      == << messages >>
-- InitNetworkState == messages = {}

-- \* `^\textbf{Sequencer State}^'
-- VARIABLE seqMsgNums

-- sequencerVars      == << seqMsgNums >>
-- InitSequencerState == seqMsgNums = [ s \in Sequencers |-> 1 ]
type sequencer
instantiate seqOrd : TotalOrderWithZero sequencer
instantiate seqOrdLeDec : DecidableRel (seqOrd.le)
-- \* `^\textbf{Replica State}^'
-- VARIABLES vLog,            \* Log of values and gaps
--           vSessMsgNum,     \* The number of messages received in the OUM session
--           vReplicaStatus,  \* One of StNormal, StViewChange, and StGapCommit
--           vViewID,         \* Current viewID replicas recognize
--           vLastNormView,   \* Last views in which replicas had status StNormal
--           vViewChanges,    \* Used for logging view change votes
--           vCurrentGapSlot, \* Used for gap commit at leader
--           vGapCommitReps,  \* Used for logging gap commit reps at leader
--           vSyncPoint,      \* Synchronization point for replicas
--           vTentativeSync,  \* Used by leader to mark current syncing point
--           vSyncReps        \* Used for logging sync reps at leader
type setMsg
instantiate mSet: TSet (Message replica value sequencer) setMsg

function vLog            : replica → List value
function vSessMsgNum     : replica → Nat
function vReplicaStatus  : replica → ReplicaStatus
function vViewID         : replica → View sequencer
function vLastNormView   : replica → View sequencer
function vViewChanges    : replica → setMsg
function vCurrentGapSlot : replica → Nat
function vGapCommitReps  : replica → setMsg
function vSyncPoint      : replica → Nat
function vTentativeSync  : replica → Nat
function vSyncReps       : replica → setMsg
function seqMsgNums      : sequencer → Nat

individual messages : setMsg


immutable individual one  : sequencer
immutable individual SIZE : Nat
immutable individual MsgCountLimit : Nat
immutable individual Replicas      : List replica
immutable individual ReplicaOrder  : List replica

#gen_state

theory ghost relation gtSequencer (x y : sequencer) := (seqOrd.le y x ∧ x ≠ y)

-- replicaVars      == << vLog, vViewID, vSessMsgNum, vLastNormView, vViewChanges,
--                        vGapCommitReps, vCurrentGapSlot, vReplicaStatus,
--                        vSyncPoint, vTentativeSync, vSyncReps >>
-- InitReplicaState ==
--   /\ vLog            = [ r \in Replicas |-> << >> ]
--   /\ vViewID         = [ r \in Replicas |->
--                            [ sessNum |-> 1, leaderNum |-> 1 ] ]
--   /\ vLastNormView   = [ r \in Replicas |->
--                            [ sessNum |-> 1, leaderNum |-> 1 ] ]
--   /\ vSessMsgNum     = [ r \in Replicas |-> 1 ]
--   /\ vViewChanges    = [ r \in Replicas |-> {} ]
--   /\ vGapCommitReps  = [ r \in Replicas |-> {} ]
--   /\ vCurrentGapSlot = [ r \in Replicas |-> 0 ]
--   /\ vReplicaStatus  = [ r \in Replicas |-> StNormal ]
--   /\ vSyncPoint      = [ r \in Replicas |-> 0 ]
--   /\ vTentativeSync  = [ r \in Replicas |-> 0 ]
--   /\ vSyncReps       = [ r \in Replicas |-> {} ]
-- \* `^\textbf{Set of all vars}^'
-- vars == << networkVars, sequencerVars, replicaVars >>

-- \* `^\textbf{Initial state}^'
-- Init == /\ InitNetworkState
--         /\ InitSequencerState
--         /\ InitReplicaState
after_init {
  /- InitReplicaState -/
  vLog R := []
  vViewID R := { sessNum := one, leaderNum := 1 }
  vLastNormView R := { sessNum := one, leaderNum := 1 }
  vSessMsgNum R := 1
  vViewChanges R := mSet.empty
  vGapCommitReps R := mSet.empty
  vCurrentGapSlot R := 0
  vReplicaStatus R := StNormal
  vSyncPoint R := 0
  vTentativeSync R := 0
  vSyncReps R := mSet.empty
  /- InitNetworkState -/
  messages := mSet.empty
  /- InitSequencerState -/
  seqMsgNums S := 1
}
-- --------------------------------------------------------------------------------
-- (* `^\textbf{\large Helpers}^' *)

-- Max(s) == CHOOSE x \in s : \A y \in s : x >= y


-- \* `^\textbf{View ID Helpers}^'
-- Leader(viewID) == ReplicaOrder[(viewID.leaderNum % Len(ReplicaOrder)) +
--                                (IF viewID.leaderNum >= Len(ReplicaOrder)
--                                 THEN 1 ELSE 0)]
procedure Leader (v : View sequencer) {
  -- Assume that `.leaderNum ≥ 1`
  /- Be cafeful about the difference between `0-based` and `1-based` here -/
  let idx := (v.leaderNum % List.length ReplicaOrder) +
             (if v.leaderNum ≥ List.length ReplicaOrder then 1 else 0)
  return ReplicaOrder[idx-1]!
}

-- ViewLe(v1, v2) == /\ v1.sessNum    <= v2.sessNum
--                   /\ v1.leaderNum <= v2.leaderNum
-- ViewLt(v1, v2) == ViewLe(v1, v2) /\ v1 /= v2
ghost relation ViewLe (v1 v2 : View sequencer) :=
  seqOrd.le v1.sessNum v2.sessNum ∧ v1.leaderNum ≤ v2.leaderNum
ghost relation ViewLt (v1 v2 : View sequencer) :=
  ViewLe v1 v2 ∧ (v1 ≠ v2)


-- \* `^\textbf{Network Helpers}^'
-- \* Add a message to the network
-- Send(ms) == messages' = messages \cup ms
procedure Send (ms : setMsg) {
  messages := mSet.union messages ms
}

-- \* `^\textbf{Log Manipulation Helpers}^'
-- (* Combine logs, taking a NoOp for any slot that has a NoOp and a Value
--    otherwise. *)
-- CombineLogs(ls) ==
--   LET
--     combineSlot(xs) == IF NoOp \in xs THEN
--                          NoOp
--                        ELSE IF xs = {} THEN
--                          NoOp
--                        ELSE
--                          CHOOSE x \in xs : x /= NoOp
--     range == Max({ Len(l) : l \in ls})
--   IN
--     [i \in (1..range) |->
--        combineSlot({l[i] : l \in { k \in ls : i <= Len(k) }})]
procedure CombineLogs (ls : List (List value)) {
  let maxLen := ls.foldl (fun acc l => Nat.max acc l.length) 0
  let oneIndexRange := (List.range maxLen).map (· + 1)
  let result := oneIndexRange.map (fun i =>
    let valuesAtSlot := ls.filterMap (fun l =>
      if i ≤ l.length then some (l.getD (i - 1) NoOp) else none)
    if valuesAtSlot.contains NoOp then
      NoOp
    else if valuesAtSlot.isEmpty then
      NoOp
    else
      /- CHOOSE x \in xs : x /= NoOp
      Since NoOp is not in valuesAtSlot, any element is a valid non-NoOp value -/
      valuesAtSlot.getD 0 NoOp)
  return result
}

-- \* Insert x into log l at position i (`which should be <= Len(l) + 1`)
-- ReplaceItem(l, i, x) ==
--   [ j \in 1..Max({Len(l), i}) |-> IF j = i THEN x ELSE l[j] ]
def ReplaceItem {α : Type} (l : List α) (i : Nat) (x : α) : List α :=
  let maxRange := Nat.max (List.length l) i
  let oneIndexRange := (List.range maxRange).map (· + 1)
  let result := oneIndexRange.map (fun j =>
    if j == i then x
    else if j ≤ l.length then l.getD (j - 1) x  -- Adjust for 0-based index
    else x)
  result


-- \* Subroutine to send an MGapCommit message
-- SendGapCommit(r) ==
--   LET
--     slot == Len(vLog[r]) + 1
--   IN
--   /\ Leader(vViewID[r]) = r
--   /\ vReplicaStatus[r]  = StNormal
--   /\ vReplicaStatus'    = [ vReplicaStatus EXCEPT ![r] = StGapCommit ]
--   /\ vGapCommitReps'    = [ vGapCommitReps   EXCEPT ![r] = {} ]
--   /\ vCurrentGapSlot'   = [ vCurrentGapSlot EXCEPT ![r] = slot ]
--   /\ Send({[ mtype      |-> MGapCommit,
--              dest       |-> d,
--              slotNumber |-> slot,
--              viewID     |-> vViewID[r] ] : d \in Replicas})
--   /\ UNCHANGED << sequencerVars, vLog, vViewID, vSessMsgNum,
--                   vLastNormView, vViewChanges, vSyncPoint,
--                   vTentativeSync, vSyncReps >>
-- ✅
procedure SendGapCommit (r : replica) {
  let slot := List.length (vLog r) + 1
  require (←Leader (vViewID r)) == r
  require vReplicaStatus r == StNormal
  vReplicaStatus r := StGapCommit
  vGapCommitReps r := mSet.empty
  vCurrentGapSlot r := slot
  let msgs : List (Message replica value sequencer) := Replicas.map (fun d =>
    { mtype      := MsgType.MGapCommit,
      dest       := d,
      slotNumber := slot,
      viewID     := vViewID r,
      sender     := default,
      value      := default,
      request    := default,
      logSlotNum := default,
      sessNum    := default,
      sessMsgNum := default,
      lastNormal := default,
      log        := [] } )
  let msgSendSet := msgs.foldl (fun acc m => TSet.insert m acc) mSet.empty
  Send msgSendSet
}
-- --------------------------------------------------------------------------------
-- (* `^\textbf{\large Main Spec}^' *)

-- Quorums == {R \in SUBSET(Replicas) : Cardinality(R) * 2 > Cardinality(Replicas)}
ghost relation isQuorum (R : replicaSet) :=
  rSet.count R * 2 > SIZE

-- (*
--   A request is committed if a quorum sent replies with matching view-id and
--   log-slot-num, where one of the replies is from the leader. The following
--   predicate is true iff value v is committed in slot i.

--   `~TODO: add temporal formula stating Committed implies always Committed
--     (this is obvious, though, because nothing gets taken out of messages).~'
-- *)
-- Committed(v, i) ==
--   \E M \in SUBSET ({m \in messages : /\ m.mtype = MRequestReply
--                                      /\ m.logSlotNum = i
--                                      /\ m.request = v }) :
--     \* Sent from a quorum
--     /\ { m.sender : m \in M } \in Quorums
--     \* Matching view-id
--     /\ \E m1 \in M : \A m2 \in M : m1.viewID = m2.viewID
--     \* One from the leader
--     /\ \E m \in M : m.sender = Leader(m.viewID)
ghost relation Committed (v : value) (i : Nat) :=
  -- Find all messages matching the criteria
  let M := mSet.filter messages (fun m =>
    m.mtype == .MRequestReply &&
    m.logSlotNum == i &&
    m.request == v)
  let Mlist := mSet.toList M
  let Msenders : replicaSet :=
    Mlist.foldl (fun acc m => rSet.insert m.sender acc) rSet.empty
  isQuorum Msenders ∧
  (∃ m1 ∈ Mlist, ∀ m2 ∈ Mlist, m1.viewID == m2.viewID)
  -- TODO: Check carefully
  -- ∧ (∃ m ∈ Mlist, m.sender == (← Leader m.viewID))


-- (*
--   We only provide the ordering layer here. This is an easier guarantee to
--   provide than saying the execution is equivalent to a linear one. We don't
--   currently model execution, and that's a much harder predicate to compute.
-- *)
-- Linearizability ==
--   LET
--     maxLogPosition == Max({1} \cup
--       { m.logSlotNum : m \in {m \in messages : m.mtype = MRequestReply } })
--   IN ~(\E v1, v2 \in Values \cup { NoOp } :
--          /\ v1 /= v2
--          /\ \E i \in (1 .. maxLogPosition) :
--            /\ Committed(v1, i)
--            /\ Committed(v2, i)
--       )

-- SyncSafety == \A r \in Replicas :
--               \A i \in 1..vSyncPoint[r] :
--               Committed(vLog[r][i], i)

-- --------------------------------------------------------------------------------
-- (* `^\textbf{\large Message Handlers and Actions}^' *)

-- \* `^\textbf{Client action}^'
-- \* Send a request for value v
-- ClientSendsRequest(v) == /\ Send({[ mtype |-> MClientRequest,
--                                     value |-> v ]})
--                          /\ UNCHANGED << sequencerVars, replicaVars >>
-- ✅
action ClientSendsRequest (v : value) {
  require v ≠ NoOp
  require mSet.count messages ≤ MsgCountLimit
  let msg : Message replica value sequencer :=
    { mtype := MsgType.MClientRequest,
      value := v,
      /- unused fields -/
      dest       := default,
      sender     := default,
      viewID     := default,
      request    := default,
      logSlotNum := default,
      sessNum    := default,
      sessMsgNum := default,
      slotNumber := default,
      lastNormal := default,
      log := [] }
  let msgSet := TSet.insert msg mSet.empty
  Send msgSet
}


-- \* `^\textbf{Normal Case Handlers}^'
-- \* Sequencer s receives MClientRequest, m
-- HandleClientRequest(m, s) ==
--   LET
--     smn == seqMsgNums[s]
--   IN
--   /\ Send({[ mtype      |-> MMarkedClientRequest,
--              dest       |-> r,
--              value      |-> m.value,
--              sessNum    |-> s,
--              sessMsgNum |-> smn ] : r \in Replicas})
--   /\ seqMsgNums' = [ seqMsgNums EXCEPT ![s] = smn + 1 ]
--   /\ UNCHANGED replicaVars
-- ✅
action HandleClientRequest (s : sequencer) {
  require mSet.count messages ≤ MsgCountLimit
  let m :| mSet.contains m messages
  require m.mtype == .MClientRequest

  let smn := seqMsgNums s
  let msgs := Replicas.map (fun r =>
    { mtype      := MsgType.MMarkedClientRequest,
      dest       := r,
      value      := m.value,
      sessNum    := s,
      sessMsgNum := smn,
      /- unused fields -/
      sender     := default,
      viewID     := default,
      request    := default,
      logSlotNum := default,
      slotNumber := default,
      lastNormal := default,
      log        := [] } )
  let msgSendSet := msgs.foldl (fun acc m => TSet.insert m acc) mSet.empty
  Send msgSendSet
  seqMsgNums s := smn + 1
}


-- \* Replica r receives MMarkedClientRequest, m
-- HandleMarkedClientRequest(r, m) ==
--   /\ vReplicaStatus[r] = StNormal
--      \* Normal case
--   /\ \/ /\ m.sessNum       = vViewID[r].sessNum
--         /\ m.sessMsgNum    = vSessMsgNum[r]
--         /\ vLog'           = [ vLog EXCEPT ![r] = Append(vLog[r], m.value) ]
--         /\ vSessMsgNum'    = [ vSessMsgNum EXCEPT ![r] = vSessMsgNum[r] + 1 ]
--         /\ Send({[ mtype      |-> MRequestReply,
--                    request    |-> m.value,
--                    viewID     |-> vViewID[r],
--                    logSlotNum |-> Len(vLog'[r]),
--                    sender     |-> r ]})
--         /\ UNCHANGED << sequencerVars,
--                         vViewID, vLastNormView, vCurrentGapSlot, vGapCommitReps,
--                         vViewChanges, vReplicaStatus, vSyncPoint,
--                         vTentativeSync, vSyncReps >>
--      \* SESSION-TERMINATED Case
--      \/ /\ m.sessNum > vViewID[r].sessNum
--         /\ LET
--              newViewID == [ sessNum   |-> m.sessNum,
--                             leaderNum |-> vViewID[r].leaderNum ]
--            IN
--            /\ Send({[ mtype  |-> MViewChangeReq,
--                       dest   |-> d,
--                       viewID |-> newViewID ] : d \in Replicas})
--            /\ UNCHANGED << replicaVars, sequencerVars >>
--      \* DROP-NOTIFICATION Case
--      \/ /\ m.sessNum    = vViewID[r].sessNum
--         /\ m.sessMsgNum > vSessMsgNum[r]
--            \* If leader, commit a gap
--         /\ \/ /\ r = Leader(vViewID[r])
--               /\ SendGapCommit(r)
--            \* Otherwise, ask the leader
--            \/ /\ r /= Leader(vViewID[r])
--               /\ Send({[ mtype      |-> MSlotLookup,
--                          viewID     |-> vViewID[r],
--                          dest       |-> Leader(vViewID[r]),
--                          sender     |-> r,
--                          sessMsgNum |-> vSessMsgNum[r] ]})
--               /\ UNCHANGED << replicaVars, sequencerVars >>
-- action MarkedClientRequest {
-- require mSet.count messages ≤ MsgCountLimit
--   let m :| mSet.contains m messages
--   if m.mtype == .MMarkedClientRequest then
--     HandleMarkedClientRequest m.dest m
-- }
action HandleMarkedClientRequest {
  require mSet.count messages ≤ MsgCountLimit
  let m :| mSet.contains m messages
  require m.mtype == .MMarkedClientRequest
  let r := m.dest

  require vReplicaStatus r == StNormal
  -- Normal case: m.sessNum = vViewID[r].sessNum /\ m.sessMsgNum = vSessMsgNum[r]
  if m.sessNum == (vViewID r).sessNum && m.sessMsgNum == vSessMsgNum r then
    let newLog := (vLog r) ++ [m.value]
    let newLogLen := List.length newLog
    vLog r := newLog
    vSessMsgNum r := vSessMsgNum r + 1
    let replyMsg : Message replica value sequencer := {
      mtype      := .MRequestReply,
      request    := m.value,
      viewID     := vViewID r,
      logSlotNum := newLogLen,
      sender     := r,
      -- Unused fields
      dest       := default,
      value      := default,
      sessNum    := default,
      sessMsgNum := default,
      slotNumber := default,
      lastNormal := default,
      log        := []
    }
    let msgSet := TSet.insert replyMsg mSet.empty
    Send msgSet
  else
    -- -- SESSION-TERMINATED Case: m.sessNum > vViewID[r].sessNum
    if gtSequencer m.sessNum (vViewID r).sessNum then
      let newViewID : View sequencer := {
        sessNum   := m.sessNum,
        leaderNum := (vViewID r).leaderNum }
      -- Send ViewChangeReq to all replicas
      let viewChangeReqMsgs : List (Message replica value sequencer) := Replicas.map (fun d => {
        mtype  := .MViewChangeReq,
        dest   := d,
        viewID := newViewID,
        sender     := default,
        value      := default,
        request    := default,
        logSlotNum := default,
        sessNum    := default,
        sessMsgNum := default,
        slotNumber := default,
        lastNormal := default,
        log        := []
      })
      let msgSendSet := viewChangeReqMsgs.foldl (fun acc msg => TSet.insert msg acc) mSet.empty
      Send msgSendSet
  -- -- DROP-NOTIFICATION Case: m.sessNum = vViewID[r].sessNum /\ m.sessMsgNum > vSessMsgNum[r]
    else
      if m.sessNum == (vViewID r).sessNum && m.sessMsgNum > vSessMsgNum r then
        let leader ← Leader (vViewID r)
        if r == leader then
          SendGapCommit r
        else
          let slotLookupMsg : Message replica value sequencer := {
            mtype      := .MSlotLookup,
            viewID     := vViewID r,
            dest       := leader,
            sender     := r,
            sessMsgNum := vSessMsgNum r,
            /-  Unused fields  -/
            value      := default,
            request    := default,
            logSlotNum := default,
            sessNum    := default,
            slotNumber := default,
            lastNormal := default,
            log        := []
          }
          let msgSet := TSet.insert slotLookupMsg mSet.empty
          Send msgSet
      else
        /- To make the num of states found match -/
        require False
}



-- \* `^\textbf{Gap Commit Handlers}^'
-- \* Replica r receives SlotLookup, m
-- HandleSlotLookup(r, m) ==
--   LET
--     logSlotNum == Len(vLog[r]) + 1 - (vSessMsgNum[r] - m.sessMsgNum)
--   IN
--   /\ m.viewID           = vViewID[r]
--   /\ Leader(vViewID[r]) = r
--   /\ vReplicaStatus[r] = StNormal
--   /\ \/ /\ logSlotNum <= Len(vLog[r])
--         /\ Send({[ mtype      |-> MMarkedClientRequest,
--                    dest       |-> m.sender,
--                    value      |-> vLog[r][logSlotNum],
--                    sessNum    |-> vViewID[r].sessNum,
--                    sessMsgNum |-> m.sessMsgNum ]})
--         /\ UNCHANGED << replicaVars, sequencerVars >>
--      \/ /\ logSlotNum = Len(vLog[r]) + 1
--         /\ SendGapCommit(r)
-- ✅
action HandleSlotLookup  {
  require mSet.count messages ≤ MsgCountLimit
  let m :| mSet.contains m messages
  require m.mtype == .MSlotLookup
  let r := m.dest

  require m.viewID = vViewID r
  require (← Leader (vViewID r)) = r
  require vReplicaStatus r = StNormal

  let logSlotNum := List.length (vLog r) + 1 - (vSessMsgNum r - m.sessMsgNum)
  if logSlotNum ≤ List.length (vLog r) then
    let msg : Message replica value sequencer :=
      { mtype      := MsgType.MMarkedClientRequest,
        dest       := m.sender,
        value      := (vLog r)[logSlotNum - 1]!,
        sessNum    := (vViewID r).sessNum,
        sessMsgNum := m.sessMsgNum,
        /- unused fields -/
        sender     := default,
        viewID     := default,
        request    := default,
        logSlotNum := default,
        slotNumber := default,
        lastNormal := default,
        log        := [] }
    let msgSet := TSet.insert msg mSet.empty
    Send msgSet
  else
    -- if logSlotNum == List.length (vLog r) + 1 then
    require logSlotNum = List.length (vLog r) + 1
    SendGapCommit r
}

-- \* Replica r receives GapCommit, m
-- HandleGapCommit(r, m) ==
--   /\ m.viewID             = vViewID[r]
--   /\ m.slotNumber         <= Len(vLog[r]) + 1
--   /\ \/ vReplicaStatus[r] = StNormal
--      \/ vReplicaStatus[r] = StGapCommit
--   /\ vLog' = [ vLog EXCEPT ![r] = ReplaceItem(vLog[r], m.slotNumber, NoOp) ]
--   \* Increment the msgNumber if necessary
--   /\ IF m.slotNumber > Len(vLog[r]) THEN
--        vSessMsgNum' = [ vSessMsgNum EXCEPT ![r] = vSessMsgNum[r] + 1 ]
--      ELSE
--        UNCHANGED vSessMsgNum
--   /\ Send({[ mtype      |-> MGapCommitRep,
--              dest       |-> Leader(vViewID[r]),
--              sender     |-> r,
--              slotNumber |-> m.slotNumber,
--              viewID     |-> vViewID[r] ],
--            [ mtype      |-> MRequestReply,
--              request    |-> NoOp,
--              viewID     |-> vViewID[r],
--              logSlotNum |-> m.slotNumber,
--              sender     |-> r ]})
--   /\ UNCHANGED << sequencerVars, vGapCommitReps, vViewID, vCurrentGapSlot,
--                   vReplicaStatus, vLastNormView, vViewChanges,
--                   vSyncPoint, vTentativeSync, vSyncReps >>
-- ✅
action HandleGapCommit {
  require mSet.count messages ≤ MsgCountLimit
  let m :| mSet.contains m messages
  require m.mtype == .MGapCommit
  let r := m.dest

  require m.viewID = vViewID r
  require m.slotNumber ≤ List.length (vLog r) + 1
  require (vReplicaStatus r = StNormal) ∨ (vReplicaStatus r = StGapCommit)
  -- TLA+ uses original vLog length for the condition (simultaneous assignment)
  -- So we must capture the original length before updating vLog
  let originalLogLen := (vLog r).length
  vLog r := ReplaceItem (vLog r) m.slotNumber NoOp
  if m.slotNumber > originalLogLen then
    vSessMsgNum r := vSessMsgNum r + 1

  let gapCommitRepMsg :=
    { mtype      := MsgType.MGapCommitRep,
      dest       := (← Leader (vViewID r)),
      sender     := r,
      slotNumber := m.slotNumber,
      viewID     := (vViewID r),
      /- unused fields -/
      value      := default,
      request    := default,
      logSlotNum := default,
      sessNum    := default,
      sessMsgNum := default,
      lastNormal := default,
      log        := [] }
  let requestReplyMsg : Message replica value sequencer :=
    { mtype      := MsgType.MRequestReply,
      request    := NoOp,
      viewID     := vViewID r,
      logSlotNum := m.slotNumber,
      sender     := r,
      /-  unused fields  -/
      dest       := default,
      value      := default,
      sessNum    := default,
      sessMsgNum := default,
      slotNumber := default,
      lastNormal := default,
      log        := [] }
  let msgSet := TSet.insert gapCommitRepMsg (TSet.insert requestReplyMsg mSet.empty)
  Send msgSet
}

-- \* Replica r receives GapCommitRep, m
-- HandleGapCommitRep(r, m) ==
--   /\ vReplicaStatus[r]  = StGapCommit
--   /\ m.viewID           = vViewID[r]
--   /\ Leader(vViewID[r]) = r
--   /\ m.slotNumber       = vCurrentGapSlot[r]
--   /\ vGapCommitReps'    =
--        [ vGapCommitReps EXCEPT ![r] = vGapCommitReps[r] \cup {m} ]
--   \* When there's enough, resume StNormal and process more messages
--   /\ LET isViewPromise(M) == /\ { n.sender : n \in M } \in Quorums
--                              /\ \E n \in M : n.sender = r
--          gCRs             == { n \in vGapCommitReps'[r] :
--                                  /\ n.mtype      = MGapCommitRep
--                                  /\ n.viewID     = vViewID[r]
--                                  /\ n.slotNumber = vCurrentGapSlot[r] }
--      IN
--        IF isViewPromise(gCRs) THEN
--          vReplicaStatus' = [ vReplicaStatus EXCEPT ![r] = StNormal ]
--        ELSE
--          UNCHANGED vReplicaStatus
--   /\ UNCHANGED << sequencerVars, networkVars, vLog, vViewID, vCurrentGapSlot,
--                   vSessMsgNum, vLastNormView, vViewChanges, vSyncPoint,
--                   vTentativeSync, vSyncReps >>
-- ✅
action HandleGapCommitRep {
  require mSet.count messages ≤ MsgCountLimit
  let m :| mSet.contains m messages
  require m.mtype == .MGapCommitRep
  let r := m.dest

  require vReplicaStatus r = StGapCommit
  require m.viewID = vViewID r
  require (← Leader (vViewID r)) = r
  require m.slotNumber = vCurrentGapSlot r
  vGapCommitReps r := mSet.insert m (vGapCommitReps r)
  let gCRs := mSet.filter (vGapCommitReps r) (fun n =>
    n.mtype == MsgType.MGapCommitRep &&
    n.viewID == vViewID r &&
    n.slotNumber == vCurrentGapSlot r)
  let gCRsList := mSet.toList gCRs
  -- isViewPromise(M) == /\ { n.sender : n \in M } \in Quorums
  --                     /\ \E n \in M : n.sender = r
  let senders := gCRsList.map (fun (m : Message replica value sequencer) => m.sender) |>.eraseDups
  let selfIncluded := gCRsList.any (fun (m : Message replica value sequencer) => m.sender = r)
  let isQuorumReached := senders.length * 2 > SIZE
  if isQuorumReached && selfIncluded then
    vReplicaStatus r := StNormal
}


-- \* `^\textbf{Failure Cases}^'
-- \* Replica r starts a Leader change
-- StartLeaderChange(r) ==
--   LET
--     newViewID == [ sessNum   |-> vViewID[r].sessNum,
--                    leaderNum |-> vViewID[r].leaderNum + 1 ]
--   IN
--   /\ Send({[ mtype  |-> MViewChangeReq,
--              dest   |-> d,
--              viewID |-> newViewID ] : d \in Replicas})
--   /\ UNCHANGED << replicaVars, sequencerVars >>
-- ✅
action StartLeaderChange (r : replica) {
  require mSet.count messages ≤ MsgCountLimit
  let newViewID : View sequencer :=
    { sessNum   := (vViewID r).sessNum,
      leaderNum := (vViewID r).leaderNum + 1 }
  let msgs : List (Message replica value sequencer) := Replicas.map (fun d =>
    { mtype  := MsgType.MViewChangeReq,
      dest   := d,
      viewID := newViewID,
      /-  unused fields  -/
      sender     := default,
      value      := default,
      request    := default,
      logSlotNum := default,
      sessNum    := default,
      sessMsgNum := default,
      slotNumber := default,
      lastNormal := default,
      log        := [] } )
  let msgSendSet := msgs.foldl (fun acc m =>TSet.insert m acc) mSet.empty
  Send msgSendSet
}


-- \* `^\textbf{View Change Handlers}^'
-- \* Replica r gets MViewChangeReq, m
-- HandleViewChangeReq(r, m) ==
--   LET
--     currentViewID == vViewID[r]
--     newSessNum    == Max({currentViewID.sessNum, m.viewID.sessNum})
--     newLeaderNum  == Max({currentViewID.leaderNum, m.viewID.leaderNum})
--     newViewID     == [ sessNum |-> newSessNum, leaderNum |-> newLeaderNum ]
--   IN
--   /\ currentViewID   /= newViewID
--   /\ vReplicaStatus' = [ vReplicaStatus EXCEPT ![r] = StViewChange ]
--   /\ vViewID'        = [ vViewID EXCEPT ![r] = newViewID ]
--   /\ vViewChanges'   = [ vViewChanges EXCEPT ![r] = {} ]
--   /\ Send({[ mtype      |-> MViewChange,
--              dest       |-> Leader(newViewID),
--              sender     |-> r,
--              viewID     |-> newViewID,
--              lastNormal |-> vLastNormView[r],
--              sessMsgNum |-> vSessMsgNum[r],
--              log        |-> vLog[r] ]} \cup
--            \* Send the MViewChangeReqs in case this is an entirely new view
--            {[ mtype  |-> MViewChangeReq,
--               dest   |-> d,
--               viewID |-> newViewID ] : d \in Replicas})
--   /\ UNCHANGED << vCurrentGapSlot, vGapCommitReps, vLog, vSessMsgNum,
--                   vLastNormView, sequencerVars, vSyncPoint,
--                   vTentativeSync, vSyncReps >>
-- ✅
action HandleViewChangeReq {
  require mSet.count messages ≤ MsgCountLimit
  let m :| mSet.contains m messages
  require m.mtype = .MViewChangeReq
  let r := m.dest

  let currentViewID := vViewID r
  let newSessNum    := if seqOrd.le (currentViewID.sessNum) (m.viewID.sessNum) then m.viewID.sessNum else currentViewID.sessNum
  let newLeaderNum  := Nat.max currentViewID.leaderNum m.viewID.leaderNum
  let newViewID     := { sessNum := newSessNum, leaderNum := newLeaderNum }
  require currentViewID ≠ newViewID
  vReplicaStatus r := StViewChange
  vViewID r := newViewID
  vViewChanges r := mSet.empty
  let viewChangeMsg : Message replica value sequencer :=
    { mtype      := MsgType.MViewChange,
      dest       := (← Leader newViewID),
      sender     := r,
      viewID     := newViewID,
      lastNormal := vLastNormView r,
      sessMsgNum := vSessMsgNum r,
      log        := vLog r,
      /- unused fields -/
      value      := default,
      request    := default,
      logSlotNum := default,
      sessNum    := default,
      slotNumber := default }
  let viewChangeReqMsgs : List (Message replica value sequencer) := Replicas.map (fun d =>
    { mtype  := MsgType.MViewChangeReq,
      dest   := d,
      viewID := newViewID,
      /- unused fields -/
      sender     := default,
      value      := default,
      request    := default,
      logSlotNum := default,
      sessNum    := default,
      sessMsgNum := default,
      slotNumber := default,
      lastNormal := default,
      log        := [] } )
  let msgSendSet :=
    viewChangeReqMsgs.foldl (fun acc (m : Message replica value sequencer) => TSet.insert m acc)
    (TSet.insert viewChangeMsg mSet.empty)
  Send msgSendSet
}


-- \* Replica r receives MViewChange, m
-- HandleViewChange(r, m) ==
--   \* Add the message to the log
--   /\ vViewID[r]         = m.viewID
--   /\ vReplicaStatus[r]  = StViewChange
--   /\ Leader(vViewID[r]) = r
--   /\ vViewChanges' =
--      [ vViewChanges EXCEPT ![r] = vViewChanges[r] \cup {m}]
--   \* If there's enough, start the new view
--   /\ LET
--        isViewPromise(M) == /\ { n.sender : n \in M } \in Quorums
--                            /\ \E n \in M : n.sender = r
--        vCMs             == { n \in vViewChanges'[r] :
--                                /\ n.mtype  = MViewChange
--                                /\ n.viewID = vViewID[r] }
--        \* Create the state for the new view
--        normalViews == { n.lastNormal : n \in vCMs }
--        lastNormal  == (CHOOSE v \in normalViews : \A v2 \in normalViews :
--                          ViewLe(v2, v))
--        goodLogs    == { n.log : n \in
--                           { o \in vCMs : o.lastNormal = lastNormal } }
--        \* If updating seqNum, revert sessMsgNum to 0; otherwise use latest
--        newMsgNum   ==
--          IF lastNormal.sessNum = vViewID[r].sessNum THEN
--             Max({ n.sessMsgNum : n \in
--                     { o \in vCMs : o.lastNormal = lastNormal } })
--          ELSE
--            0
--      IN
--        IF isViewPromise(vCMs) THEN
--          Send({[ mtype      |-> MStartView,
--                  dest       |-> d,
--                  viewID     |-> vViewID[r],
--                  log        |-> CombineLogs(goodLogs),
--                  sessMsgNum |-> newMsgNum ] : d \in Replicas })
--        ELSE
--          UNCHANGED networkVars
--   /\ UNCHANGED << vReplicaStatus, vViewID, vLog, vSessMsgNum, vCurrentGapSlot,
--                   vGapCommitReps, vLastNormView, sequencerVars, vSyncPoint,
--                   vTentativeSync, vSyncReps >>
-- ✅
action HandleViewChange {
  require mSet.count messages ≤ MsgCountLimit
  let m :| mSet.contains m messages
  require m.mtype = .MViewChange
  let r := m.dest

  require vViewID r = m.viewID
  require vReplicaStatus r = StViewChange
  require (← Leader (vViewID r)) = r
  vViewChanges r := mSet.insert m (vViewChanges r)
  let vCMs := mSet.filter (vViewChanges r) (fun n =>
    n.mtype == .MViewChange && n.viewID == vViewID r)
  let vCMsList := mSet.toList vCMs

  let senders := vCMsList.map (fun (m : Message replica value sequencer) => m.sender) |>.eraseDups
  let isQuorumReached := senders.length * 2 > SIZE
  let selfIncluded := senders.contains r

  if isQuorumReached && selfIncluded then
    -- normalViews == { n.lastNormal : n \in vCMs }
    -- lastNormal == (CHOOSE v \in normalViews : \A v2 \in normalViews : ViewLe(v2, v))
    -- Find the maximum lastNormal view (the one where all others are ViewLe to it)
    let lastNormal := vCMsList.foldl (fun acc n =>
      if ViewLe acc n.lastNormal then
        n.lastNormal
      else
        acc)
      (vCMsList.head!.lastNormal)

    let goodLogMsgs := vCMsList.filter (fun o => o.lastNormal == lastNormal)
    let goodLogs := goodLogMsgs.map (fun n => n.log)
    let combinedLog ← CombineLogs goodLogs
    /- newMsgNum == IF lastNormal.sessNum = vViewID[r].sessNum THEN
                    Max({ n.sessMsgNum : n \in { o \in vCMs : o.lastNormal = lastNormal } })
                  ELSE 0 -/
    let newMsgNum :=
      if lastNormal.sessNum == (vViewID r).sessNum then
        goodLogMsgs.foldl (fun acc n => Nat.max acc n.sessMsgNum) 0
      else
        0
    let startViewMsgs : List (Message replica value sequencer) := Replicas.map (fun d =>
      { mtype      := .MStartView,
        dest       := d,
        viewID     := vViewID r,
        log        := combinedLog,
        sessMsgNum := newMsgNum,
        /-  unused fields  -/
        sender     := default,
        value      := default,
        request    := default,
        logSlotNum := default,
        sessNum    := default,
        slotNumber := default,
        lastNormal := default })
    let msgSendSet := startViewMsgs.foldl (fun acc msg => TSet.insert msg acc) mSet.empty
    Send msgSendSet
}

-- \* Replica r receives a MStartView, m
-- HandleStartView(r, m) ==
--   (*
--     Note how I handle this. There was actually a bug in prose description in the
--     paper where the following guard was underspecified.
--   *)
--   /\ \/ ViewLt(vViewID[r], m.viewID)
--      \/ vViewID[r]   = m.viewID /\ vReplicaStatus[r] = StViewChange
--   /\ vLog'           = [ vLog EXCEPT ![r] = m.log ]
--   /\ vSessMsgNum'    = [ vSessMsgNum EXCEPT ![r] = m.sessMsgNum ]
--   /\ vReplicaStatus' = [ vReplicaStatus EXCEPT ![r] = StNormal ]
--   /\ vViewID'        = [ vViewID EXCEPT ![r] = m.viewID ]
--   /\ vLastNormView'  = [ vLastNormView EXCEPT ![r] = m.viewID ]
--   \* Send replies (in the new view) for all log items
--   /\ Send({[ mtype      |-> MRequestReply,
--              request    |-> m.log[i],
--              viewID     |-> m.viewID,
--              logSlotNum |-> i,
--              sender     |-> r ] : i \in (1..Len(m.log))})
--   /\ UNCHANGED << sequencerVars,
--                   vViewChanges, vCurrentGapSlot, vGapCommitReps, vSyncPoint,
--                   vTentativeSync, vSyncReps >>
-- ✅
action HandleStartView {
  require mSet.count messages ≤ MsgCountLimit
  let m :| mSet.contains m messages
  require m.mtype = .MStartView
  let r := m.dest

  require (ViewLt (vViewID r) m.viewID) ∨ (vViewID r = m.viewID ∧ vReplicaStatus r = StViewChange)
  vLog r := m.log
  vSessMsgNum r := m.sessMsgNum
  vReplicaStatus r := StNormal
  vViewID r := m.viewID
  vLastNormView r := m.viewID

  let requestReplyMsgs : List (Message replica value sequencer) :=
    ((List.range m.log.length).map (· + 1)).map (fun i =>
      { mtype      := MsgType.MRequestReply,
        sender     := r,
        dest       := default,
        viewID     := m.viewID,
        request    := m.log.getD (i - 1) default,
        logSlotNum := i,
        /-  unused fields  -/
        value      := default,
        sessNum    := default,
        sessMsgNum := default,
        slotNumber := default,
        lastNormal := default,
        log        := [] })
  let msgSendSet := requestReplyMsgs.foldl (fun acc msg => TSet.insert msg acc) mSet.empty
  Send msgSendSet
}


-- \* `^\textbf{Synchronization handlers}^'
-- \* Leader replica r starts synchronization
-- StartSync(r) ==
--   /\ Leader(vViewID[r]) = r
--   /\ vReplicaStatus[r]  = StNormal
--   /\ vSyncReps'         = [ vSyncReps EXCEPT ![r] = {} ]
--   /\ vTentativeSync'    = [ vTentativeSync EXCEPT ![r] = Len(vLog[r]) ]
--   /\ Send({[ mtype      |-> MSyncPrepare,
--              sender     |-> r,
--              dest       |-> d,
--              viewID     |-> vViewID[r],
--              sessMsgNum |-> vSessMsgNum[r],
--              log        |-> vLog[r] ] : d \in Replicas })
--   /\ UNCHANGED << sequencerVars, vLog, vViewID, vSessMsgNum, vLastNormView,
--                   vCurrentGapSlot, vViewChanges, vReplicaStatus,
--                   vGapCommitReps, vSyncPoint >>
-- ✅
action StartSync (r : replica) {
  require mSet.count messages ≤ MsgCountLimit
  require (← Leader (vViewID r)) == r
  require vReplicaStatus r == StNormal

  vSyncReps r := mSet.empty
  vTentativeSync r := List.length (vLog r)
  let msgs : List (Message replica value sequencer) := Replicas.map (fun d =>
    { mtype      := .MSyncPrepare,
      sender     := r,
      dest       := d,
      viewID     := vViewID r,
      sessMsgNum := vSessMsgNum r,
      log        := vLog r,
      /-  unused fields  -/
      value      := default,
      request    := default,
      logSlotNum := default,
      sessNum    := default,
      slotNumber := default,
      lastNormal := default } )
  let msgSendSet := msgs.foldl (fun acc m => TSet.insert m acc) mSet.empty
  Send msgSendSet
}

-- \* Replica r receives MSyncPrepare, m
-- HandleSyncPrepare(r, m) ==
--   LET
--     newLog    == m.log \o SubSeq(vLog[r], Len(m.log) + 1, Len(vLog[r]))
--     newMsgNum == vSessMsgNum[r] + (Len(newLog) - Len(vLog[r]))
--   IN
--   /\ vReplicaStatus[r] = StNormal
--   /\ m.viewID          = vViewID[r]
--   /\ m.sender          = Leader(vViewID[r])
--   /\ vLog'             = [ vLog EXCEPT ![r] = newLog ]
--   /\ vSessMsgNum'      = [ vSessMsgNum EXCEPT ![r] = newMsgNum ]
--   /\ Send({[ mtype         |-> MSyncRep,
--              sender        |-> r,
--              dest          |-> m.sender,
--              viewID        |-> vViewID[r],
--              logSlotNumber |-> Len(m.log) ]} \cup
--           {[ mtype      |-> MRequestReply,
--              request    |-> vLog'[r][i],
--              viewID     |-> vViewID[r],
--              logSlotNum |-> i,
--              sender     |-> r ] : i \in 1..Len(vLog'[r])})
--   /\ UNCHANGED << sequencerVars, vViewID, vLastNormView, vCurrentGapSlot,
--                   vViewChanges, vReplicaStatus, vGapCommitReps,
--                   vSyncPoint, vTentativeSync, vSyncReps >>
-- ✅
action HandleSyncPrepare {
  require mSet.count messages ≤ MsgCountLimit
  let m :| mSet.contains m messages
  require m.mtype = .MSyncPrepare
  let r := m.dest

  require vReplicaStatus r = StNormal
  require m.viewID = vViewID r
  require m.sender = (← Leader (vViewID r))
  /- TLA+ operator: `SubSeq(seq, m, n)`:
  Used to select the subsequence
  <<s[m], s[m+1], ... , s[n]>> in seq. Indices are `inclusive`.
  Example: `SubSeq(<<7, 8, 9>>, 1, 2) = <<7, 8>>`.
  SubSeq(L, m, n) == L.extract (m - 1) n -/
  let newLog := m.log ++ (vLog r).extract (List.length m.log) (List.length (vLog r))
  let newMsgNum := vSessMsgNum r + (List.length newLog - List.length (vLog r))
  vLog r := newLog
  vSessMsgNum r := newMsgNum

  let syncRepMsg : Message replica value sequencer :=
    { mtype         := MsgType.MSyncRep,
      sender        := r,
      dest          := m.sender,
      viewID        := vViewID r,
      logSlotNum    := List.length (m.log),
      value         := default,
      request       := default,
      sessNum       := default,
      sessMsgNum    := default,
      slotNumber    := default,
      lastNormal    := default,
      log           := [] }
  let requestReplyMsgs : List (Message replica value sequencer) :=
    ((List.range newLog.length).map (· + 1)).map (fun i =>
      { mtype       := MsgType.MRequestReply,
        viewID      := vViewID r,
        request     := newLog.getD (i - 1) default,
        logSlotNum  := i,
        sender      := r,
        dest        := default,
        value       := default,
        sessNum     := default,
        sessMsgNum  := default,
        slotNumber  := default,
        lastNormal  := default,
        log         := [] })
  let allMsgs := syncRepMsg :: requestReplyMsgs
  let msgSendSet := allMsgs.foldl (fun acc msg => TSet.insert msg acc) mSet.empty
  Send msgSendSet
}


-- \* Replica r receives MSyncRep, m
-- HandleSyncRep(r, m) ==
--   /\ m.viewID          = vViewID[r]
--   /\ vReplicaStatus[r] = StNormal
--   /\ vSyncReps'        = [ vSyncReps EXCEPT ![r] = vSyncReps[r] \cup { m } ]
--   /\ LET isViewPromise(M) == /\ { n.sender : n \in M } \in Quorums
--                              /\ \E n \in M : n.sender = r
--          sRMs             == { n \in vSyncReps'[r] :
--                                  /\ n.mtype         = MSyncRep
--                                  /\ n.viewID        = vViewID[r]
--                                  /\ n.logSlotNumber = vTentativeSync[r] }
--          committedLog     == IF vTentativeSync[r] >= 1 THEN
--                                SubSeq(vLog[r], 1, vTentativeSync[r])
--                              ELSE
--                                << >>
--      IN
--        IF isViewPromise(sRMs) THEN
--          Send({[ mtype         |-> MSyncCommit,
--                  sender        |-> r,
--                  dest          |-> d,
--                  viewID        |-> vViewID[r],
--                  log           |-> committedLog,
--                  sessMsgNum    |-> vSessMsgNum[r] -
--                                    (Len(vLog[r]) - Len(committedLog)) ] :
--               d \in Replicas })
--        ELSE
--          UNCHANGED networkVars
--   /\ UNCHANGED << sequencerVars, vLog, vViewID, vSessMsgNum, vLastNormView,
--                   vCurrentGapSlot, vViewChanges, vReplicaStatus,
--                   vGapCommitReps, vSyncPoint, vTentativeSync >>
-- ✅
action HandleSyncRep  {
  require mSet.count messages ≤ MsgCountLimit
  let m :| mSet.contains m messages
  require m.mtype = .MSyncRep
  let r := m.dest

  require m.viewID = vViewID r
  require vReplicaStatus r = StNormal
  vSyncReps r := mSet.insert m (vSyncReps r)
  let sRMs := mSet.filter (vSyncReps r) (fun n =>
    n.mtype == .MSyncRep &&
    n.viewID == vViewID r &&
    n.logSlotNum == vTentativeSync r)
  let sRMsList := mSet.toList sRMs
  /- isViewPromise(M) == /\ { n.sender : n \in M } \in Quorums
                         /\ \E n \in M : n.sender = r -/
  let senders := sRMsList.map (fun m => m.sender) |>.eraseDups
  let isQuorumReached := senders.length * 2 > SIZE
  let selfIncluded := senders.contains r

  if isQuorumReached && selfIncluded then
    let committedLog := if vTentativeSync r ≥ 1 then
        (vLog r).take (vTentativeSync r)
      else
        []
    let syncCommitMsgs := Replicas.map (fun d =>
      { mtype       := MsgType.MSyncCommit,
        sender      := r,
        dest        := d,
        viewID      := vViewID r,
        log         := committedLog,
        sessMsgNum  := vSessMsgNum r - ((vLog r).length - committedLog.length),
        value       := default,
        request     := default,
        logSlotNum  := default,
        sessNum     := default,
        slotNumber  := default,
        lastNormal  := default })
    let msgSendSet := syncCommitMsgs.foldl (fun acc msg => TSet.insert msg acc) mSet.empty
    Send msgSendSet
}



-- \* Replica r receives MSyncCommit, m
-- HandleSyncCommit(r, m) ==
--   LET
--     newLog    == m.log \o SubSeq(vLog[r], Len(m.log) + 1, Len(vLog[r]))
--     newMsgNum == vSessMsgNum[r] + (Len(newLog) - Len(vLog[r]))
--   IN
--   /\ vReplicaStatus[r] = StNormal
--   /\ m.viewID          = vViewID[r]
--   /\ m.sender          = Leader(vViewID[r])
--   /\ vLog'             = [ vLog EXCEPT ![r] = newLog ]
--   /\ vSessMsgNum'      = [ vSessMsgNum EXCEPT ![r] = newMsgNum ]
--   /\ vSyncPoint'       = [ vSyncPoint EXCEPT ![r] = Len(m.log) ]
--   /\ UNCHANGED << sequencerVars, networkVars, vViewID, vLastNormView,
--                   vCurrentGapSlot, vViewChanges, vReplicaStatus,
--                   vGapCommitReps, vTentativeSync, vSyncReps >>
action SyncCommit {
  require mSet.count messages ≤ MsgCountLimit
  let m :| mSet.contains m messages
  require m.mtype = .MSyncCommit
  let r := m.dest

  require vReplicaStatus r == StNormal
  require m.viewID == vViewID r
  require m.sender == (← Leader (vViewID r))

  let newLog := m.log ++ (vLog r).extract (List.length m.log) (List.length (vLog r))
  let newMsgNum := vSessMsgNum r + (List.length newLog - List.length (vLog r))
  vLog r := newLog
  vSessMsgNum r := newMsgNum
  vSyncPoint r := List.length (m.log)
}


-- Next == \* Handle Messages
--         \/ \E m \in messages :
--            \E s \in Sequencers
--                              : /\ m.mtype = MClientRequest
--                                /\ HandleClientRequest(m, s)
--         \/ \E m \in messages : /\ m.mtype = MMarkedClientRequest
--                                /\ HandleMarkedClientRequest(m.dest, m)
--         \/ \E m \in messages : /\ m.mtype = MViewChangeReq
--                                /\ HandleViewChangeReq(m.dest, m)
--         \/ \E m \in messages : /\ m.mtype = MViewChange
--                                /\ HandleViewChange(m.dest, m)
--         \/ \E m \in messages : /\ m.mtype = MStartView
--                                /\ HandleStartView(m.dest, m)
--         \/ \E m \in messages : /\ m.mtype = MSlotLookup
--                                /\ HandleSlotLookup(m.dest, m)
--         \/ \E m \in messages : /\ m.mtype = MGapCommit
--                                /\ HandleGapCommit(m.dest, m)
--         \/ \E m \in messages : /\ m.mtype = MGapCommitRep
--                                /\ HandleGapCommitRep(m.dest, m)
--         \/ \E m \in messages : /\ m.mtype = MSyncPrepare
--                                /\ HandleSyncPrepare(m.dest, m)
--         \/ \E m \in messages : /\ m.mtype = MSyncRep
--                                /\ HandleSyncRep(m.dest, m)
--         \/ \E m \in messages : /\ m.mtype = MSyncCommit
--                                /\ HandleSyncCommit(m.dest, m)
--         \* Client Actions
--         \/ \E v \in Values : ClientSendsRequest(v)
--         \* Start synchronization
--         \/ \E r \in Replicas : StartSync(r)
--         \* Failure case
--         \/ \E r \in Replicas : StartLeaderChange(r)

-- --------------------------------------------------------------------------------
-- (******************************************************************************)
-- (* Additions to the file.                                                     *)
-- (******************************************************************************)

-- \* Helper function
-- Range(f) == {f[x] : x \in DOMAIN f}

-- \* For initializing constants in the config file; we must initialize them here
-- \* in order to provide a sequence of ReplicasConst elements
-- ReplicasConst == { "n1", "n2", "n3" }
-- ReplicaOrderConst == << "n1", "n2", "n3" >>

-- \* Backported Ivy invariants
-- ClientNoOp ==
--    LET mClientReqs == {m \in messages : m.mtype = MClientRequest}
--    IN \A m \in mClientReqs : m.value # NoOp
-- invariant [client_no_op]
--   let mfilter := mSet.toList messages |>.filter (fun m => m.mtype == .MClientRequest)
--   mfilter.all (fun m => m.value ≠ NoOp)
--   -- ∀m ∈ (mSet.filter messages (fun m => m.mtype == .MClientRequest)),
--   --   m.value ≠ NoOp

-- -- MarkedReqNonTrivial ==
-- --    LET mMClientReqs == {m \in messages : m.mtype = MMarkedClientRequest}
-- --        mClientReqs == {m \in messages : m.mtype = MClientRequest}
-- --    IN \A m \in {m \in mMClientReqs : m.value # NoOp} :
-- --          \E w \in mClientReqs : w.value = m.value
-- invariant [marked_req_non_trivial]
--   let mMClientReqs := mSet.filter messages (fun m => m.mtype == .MMarkedClientRequest)
--   let mClientReqs := mSet.filter messages (fun m => m.mtype == .MClientRequest)
--   let mMClientReqsList := mSet.toList mMClientReqs
--   mMClientReqsList |>.filter (fun m => m.value ≠ NoOp)
--     |>.all (fun m => mSet.toList mClientReqs
--         |>.any (fun w => w.value == m.value))

-- -- RequestReplyNonTrivial ==
-- --    LET mReqReps == {m \in messages : m.mtype = MRequestReply}
-- --        mClientReqs == {m \in messages : m.mtype = MClientRequest}
-- --    IN \A m \in {m \in mReqReps : m.request # NoOp} :
-- --          \E w \in mClientReqs : w.value = m.request
-- invariant [request_reply_non_trivial]
--   let mReqReps := mSet.filter messages (fun m => m.mtype == .MRequestReply)
--   let mClientReqs := mSet.filter messages (fun m => m.mtype == .MClientRequest)
--   let mReqRepsList := mSet.toList mReqReps
--   mReqRepsList |>.filter (fun m => m.request ≠ NoOp)
--     |>.all (fun m => mSet.toList mClientReqs
--         |>.any (fun w => w.value == m.request))


-- LogNonTrivial ==
--    LET mMClientReqs == {m \in messages : m.mtype = MMarkedClientRequest}
--    IN \A r \in Replicas :
--          \A v \in {v \in Range(vLog[r]) : v # NoOp} :
--             \E m \in mMClientReqs : m.value = v

-- \* This does not hold with multiple sequencers, so this will fail if the
-- \* NumSequencers constant is greater than 1
-- ValidSessMsgNum ==
--    \A r \in Replicas :
--       Len(vLog[r]) + 1 = vSessMsgNum[r]

-- LeadGapCommits ==
--    LET leaders == {r \in Replicas : Leader(vViewID[r]) = r}
--        mGaps == {m \in messages : m.mtype = MGapCommit}
--    IN \A r \in leaders :
--          \A n \in (0..Len(vLog[r])) :
--             \A m \in {m \in mGaps : m.dest = r /\ m.viewID = vViewID[r]} :
--                \/ m.slotNumber # n
--                \/ vLog[r][m.slotNumber] = NoOp

-- LogSMN ==
--    \A r \in Replicas :
--       \A n \in (vSessMsgNum[r]..(vSessMsgNum[r] + 3)) :
--          Len(vLog[r]) < n

-- LogSMNGap ==
--    LET leaders == {r \in Replicas : Leader(vViewID[r]) = r}
--        mGaps == {m \in messages : m.mtype = MGapCommit}
--    IN \A r \in leaders :
--          \A n \in ((vSessMsgNum[r] + 1)..(vSessMsgNum[r] + 3)) :
--             \A m \in {m \in mGaps : m.dest = r /\ m.viewID = vViewID[r]} :
--                m.slotNumber # n

-- ReplySMN ==
--    LET mReqReps == {m \in messages : m.mtype = MRequestReply}
--    IN \A m \in mReqReps : m.logSlotNum < vSessMsgNum[m.sender]

-- LeaderSMNGap ==
--    LET leaders == {r \in Replicas : Leader(vViewID[r]) = r}
--        mGaps == {m \in messages : m.mtype = MGapCommit}
--    IN \A r \in leaders :
--          LET a == {m \in mGaps : m.dest = r /\ m.viewID = vViewID[r]}
--              b == {m.slotNumber : m \in a}
--              c == {m \in b : m = Max(b)}
--              d == {m \in c : m = vSessMsgNum[r]}
--          IN \A n \in d :
--             /\ vReplicaStatus[r] = StGapCommit
--             /\ vCurrentGapSlot[r] = n
-- invariant [message_less_than_three] mSet.count messages < 4
-- \* Conjunction of invariants
-- IvyInvariants ==
--    /\ ClientNoOp
--    /\ MarkedReqNonTrivial
--    /\ RequestReplyNonTrivial
--    /\ LogNonTrivial
--    /\ ValidSessMsgNum
--    /\ LeadGapCommits
--    /\ LogSMN
--    /\ LogSMNGap
--    /\ ReplySMN
--    /\ LeaderSMNGap
#gen_spec

#model_check
{
  replica := Fin 3
  replicaSet := Std.ExtTreeSet (Fin 3) compare
  sequencer := Fin 1
  setMsg := Std.ExtTreeSet (Message (Fin 3) value_IndT (Fin 1)) compare
}
{
  ReplicaOrder := [0, 1, 2]
  Replicas := [0, 1, 2]
  SIZE := 3
  one := 0
  MsgCountLimit := 14
}

-- ================================================================================
end NOPaxosTLA
