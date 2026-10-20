module

public import Veil

-- NOTE: `Max (Fin n)` used to come from Mathlib, which Veil no longer depends on
public instance : Max (Fin n) := maxOfLe

veil module NOPaxos

set_option veil.deferVCGeneration true

abbrev LogTy (value : Type) := Array value

-- ViewIDs == [ leaderNum |-> n \in (1..), sessNum |-> n \in Sequencers ]
@[veil_decl]
structure View (seq : Type) where
  leaderNum : Nat
  sessNum   : seq

-- NOTE: This takes ~3 seconds
@[veil_decl]
inductive Msg (rep val seq : Type) where
  | clientRequest (value : val)
  | markedClientRequest (dest : rep) (value : val) (sessNum : seq) (sessMsgNum : Nat)
  | requestReply (sender : rep) (viewID : View seq) (request : val) (logSlotNum : Nat)
  | slotLookup (dest : rep) (sender : rep) (viewID : View seq) (sessMsgNum : Nat)
  | gapCommit (dest : rep) (viewID : View seq) (slotNumber : Nat)
  | gapCommitRep (dest : rep) (sender : rep) (viewID : View seq) (slotNumber : Nat)
  | viewChangeReq (dest : rep) (viewID : View seq)
  | viewChange (dest : rep) (sender : rep) (viewID : View seq)
      (lastNormal : View seq) (sessMsgNum : Nat) (log : LogTy val)
  | startView (dest : rep) (viewID : View seq) (log : LogTy val) (sessMsgNum : Nat)
  | syncPrepare (dest : rep) (sender : rep) (viewID : View seq)
      (sessMsgNum : Nat) (log : LogTy val)
  | syncRep (dest : rep) (sender : rep) (viewID : View seq) (logSlotNum : Nat)
  | syncCommit (dest : rep) (sender : rep) (viewID : View seq)
      (log : LogTy val) (sessMsgNum : Nat)

def Msg.value [Inhabited val] (msg : Msg rep val seq) : val :=
  match msg with
  | .clientRequest v => v
  | .markedClientRequest _ v _ _ => v
  | .requestReply _ _ v _ => v
  | _ => default

def Msg.dest [Inhabited rep] (msg : Msg rep val seq) : rep :=
  match msg with
  | .markedClientRequest d _ _ _ => d
  | .slotLookup d _ _ _ => d
  | .gapCommit d _ _ => d
  | .gapCommitRep d _ _ _ => d
  | .viewChangeReq d _ => d
  | .viewChange d _ _ _ _ _ => d
  | .startView d _ _ _ => d
  | .syncPrepare d _ _ _ _ => d
  | .syncRep d _ _ _ => d
  | .syncCommit d _ _ _ _ => d
  | _ => default

def Msg.sessNum [Inhabited seq] (msg : Msg rep val seq) : seq :=
  match msg with
  | .markedClientRequest _ _ sn _ => sn
  | _ => default

def Msg.sessMsgNum (msg : Msg rep val seq) : Nat :=
  match msg with
  | .markedClientRequest _ _ _ smn => smn
  | .slotLookup _ _ _ smn => smn
  | .viewChange _ _ _ _ smn _ => smn
  | .startView _ _ _ smn => smn
  | .syncPrepare _ _ _ smn _ => smn
  | .syncCommit _ _ _ _ smn => smn
  | _ => 0

def Msg.sender [Inhabited rep] (msg : Msg rep val seq) : rep :=
  match msg with
  | .requestReply s _ _ _ => s
  | .slotLookup _ s _ _ => s
  | .gapCommitRep _ s _ _ => s
  | .viewChange _ s _ _ _ _ => s
  | .syncPrepare _ s _ _ _ => s
  | .syncRep _ s _ _ => s
  | .syncCommit _ s _ _ _ => s
  | _ => default

def Msg.viewID [Inhabited seq] (msg : Msg rep val seq) : View seq :=
  match msg with
  | .requestReply _ v _ _ => v
  | .slotLookup _ _ v _ => v
  | .gapCommit _ v _ => v
  | .gapCommitRep _ _ v _ => v
  | .viewChangeReq _ v => v
  | .viewChange _ _ v _ _ _ => v
  | .startView _ v _ _ => v
  | .syncPrepare _ _ v _ _ => v
  | .syncRep _ _ v _ => v
  | .syncCommit _ _ v _ _ => v
  | _ => default

def Msg.slotNumber (msg : Msg rep val seq) : Nat :=
  match msg with
  | .gapCommit _ _ s => s
  | .gapCommitRep _ _ _ s => s
  | _ => 0

def Msg.log (msg : Msg rep val seq) : LogTy val :=
  match msg with
  | .viewChange _ _ _ _ _ l => l
  | .startView _ _ l _ => l
  | .syncPrepare _ _ _ _ l => l
  | .syncCommit _ _ _ l _ => l
  | _ => #[]

abbrev SeqTy (maxSeq : Nat) := Fin (maxSeq + 1)

abbrev NOPaxosMsg (rep val : Type) (maxSeq : Nat) := Msg rep val (SeqTy maxSeq)

param maxSeq : Nat
-- NOTE: Here, only seq numbers are 0-based;
-- also note that in TLA, the list indices are 1-based

type replica
type replicaSet
type value
instantiate rSet : TSet replica replicaSet

enum ReplicaStatus = {StNormal, StViewChange, StGapCommit}

type MsgSet
instantiate mSet : TSet (NOPaxosMsg replica value maxSeq) MsgSet

individual messages : MsgSet

function seqMsgNums      : SeqTy maxSeq → Nat

function vLog            : replica → LogTy value
function vViewID         : replica → View (SeqTy maxSeq)
function vLastNormView   : replica → View (SeqTy maxSeq)
function vSessMsgNum     : replica → Nat
function vViewChanges    : replica → MsgSet
function vGapCommitReps  : replica → MsgSet
function vCurrentGapSlot : replica → Nat
function vReplicaStatus  : replica → ReplicaStatus
function vSyncPoint      : replica → Nat
function vTentativeSync  : replica → Nat
function vSyncReps       : replica → MsgSet

immutable individual NoOp : value
immutable individual MsgCountLimit : Nat
immutable individual ReplicaOrder  : Array replica

-- ASSUME IsFiniteSet(Replicas)
instantiate replicaEnumerable : Veil.Enumeration replica

-- veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

after_init {
  let initSeq : SeqTy maxSeq := ⟨0, Nat.zero_lt_succ maxSeq⟩
  let initView : View (SeqTy maxSeq) := { sessNum := initSeq, leaderNum := 1 }
  vLog R := #[]
  vViewID R := initView
  vLastNormView R := initView
  vSessMsgNum R := 1
  vViewChanges R := mSet.empty
  vGapCommitReps R := mSet.empty
  vCurrentGapSlot R := 0
  vReplicaStatus R := StNormal
  vSyncPoint R := 0
  vTentativeSync R := 0
  vSyncReps R := mSet.empty

  messages := mSet.empty
  seqMsgNums S := 1
}

-- Leader(viewID) == ReplicaOrder[(viewID.leaderNum % Len(ReplicaOrder)) +
--                                (IF viewID.leaderNum >= Len(ReplicaOrder)
--                                 THEN 1 ELSE 0)]
ghost function Leader (v : View (SeqTy maxSeq)) : replica :=
  let idx := (v.leaderNum % ReplicaOrder.size) +
             (if v.leaderNum ≥ ReplicaOrder.size then 1 else 0)
  ReplicaOrder[(idx - 1)]!

-- ViewLe(v1, v2) == /\ v1.sessNum    <= v2.sessNum
--                   /\ v1.leaderNum <= v2.leaderNum
-- ViewLt(v1, v2) == ViewLe(v1, v2) /\ v1 /= v2
ghost relation ViewLe (v1 v2 : View (SeqTy maxSeq)) :=
  v1.sessNum ≤ v2.sessNum ∧ v1.leaderNum ≤ v2.leaderNum
ghost relation ViewLt (v1 v2 : View (SeqTy maxSeq)) :=
  ViewLe v1 v2 ∧ (v1 ≠ v2)

-- \* `^\textbf{Network Helpers}^'
-- \* Add a message to the network
-- Send(ms) == messages' = messages \cup ms
procedure Send (ms : MsgSet) {
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
ghost function CombineLogs (ls : List (LogTy value)) : LogTy value :=
  -- NOTE: `xs` should be actually a set here, but to keep the order for `CHOOSE` we use a list
  let combineSlot (xs : List value) : value :=
    if NoOp ∈ xs then NoOp
    else if h : xs.isEmpty then NoOp
    else xs.head (by grind)   -- CHOOSE x \in xs : x /= NoOp
  let range := ls.map Array.size |>.max? |>.getD 0
  Array.range range |>.map fun i =>
    let i := i + 1 -- Convert to 1-indexed
    let valuesAtSlot := ls.filterMap fun l =>
      if h : i ≤ l.size then some l[i - 1] else none
    combineSlot valuesAtSlot

-- \* Insert x into log l at position i (`which should be <= Len(l) + 1`)
-- ReplaceItem(l, i, x) ==
--   [ j \in 1..Max({Len(l), i}) |-> IF j = i THEN x ELSE l[j] ]
-- NOTE: This is 1-indexed, and if i = Len(l) + 1, it appends x to the end of l
abbrev ReplaceItem {α : Type u} (l : Array α) (i : Nat) (x : α) :=
  let i := i - 1
  if h : i < l.size then l.set i x else l.push x

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
procedure SendGapCommit (r : replica) {
  let slot := (vLog r).size + 1
  require Leader (vViewID r) = r
  require vReplicaStatus r = StNormal
  vReplicaStatus r := StGapCommit
  vGapCommitReps r := mSet.empty
  vCurrentGapSlot r := slot
  let msgs := replicaEnumerable.allValues.map fun d =>
    Msg.gapCommit d (vViewID r) slot
  Send <| mSet.ofList msgs
}

-- Quorums == {R \in SUBSET(Replicas) : Cardinality(R) * 2 > Cardinality(Replicas)}
ghost relation isQuorum (R : replicaSet) :=
  rSet.count R * 2 > replicaEnumerable.allValues.length

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
  let submsgs := mSet.filter messages fun m =>
    match m with
    | .requestReply _ _ req lsn => req == v && lsn == i
    | _ => false
  ∃ M : { M // mSet.isSubset M submsgs } ,
    let M := M.val
    (isQuorum <| mSet.filterMap (target_set := rSet) M fun m =>
      match m with
      | .requestReply sender .. => some sender
      | _ => none) ∧
    (∃ m1 : { m // m ∈ M }, ∀ m2 : { m // m ∈ M }, (match m1.val, m2.val with
      | .requestReply _ vid1 .., .requestReply _ vid2 .. => decide $ vid1 = vid2
      | _, _ => false) = true) ∧
    (∃ m : { m // m ∈ M }, (match m.val with
      | .requestReply sender vid .. => decide $ sender = Leader vid
      | _ => false) = true)

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
ghost relation Linearizability :=
  let logSlotNums := mSet.toList messages |>.filterMap fun m =>
    match m with
    | .requestReply _ _ _ lsn => some lsn
    | _ => none
  let maxLogPosition := (1 :: logSlotNums).max (List.cons_ne_nil _ _)
  ¬ (∃ v1 v2 : value,
      v1 ≠ v2 ∧
      -- NOTE: Write in this way to allow Lean to synthesize `Decidable` instance
      ∃ i ≤ maxLogPosition, 1 ≤ i ∧ Committed v1 i ∧ Committed v2 i)

-- \* `^\textbf{Client action}^'
-- \* Send a request for value v
-- ClientSendsRequest(v) == /\ Send({[ mtype |-> MClientRequest,
--                                     value |-> v ]})
--                          /\ UNCHANGED << sequencerVars, replicaVars >>
action ClientSendsRequest (v : value) {
  require mSet.count messages ≤ MsgCountLimit
  require v ≠ NoOp
  Send <| mSet.ofList [Msg.clientRequest v]
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
action HandleClientRequest (s : SeqTy maxSeq) {
  require mSet.count messages ≤ MsgCountLimit
  let smn := seqMsgNums s
  let m :| m ∈ messages
  assume m matches .clientRequest ..
  let toSent := replicaEnumerable.allValues.map fun r =>
    Msg.markedClientRequest r m.value s smn
  Send <| mSet.ofList toSent
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
action HandleMarkedClientRequest {
  require mSet.count messages ≤ MsgCountLimit
  let m :| m ∈ messages
  assume m matches .markedClientRequest ..
  let r := m.dest
  let mValue := m.value
  let mSessNum := m.sessNum
  let mSessMsgNum := m.sessMsgNum

  require vReplicaStatus r = StNormal
  -- Normal case: m.sessNum = vViewID[r].sessNum /\ m.sessMsgNum = vSessMsgNum[r]
  if mSessNum = (vViewID r).sessNum ∧ mSessMsgNum = vSessMsgNum r then
    vLog r := (vLog r).push mValue
    vSessMsgNum r := vSessMsgNum r + 1
    let replyMsg := Msg.requestReply r (vViewID r) mValue (vLog r).size
    Send <| mSet.ofList [replyMsg]
  else
    -- SESSION-TERMINATED Case: m.sessNum > vViewID[r].sessNum
    if mSessNum > (vViewID r).sessNum then
      let newViewID : View (SeqTy maxSeq) := {
        sessNum   := mSessNum,
        leaderNum := (vViewID r).leaderNum }
      let viewChangeReqMsgs := replicaEnumerable.allValues.map fun d =>
        Msg.viewChangeReq d newViewID
      Send <| mSet.ofList viewChangeReqMsgs
    -- DROP-NOTIFICATION Case: m.sessNum = vViewID[r].sessNum /\ m.sessMsgNum > vSessMsgNum[r]
    else
      require mSessNum = (vViewID r).sessNum
      require mSessMsgNum > vSessMsgNum r
      let leader := Leader (vViewID r)
      if r = leader then
        SendGapCommit r
      else
        let slotLookupMsg := Msg.slotLookup leader r (vViewID r) (vSessMsgNum r)
        Send <| mSet.ofList [slotLookupMsg]
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
action HandleSlotLookup {
  require mSet.count messages ≤ MsgCountLimit
  let m :| m ∈ messages
  assume m matches .slotLookup ..
  let r := m.dest
  let mSender := m.sender
  let mViewID := m.viewID
  let mSessMsgNum := m.sessMsgNum

  require mViewID = vViewID r
  require Leader (vViewID r) = r
  require vReplicaStatus r = StNormal

  let logSlotNum := (vLog r).size + 1 - (vSessMsgNum r - mSessMsgNum)
  if logSlotNum ≤ (vLog r).size then
    let msg := Msg.markedClientRequest mSender
      ((vLog r)[logSlotNum - 1]!) (vViewID r).sessNum mSessMsgNum
    Send <| mSet.ofList [msg]
  else
    require logSlotNum = (vLog r).size + 1
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
action HandleGapCommit {
  require mSet.count messages ≤ MsgCountLimit
  let m :| m ∈ messages
  assume m matches .gapCommit ..
  let r := m.dest
  let mViewID := m.viewID
  let mSlotNumber := m.slotNumber

  require mViewID = vViewID r
  require mSlotNumber ≤ (vLog r).size + 1
  require (vReplicaStatus r = StNormal) ∨ (vReplicaStatus r = StGapCommit)
  let originalLogSize := (vLog r).size
  vLog r := ReplaceItem (vLog r) mSlotNumber NoOp
  if mSlotNumber > originalLogSize then
    vSessMsgNum r := vSessMsgNum r + 1

  let gapCommitRepMsg := Msg.gapCommitRep
    (Leader (vViewID r)) r (vViewID r) mSlotNumber
  let requestReplyMsg := Msg.requestReply r (vViewID r) NoOp mSlotNumber
  Send <| mSet.ofList [gapCommitRepMsg, requestReplyMsg]
}

ghost relation isViewPromise (r : replica) (M : MsgSet) :=
  (isQuorum <| mSet.map (target_set := rSet) M Msg.sender) ∧
  (∃ n : { n // n ∈ M }, n.val.sender = r)

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
action HandleGapCommitRep {
  require mSet.count messages ≤ MsgCountLimit
  let m :| m ∈ messages
  assume m matches .gapCommitRep ..
  let r := m.dest
  let mViewID := m.viewID
  let mSlotNumber := m.slotNumber

  require vReplicaStatus r = StGapCommit
  require mViewID = vViewID r
  require Leader (vViewID r) = r
  require mSlotNumber = vCurrentGapSlot r
  vGapCommitReps r := mSet.insert m (vGapCommitReps r)
  let gCRs := mSet.filter (vGapCommitReps r) (fun n =>
    match n with
    | .gapCommitRep _ _ vid sn =>
      vid == vViewID r && sn == vCurrentGapSlot r
    | _ => false)
  if isViewPromise r gCRs then
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
action StartLeaderChange (r : replica) {
  require mSet.count messages ≤ MsgCountLimit
  let newViewID : View (SeqTy maxSeq) :=
    { sessNum   := (vViewID r).sessNum,
      leaderNum := (vViewID r).leaderNum + 1 }
  let msgs := replicaEnumerable.allValues.map fun d =>
    Msg.viewChangeReq d newViewID
  Send <| mSet.ofList msgs
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
action HandleViewChangeReq {
  require mSet.count messages ≤ MsgCountLimit
  let m :| m ∈ messages
  assume m matches .viewChangeReq ..
  let r := m.dest
  let mViewID := m.viewID

  let currentViewID := vViewID r
  let newSessNum := max currentViewID.sessNum mViewID.sessNum
  let newLeaderNum := max currentViewID.leaderNum mViewID.leaderNum
  let newViewID : View (SeqTy maxSeq) := { sessNum := newSessNum, leaderNum := newLeaderNum }
  require currentViewID ≠ newViewID
  vReplicaStatus r := StViewChange
  vViewID r := newViewID
  vViewChanges r := mSet.empty
  let viewChangeMsg := Msg.viewChange
    (Leader newViewID) r newViewID (vLastNormView r) (vSessMsgNum r) (vLog r)
  let viewChangeReqMsgs := replicaEnumerable.allValues.map fun d =>
    Msg.viewChangeReq d newViewID
  Send <| mSet.ofList (viewChangeMsg :: viewChangeReqMsgs)
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
action HandleViewChange {
  require mSet.count messages ≤ MsgCountLimit
  let m :| m ∈ messages
  assume m matches .viewChange ..
  let r := m.dest
  let mViewID := m.viewID

  require vViewID r = mViewID
  require vReplicaStatus r = StViewChange
  require Leader (vViewID r) = r
  vViewChanges r := mSet.insert m (vViewChanges r)
  let vCMs := mSet.filter (vViewChanges r) (fun n =>
    match n with
    | .viewChange _ _ vid _ _ _ => vid == vViewID r
    | _ => false)

  if isViewPromise r vCMs then
    -- Find the maximum lastNormal view
    let vCMsList := mSet.toList vCMs
    let normalViews := vCMsList.filterMap fun n =>
      match n with
      | .viewChange _ _ _ ln _ _ => some ln
      | _ => none
    -- This should be unique
    let lastNormal : { v // v ∈ normalViews } :| ∀ v' ∈ normalViews, ViewLe v' lastNormal.val
    let goodLogs := vCMsList.filterMap fun n =>
      match n with
      | .viewChange _ _ _ ln _ log =>
        if ln = lastNormal.val then some log else none
      | _ => none
    let newMsgNum :=
      if lastNormal.val.sessNum = (vViewID r).sessNum then
        let tmp := vCMsList.filterMap fun n =>
          match n with
          | .viewChange _ _ _ ln smn _ =>
            if ln = lastNormal.val then some smn else none
          | _ => none
        tmp.max? |>.getD 0
      else
        0
    let startViewMsgs := replicaEnumerable.allValues.map fun d =>
      Msg.startView d (vViewID r) (CombineLogs goodLogs) newMsgNum
    Send <| mSet.ofList startViewMsgs
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
action HandleStartView {
  require mSet.count messages ≤ MsgCountLimit
  let m :| m ∈ messages
  assume m matches .startView ..
  let r := m.dest
  let mViewID := m.viewID
  let mLog := m.log
  let mSessMsgNum := m.sessMsgNum

  require (ViewLt (vViewID r) mViewID) ∨ (vViewID r = mViewID ∧ vReplicaStatus r = StViewChange)
  vLog r := mLog
  vSessMsgNum r := mSessMsgNum
  vReplicaStatus r := StNormal
  vViewID r := mViewID
  vLastNormView r := mViewID

  let requestReplyMsgs := (List.range mLog.size).map fun i =>
      Msg.requestReply r mViewID (mLog[i]!) (i + 1)
  Send <| mSet.ofList requestReplyMsgs
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
action StartSync (r : replica) {
  require mSet.count messages ≤ MsgCountLimit
  require Leader (vViewID r) = r
  require vReplicaStatus r = StNormal
  vSyncReps r := mSet.empty
  vTentativeSync r := (vLog r).size
  let msgs := replicaEnumerable.allValues.map fun d =>
    Msg.syncPrepare d r (vViewID r) (vSessMsgNum r) (vLog r)
  Send <| mSet.ofList msgs
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
action HandleSyncPrepare {
  require mSet.count messages ≤ MsgCountLimit
  let m :| m ∈ messages
  assume m matches .syncPrepare ..
  let r := m.dest
  let mSender := m.sender
  let mViewID := m.viewID
  let mLog := m.log

  require vReplicaStatus r = StNormal
  require mViewID = vViewID r
  require mSender = Leader (vViewID r)
  -- newLog == m.log \o SubSeq(vLog[r], Len(m.log) + 1, Len(vLog[r]))
  let newLog := mLog ++ (vLog r).extract mLog.size (vLog r).size
  let newMsgNum := vSessMsgNum r + (newLog.size - (vLog r).size)
  vLog r := newLog
  vSessMsgNum r := newMsgNum

  let syncRepMsg := Msg.syncRep mSender r (vViewID r) mLog.size
  let requestReplyMsgs :=
    (List.range newLog.size).map fun i =>
      Msg.requestReply r (vViewID r) (newLog[i]!) (i + 1)
  Send <| mSet.ofList (syncRepMsg :: requestReplyMsgs)
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
action HandleSyncRep {
  require mSet.count messages ≤ MsgCountLimit
  let m :| m ∈ messages
  assume m matches .syncRep ..
  let r := m.dest
  let mViewID := m.viewID

  require mViewID = vViewID r
  require vReplicaStatus r = StNormal
  vSyncReps r := mSet.insert m (vSyncReps r)
  let sRMs := mSet.filter (vSyncReps r) (fun n =>
    match n with
    | .syncRep _ _ vid lsn =>
      vid == vViewID r && lsn == vTentativeSync r
    | _ => false)
  if isViewPromise r sRMs then
    let committedLog := if vTentativeSync r ≥ 1 then
        (vLog r).extract 0 (vTentativeSync r)
      else
        #[]
    let syncCommitMsgs := replicaEnumerable.allValues.map fun d =>
      Msg.syncCommit d r (vViewID r) committedLog
        (vSessMsgNum r - ((vLog r).size - committedLog.size))
    Send <| mSet.ofList syncCommitMsgs
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
  let m :| m ∈ messages
  assume m matches .syncCommit ..
  let r := m.dest
  let mSender := m.sender
  let mViewID := m.viewID
  let mLog := m.log

  require vReplicaStatus r = StNormal
  require mViewID = vViewID r
  require mSender = Leader (vViewID r)

  -- newLog == m.log \o SubSeq(vLog[r], Len(m.log) + 1, Len(vLog[r]))
  let newLog := mLog ++ (vLog r).extract mLog.size (vLog r).size
  let newMsgNum := vSessMsgNum r + (newLog.size - (vLog r).size)
  vLog r := newLog
  vSessMsgNum r := newMsgNum
  vSyncPoint r := mLog.size
}

-- Linearizability
invariant [linearizability] Linearizability

-- SyncSafety
invariant [sync_safety]
  ∀ (r : replica),
    ∀ i < vSyncPoint r,
      Committed ((vLog r)[i]!) (i + 1)

-- NOTE: state constraint not really applicable here

set_option maxHeartbeats 1600000
#gen_spec
#gen_executable

-- #model_check compiled
-- {
--   replica := Fin 3
--   replicaSet := OrdList (Fin 3)
--   value := Fin 6
--   maxSeq := 0
--   MsgSet := OrdList (NOPaxosMsg (Fin 3) (Fin 6) 0)
-- }
-- {
--   NoOp := 0
--   MsgCountLimit := 16
--   ReplicaOrder := #[0, 1, 2]
-- }

-- ================================================================================
end NOPaxos
