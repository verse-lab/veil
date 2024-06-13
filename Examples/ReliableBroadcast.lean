import LeanSts.State
import LeanSts.TransitionSystem
import LeanSts.Tactic
import LeanSts.BFT.Network

-- https://github.com/verse-lab/verify-ABC-in-Coq/blob/main/Protocols/RB/Protocol.v
-- https://decentralizedthoughts.github.io/2020-09-19-living-with-asynchrony-brachas-reliable-broadcast/

section ReliableBroadcast
variable {Address Round Value : Type}
variable [dec_addr : DecidableEq Address] [dec_round : DecidableEq Round] [dec_value : DecidableEq Value]

def InternalTransition := Round

inductive Message
  | InitialMsg (r : Round) (v : Value)
  /-- The `originator` is the leader, i.e. the party that initiates the broadcast.
    It is NOT the sender of the message. -/
  | EchoMsg (originator : Address) (r : Round) (v : Value)
  /-- The `originator` is the leader, i.e. the party that initiates the broadcast.
    It is NOT the sender of the message. -/
  | VoteMsg (originator : Address) (r : Round) (v : Value)
deriving DecidableEq

structure NodeState :=
  /-- This node's address -/
  id : Address
  /-- The set of all nodes -/
  allNodes : List Address

  sent : Round → Bool
  echoed : (Address × Round) → Option Value
  voted : (Address × Round) → Option Value
  msgReceivedFrom : (@Message Address Round Value) → List Address
  output : (Address × Round) → List Value

def RBNetworkState := @AsynchronousNetwork.World Address (Packet Address (@Message Address Round Value)) (@NodeState Address Round Value)
instance RBAdversary
  (f : ℕ)
  (nodes : {ns : List Address // List.Nodup ns ∧ 0 < List.length ns ∧ f < List.length ns})
  (isByz : {isC : Address → Bool // List.length (List.filter isC nodes.val) ≤ f})
  :
  @NonadaptiveByzantineAdversary Address (Packet Address (@Message Address Round Value)) (@NetworkState Address (Packet Address (@Message Address Round Value)) (@NodeState Address Round Value)) where
  setting := {
    N := List.length nodes.val,
    f := f,
    nodes := ⟨(Multiset.ofList nodes.val), by aesop⟩

    N_gt_0 := by aesop
    f_lt_N := by aesop
    N_nodes := by aesop
  }
  /- Unforgeable channels assumption: the adversary can produce ANY packet
    as long as it does not forge the origin. It cannot send packets purporting
    to be from honest nodes. -/
  constraint := ⟨(λ pkt _ => isByz.val pkt.src)⟩
  isByzantine := isByz
  byz_lte_f := by { dsimp [Finset.filter] ; aesop }


def initLocalState (id : Address) (nodes : List Address) : @NodeState Address Round Value := {
  id := id
  allNodes := nodes
  sent := λ _ => false
  echoed := λ _ => none
  voted := λ _ => none
  msgReceivedFrom := λ _ => []
  output := λ _ => []
}

def procInt (inputValue : Address → Value) (st : @NodeState Address Round Value) (r : @InternalTransition Round) :
  (@NodeState Address Round Value) × List (Packet Address (@Message Address Round Value)) :=
  if st.sent r then
    (st, [])
  else
    let st' := { st with sent := st.sent[r ↦ true] };
    let msg := Message.InitialMsg r (inputValue st.id);
    let pkts := Packet.broadcast st.id st.allNodes msg
    (st', pkts)

/-- Internal message handler for Reliable Broadcast. Returns `none` if nothing to do. -/
def handleMessage (st : @NodeState Address Round Value) (src : Address) (msg : @Message Address Round Value) :
  Option ((@NodeState Address Round Value) × List (Packet Address (@Message Address Round Value))) :=
  match msg with
  | Message.InitialMsg r v =>
    if let .none := st.echoed (src, r) then
      let st' := {st with echoed := st.echoed[(src, r) ↦ some v]};
      let msg := Message.EchoMsg st.id r v;
      let pkts := Packet.broadcast st.id st.allNodes msg
      (st', pkts)
    else none
  /- We keep track of how many times we've seen  -/
  | _ =>
    let alreadyReceived := st.msgReceivedFrom msg;
    if src ∈ alreadyReceived then
      none
    else
      let msgReceivedFrom' := st.msgReceivedFrom[msg ↦ src :: alreadyReceived]
      let st' := {st with msgReceivedFrom := msgReceivedFrom'}
      .some (st', [])

local notation "RBMessage" => (@Message Address Round Value)
local notation "RBState" => (@NodeState Address Round Value)
local notation "RBPacket" => (Packet Address RBMessage)

-- The number of nodes in the network now can only be calculated from the state
def numNodes (st : RBState) : ℕ := st.allNodes.length

def byzThres (st : RBState) : ℕ := (numNodes st - 1) / 3

def thresEcho4Vote (st : RBState) := numNodes st - byzThres st
def thresVote4Vote (st : RBState) := numNodes st - (byzThres st + byzThres st)
def thresVote4Output (st : RBState) := numNodes st - byzThres st

def checkVoteCondition (st : RBState) (msg : RBMessage) : Bool :=
  match msg with
  | Message.EchoMsg q r _ =>
    Option.isNone (st.voted (q, r)) && (thresEcho4Vote st ≤ List.length (st.msgReceivedFrom msg))
  | Message.VoteMsg q r _ =>
    Option.isNone (st.voted (q, r)) && (thresVote4Vote st ≤ List.length (st.msgReceivedFrom msg))
  | _ => false

def updateVotedByMessage (st : RBState) (msg : RBMessage) : RBState × List RBPacket :=
  match msg with
  | Message.EchoMsg q r v | Message.VoteMsg q r v =>
    ({st with voted := st.voted[(q, r) ↦ some v]}, Packet.broadcast st.id st.allNodes (Message.VoteMsg q r v))
  | _ => (st, [])

def tryUpdateOutputByMessage (st : RBState) (msg : RBMessage) : RBState :=
  if let Message.VoteMsg q r v := msg then
    if thresVote4Output st ≤ List.length (st.msgReceivedFrom msg) then
      let l := st.output (q, r)
      {st with output := st.output[(q, r) ↦ l.insert v]}
    else
      st
  else
    st

def routineCheck (st : RBState) (msg : RBMessage) : RBState × List RBPacket :=
  -- let (st', pkts) := if checkVoteCondition st msg then updateVotedByMessage st msg else (st, [])
  -- let st'' := tryUpdateOutputByMessage st' msg
  -- (st'', pkts)

  -- Need to make the if be the outermost thing?
  if checkVoteCondition st msg then
    let (st', pkts) := updateVotedByMessage st msg
    let st'' := tryUpdateOutputByMessage st' msg
    (st'', pkts)
  else
    let st'' := tryUpdateOutputByMessage st msg
    (st'', [])

def procMsg (st : @NodeState Address Round Value) (src : Address) (msg : @Message Address Round Value) :
  (@NodeState Address Round Value) × List (Packet Address (@Message Address Round Value)) :=
  match handleMessage st src msg with
  | some (st', pkts) =>
    match msg with
    | Message.InitialMsg _ _ => (st', pkts)
    | _ =>
      let (st'', pkts') := routineCheck st' msg
      (st'', pkts ++ pkts')
  | none => (st, [])

instance RBProtocol (nodes : List Address) (inputValue : Address → Value) :
  @NetworkProtocol Address (@Message Address Round Value) (@NodeState Address Round Value) (@InternalTransition Round) :=
  ⟨λ id => initLocalState id nodes, procInt inputValue, procMsg⟩

instance RBAsyncNetwork
  (f : ℕ) /- Number of faults-/
  (nodes : {ns : List Address // List.Nodup ns ∧ 0 < List.length ns ∧ f < List.length ns})
  (isByz : {isC : Address → Bool // List.length (List.filter isC nodes.val) ≤ f}) /- Oracle for which nodes are corrupt -/
  (inputValue : Address → Value) /- Oracle for value broadcast by the leader -/
  : RelationalTransitionSystem (@RBNetworkState Address Round Value) where
  init  := λ s => s = @AsynchronousNetwork.init _ _ _ _ (RBProtocol nodes inputValue) nodes
  next  := λ w w' => ∃
            (s : AsynchronousNetwork.step)
            (_ : @AsynchronousNetwork.transition _ _ _ _ _ _  (RBProtocol nodes inputValue) (RBAdversary f nodes isByz) s w w'), True
  safe := λ _ => True
  inv  := λ _ => True

namespace RBProofs

theorem initInv : (@invInit (@RBNetworkState Address Round Value) (RBAsyncNetwork f nodes isByz inputValue)) := by {
  simp [invInit, RelationalTransitionSystem.init, RelationalTransitionSystem.inv]
}

local notation "RBstep" => (@AsynchronousNetwork.step (@RBNetworkState Address Round Value) RBMessage RBPacket InternalTransition)

section Test

variable (f : ℕ)
  (nodes : {ns : List Address // List.Nodup ns ∧ 0 < List.length ns ∧ f < List.length ns})
  (isByz : {isC : Address → Bool // List.length (List.filter isC nodes.val) ≤ f})
  (inputValue : Address → Value)

local notation "RBP" => (@RBProtocol _ Round _ _ _ _ nodes inputValue)
local notation "RBAdv" => (RBAdversary f nodes isByz)
local notation "RBtransition" => (@AsynchronousNetwork.transition _ _ _ _ _ _ RBP RBAdv)

local infixl:50 "@" => NetworkState.localState

example : ∀ s (w w' : RBNetworkState), RBtransition s w w' →
  ∀ n, (w @ n).id = (w' @ n).id :=
  by
    intros s w w' h n0
    rcases h with ⟨Es, Ew⟩ | ⟨⟨ns, nd, m, used⟩, Es, hin, hnonbyz, E⟩ | ⟨n, itr, Es, hnonbyz, E⟩ | ⟨p, Es, hbyz, Ew'⟩ <;> subst Es
    · subst Ew ; rfl
    · simp [NonadaptiveByzantineAdversary.isByzantine] at hnonbyz
      simp only [NetworkPacket.dst] at E -- seems like simp will separate the pair automatically
      subst E
      have ⟨⟨stf, psf⟩, Ef⟩ : ∃ a, procMsg (w.localState nd) ns m = a := Exists.intro _ (Eq.refl _)
      rw [Ef] ; dsimp
      split_ifs with Etmp <;> try rfl
      subst Etmp
      dsimp [procMsg] at Ef

      split at Ef
      · rename_i _ st' ps E
        split at Ef
        · rename_i _ r v
          simp at Ef ; rcases Ef with ⟨E0, E1⟩ ; subst E0 E1
          dsimp [handleMessage] at E
          split at E <;> try (solve | simp_all)
          · simp at E ; rcases E with ⟨E0, E1⟩ ; subst E0 E1
            rfl
        · rename_i __1
          simp at Ef ; rcases Ef with ⟨E0, E1⟩ ; subst E0 E1
          dsimp [handleMessage] at E
          split at E <;> try (solve | simp_all)
          · rename_i __2
            split_ifs at E with hnotin_ <;> try (solve | simp_all)
            · simp at E ; rcases E with ⟨E0, E1⟩ ; subst E0 E1

              dsimp [routineCheck]
              split_ifs with Echeck
              · dsimp [checkVoteCondition] at Echeck
                split at Echeck <;> try (solve | simp_all)
                · rename_i __3 q r v
                  dsimp [tryUpdateOutputByMessage]
                  dsimp [updateVotedByMessage]
                · rename_i __3 q r v
                  dsimp [tryUpdateOutputByMessage]
                  split
                  · dsimp [updateVotedByMessage]
                  · dsimp [updateVotedByMessage]
              · dsimp [tryUpdateOutputByMessage]
                -- split -- why does not work?
                split_ifs <;> split <;> rfl
      · simp at Ef ; rcases Ef with ⟨E0, E1⟩ ; subst E0 E1
        rfl
    · simp [NonadaptiveByzantineAdversary.isByzantine] at hnonbyz
      dsimp at E
      subst E
      have ⟨⟨st, ps⟩, E⟩ : ∃ a, (procInt inputValue (w.localState n) itr) = a := Exists.intro _ (Eq.refl _)
      rw [E] ; dsimp
      split_ifs with Etmp <;> try rfl
      subst Etmp
      dsimp [procInt] at E

      split_ifs at E <;> try (solve | simp_all)
      · simp at E ; rcases E with ⟨E0, E1⟩ ; subst E0 E1
        rfl
    · subst Ew'
      simp [AdversaryConstraint.canProducePacket] at hbyz
      dsimp

end Test

end RBProofs

end ReliableBroadcast
