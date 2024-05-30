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
instance RBAdversary : @ByzantineAdversary Address (@Message Address Round Value) (@NetworkState Address (Packet Address (@Message Address Round Value)) (@NodeState Address Round Value)) :=
  sorry

def init (id : Address) (nodes : List Address) : @NodeState Address Round Value := {
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

def procMsg (st : @NodeState Address Round Value) (src : Address) (msg : @Message Address Round Value) :
  (@NodeState Address Round Value) × List (Packet Address (@Message Address Round Value)) := sorry

instance RBProtocol (nodes : List Address) (inputValue : Address → Value) :
  @NetworkProtocol Address (@Message Address Round Value) (@NodeState Address Round Value) (@InternalTransition Round) :=
  ⟨λ id => init id nodes, procInt inputValue, procMsg⟩

instance RBAsyncNetwork (nodes : List Address) (inputValue : Address → Value)
  : RelationalTransitionSystem (@RBNetworkState Address Round Value) where
  init  := λ s => s = @AsynchronousNetwork.init _ _ _ _ (RBProtocol nodes inputValue) nodes
  next  := λ w w' => ∃
            (s : AsynchronousNetwork.step)
            (_ : @AsynchronousNetwork.transition _ _ _ _ _ _  (RBProtocol nodes inputValue) RBAdversary s w w'), True
  safe := λ _ => True
  inv  := λ _ => True

namespace RBProofs

theorem initInv : (@invInit (@RBNetworkState Address Round Value) (RBAsyncNetwork nodes inputValue)) := by {
  simp [invInit, RelationalTransitionSystem.init, RelationalTransitionSystem.inv]
}

end RBProofs

end ReliableBroadcast
