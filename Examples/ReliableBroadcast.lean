import LeanSts.State
import LeanSts.TransitionSystem
import LeanSts.Tactic
import LeanSts.BFT.Network

-- https://github.com/verse-lab/verify-ABC-in-Coq/blob/main/Protocols/RB/Protocol.v

section ReliableBroadcast
variable {Address Round Value : Type}
variable [dec_addr : DecidableEq Address] [dec_round : DecidableEq Round] [dec_value : DecidableEq Value]

def InternalTransition := Round

inductive Message
  | InitialMsg (r : Round) (v : Value)
  | EchoMsg (orig : Address) (r : Round) (v : Value)
  | VoteMsg (orig : Address) (r : Round) (v : Value)
deriving DecidableEq

structure NodeState :=
  id : Address
  sent : Round → Bool
  echoed : (Address × Round) → Option Value
  voted : (Address × Round) → Option Value
  msgCount : @Message Address Round Value → List Address
  output : (Address × Round) → List Value

def init (id : Address) : @NodeState Address Round Value := {
  id := id
  sent := λ _ => false
  echoed := λ _ => none
  voted := λ _ => none
  msgCount := λ _ => []
  output := λ _ => []
}

def procInt (st : @NodeState Address Round Value) (r : @InternalTransition Round) :
  (@NodeState Address Round Value) × List (Packet Address (@Message Address Round Value)) := sorry

def procMsg (st : @NodeState Address Round Value) (src : Address) (msg : @Message Address Round Value) :
  (@NodeState Address Round Value) × List (Packet Address (@Message Address Round Value)) := sorry

instance RBProtocol : @NetworkProtocol Address (@Message Address Round Value) (@NodeState Address Round Value) (@InternalTransition Round) :=
  ⟨init, procInt, procMsg⟩


def RBNetworkState := @AsynchronousNetwork.World Address (Packet Address (@Message Address Round Value)) (@NodeState Address Round Value)
instance RBAdversary : @ByzantineAdversary Address (@Message Address Round Value) (@NetworkState Address (Packet Address (@Message Address Round Value)) (@NodeState Address Round Value)) := sorry

-- #check AsynchronousNetwork.transition
-- #check (@defaultNetworkState _ _ _ _ RBProtocol).default

instance RBAsyncNetwork
  : RelationalTransitionSystem (@RBNetworkState Address Round Value) where
  init  := λ s => s = (@defaultNetworkState _ _ _ _ RBProtocol).default
  next  := λ w w' => ∃
            (s : AsynchronousNetwork.step)
            (_ : @AsynchronousNetwork.transition _ _ _ _ _ _  RBProtocol RBAdversary s w w'), True
            -- (t : @AsynchronousNetwork.transition Address (@Message Address Round Value) (@NodeState Address Round Value) (@InternalTransition Round) _ _  RBProtocol byz
            --     s w w'), True
  safe := λ _ => True
  inv  := λ _ => True

-- #check (@invInit _ RBAsyncNetwork)

namespace RBProofs

theorem initInv : (@invInit (@RBNetworkState Address Round Value) RBAsyncNetwork) := by {
  simp [invInit, RelationalTransitionSystem.init, RelationalTransitionSystem.inv]
}

end RBProofs

end ReliableBroadcast
