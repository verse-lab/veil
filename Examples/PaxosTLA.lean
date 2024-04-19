import LeanSts.State
import LeanSts.TransitionSystem
import LeanSts.Tactics
import Mathlib.Tactic

-- From https://github.com/tlaplus/DrTLAPlus/blob/master/Paxos/Paxos.tla

section Paxos

class Quorum (acceptor : outParam Type) (quorum : Type):=
  -- relation
  member (a : acceptor) (q : quorum) : Prop
  -- axioms
  quorum_intersection :
    ∀ (q1 q2 : quorum), ∃ (a : acceptor), member a q1 ∧ member a q2

instance [Quorum acceptor quorum] :
  Membership acceptor quorum := ⟨Quorum.member⟩

variable {acceptor : Type} [DecidableEq acceptor] [Inhabited acceptor]
variable {value : Type} [DecidableEq value]
variable {quorum : Type} [DecidableEq quorum] [Quorum acceptor quorum]
variable {ballot : Type} [DecidableEq ballot] [LT ballot] [LE ballot] [OfNat ballot 0]

inductive Message where
  | msg_1a (b : ballot)
  | msg_1b (a : acceptor) (b : ballot) (max_ballot : Option ballot) (value : Option value)
  | msg_2a (b : ballot) (v : value)
  | msg_2b (a : acceptor) (b : ballot) (v : value)

namespace Message
  def bal : (@Message acceptor value ballot) → ballot
    | msg_1a b => b
    | msg_1b _ b _ _ => b
    | msg_2a b _ => b
    | msg_2b _ b _ => b

  def maxVBal : (@Message acceptor value ballot) → Option ballot
    | msg_1b _ _ mb _ => mb
    | _ => none

  def maxVal : (@Message acceptor value ballot) → Option value
    | msg_1b _ _ _ v => v
    | _ => none

  def acc : (@Message acceptor value ballot) → acceptor
    | msg_1b a _ _ _ => a
    | msg_2b a _ _ => a
    | _ => default
end Message

structure GlobalState where
  /-- The set of messages that have been sent -/
  msgs : Set (@Message acceptor value ballot)
  /-- `maxBal[a]` is the highest-number ballot acceptor `a` has participated in -/
  maxBal : acceptor → Option ballot
  /-- ⟨maxVBal[a], maxVal[a]⟩ is the vote with the largest round number cast by `a` -/
  maxVBal : acceptor → Option ballot
  maxVal : acceptor → Option value

def initialState? (st : @GlobalState acceptor value ballot) : Prop :=
  (∀ (msg : Message), msg ∉ st.msgs) ∧
  (∀ (a : acceptor), st.maxBal a = none) ∧
  (∀ (a : acceptor), st.maxVBal a = none) ∧
  (∀ (a : acceptor), st.maxVal a = none)

-- State update helpers
def send (st st' : @GlobalState acceptor value ballot) (msg : Message) :=
  st'.msgs = st.msgs.insert msg

-- Transitions

/--
  Phase 1a: A leader selects a ballot number b and sends a 1a message with ballot
  b to a majority of acceptors. It can do this only if it has not already sent a
  1a message for ballot b.
-/
def phase_1a : RelationalTransitionSystem.action (@GlobalState acceptor value ballot) :=
  λ (st st' : @GlobalState acceptor value ballot) =>
    ∃ (b : ballot),
      Message.msg_1a b ∉ st.msgs ∧
      send st st' (Message.msg_1a b)

/--
  Phase 1b: If an acceptor receives a 1a message with ballot b greater than that
  of any 1a message to which it has already responded, then it responds to the
  request with a promise not to accept any more proposals for ballots numbered
  less than b and with the highest-numbered ballot (if any) for which it has
  voted for a value and the value it voted for in that ballot. That promise is
  made in a 1b message.
-/
def phase_1b : RelationalTransitionSystem.action (@GlobalState acceptor value ballot) :=
  λ (st st' : @GlobalState acceptor value ballot) =>
    ∃ (a : acceptor),
      ∃ (m : Message) (b : ballot), -- b = `m.bal`
        m ∈ st.msgs ∧
        m = Message.msg_1a b ∧
        m.bal > st.maxBal a ∧
        st'.maxBal = st.maxBal[a ↦ b]

/--
  Phase 2a: If the leader receives a response to its 1b message (for ballot b)
  from a quorum of acceptors, then it sends a 2a message to all acceptors for a
  proposal in ballot b with a value v, where v is the value of the
  highest-numbered proposal among the responses, or is any value if the
  responses reported no proposals. The leader can send only one 2a message for
  any ballot.
-/
def phase_2a : RelationalTransitionSystem.action (@GlobalState acceptor value ballot) :=
  λ (st st' : @GlobalState acceptor value ballot) =>
    ∃ (b : ballot),
      (∀ (v : value), Message.msg_2a b v ∉ st.msgs) ∧
      (∃ (v : value),
        (∃ (Q : quorum),
          (∃ (S : Set Message), -- \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)}
            S ⊆ { m ∈ st.msgs | ∃ a' mb mv, m = Message.msg_1b a' b mb mv} ∧
            (∀ a ∈ Q, ∃ m ∈ S, m.acc = a ∧
              (∀ m ∈ S, m.maxVBal = none) ∨
              (∃ (c : ballot), 0 ≤ c ∧ c < b ∧ -- \E c \in 0..(b-1)
                -- \A m \in S : m.maxVBal =< c
                (∀ m ∈ S, ∀ (isS : m.maxVBal.isSome = true), m.maxVBal.get isS ≤ c) ∧
                -- \E m \in S : /\ m.maxVBal = c /\ m.maxVal = v
                (∃ m ∈ S, ∀ (isS : m.maxVBal.isSome = true), ∀ (isS' : m.maxVal.isSome = true),
                  m.maxVBal.get isS = c ∧ m.maxVal.get isS' = v)))))
      ∧ send st st' (Message.msg_2a b v))

/--
  Phase 2b: If an acceptor receives a 2a message for a ballot numbered b, it
  votes for the message's value in ballot b unless it has already responded to a
  1a request for a ballot number greater than or equal to b.
-/
def phase_2b : RelationalTransitionSystem.action (@GlobalState acceptor value ballot) :=
  λ (st st' : @GlobalState acceptor value ballot) =>
    ∃ (a : acceptor),
      ∃ m ∈ st.msgs, ∃ b v, m = Message.msg_2a b v ∧
        send st st' (Message.msg_2b a b v) ∧
        st'.maxVBal = st.maxVBal[a ↦ b] ∧
        st'.maxBal = st.maxBal[a ↦ b] ∧
        st'.maxVal = st.maxVal[a ↦ v]

end Paxos
