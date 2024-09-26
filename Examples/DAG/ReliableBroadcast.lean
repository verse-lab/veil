import LeanSts.State
import LeanSts.BFT.Network

namespace ReliableBroadcast

variable {NodeID Value : Type} [DecidableEq NodeID] [DecidableEq Value]

abbrev Round := Nat
local notation "InstanceID" => (NodeID × Round)

/- External protocols interact with this one by issuing (`broadcast`)
   inputs and handling (`deliver`) outputs of this protocol. -/

inductive InputEvent where
  | broadcast (inst : InstanceID) (v : Value)

inductive OutputEvent where
  | deliver (inst : InstanceID) (v : Value)

inductive InternalEvent where
  | checkCounters (inst : InstanceID) (v : Value)

local notation "InputEvent" => @InputEvent NodeID Value
local notation "OutputEvent" => @OutputEvent NodeID Value
local notation "InternalEvent" => @InternalEvent NodeID Value

inductive Message where
  /-- Message to indicate the initiation of a broadcast. -/
  | initMsg (inst : InstanceID) (v : Value)
  | echoMsg (inst : InstanceID) (v : Value)
  | voteMsg (inst : InstanceID) (v : Value)
deriving DecidableEq

local notation "Message" => @Message NodeID Value

def Message.instanceID : Message → InstanceID
  | Message.initMsg inst _ => inst
  | Message.echoMsg inst _ => inst
  | Message.voteMsg inst _ => inst

structure NodeState :=
  /-- This node's ID -/
  id : NodeID

  /-- Has this node broadcast a vertex in round `r`? -/
  haveBroadcast : Round → Bool
  /-- What value did we echo in the protocol instance?-/
  haveEchoed : InstanceID → Option Value
  /-- What value did we vote for in the protocol instance?-/
  haveVoted : InstanceID → Option Value
  /-- What value have we delivered (output) in the protocol instance?-/
  haveDelivered : InstanceID → Option Value

  /-- Keep track of echoes. -/
  seenEcho : InstanceID → Value → List NodeID
  /-- Keep track of votes. -/
  seenVote : InstanceID → Value → List NodeID

local notation "NodeState" => @NodeState NodeID Value

def initLocalState (id : NodeID) : NodeState := {
  id := id
  haveBroadcast := fun _ => false
  haveEchoed := fun _ => none
  haveVoted := fun _ => none
  haveDelivered := fun _ => none
  seenEcho := fun _ _ => []
  seenVote := fun _ _ => []
}

local notation "Packet" => @Packet NodeID Message
local notation "Network" => @Network NodeID

abbrev numNodes (net : Network) : ℕ := net.length
abbrev byzThres (net : Network) : ℕ := (numNodes net) / 3
/-- `n - f ≥ 2f + 1`-/
def threshEcho4Vote (net : Network) : ℕ := numNodes net - byzThres net
/-- `n - 2f ≥ f + 1`-/
def thresVote4Vote (net : Network) : ℕ := numNodes net - 2 * byzThres net
/-- `n - f ≥ 2f + 1`-/
def thresVote4Deliver (net : Network) : ℕ := numNodes net - byzThres net

def procInp (net : Network) (st : NodeState) (t : InputEvent) : NodeState × List Packet × List InternalEvent × List OutputEvent :=
  match t with
  | .broadcast (src, r) v =>
    if st.haveBroadcast r || src != st.id then (st, [], [], []) else
    let st' := { st with haveBroadcast := st.haveBroadcast[r ↦ true]};
    let msg := Message.initMsg (src, r) v;
    (st', Packet.broadcast st.id net msg, [], [])

def procInt (net : Network) (st : NodeState) (t : InternalEvent) : NodeState × List Packet × List InternalEvent × List OutputEvent :=
  match t with
  | .checkCounters inst v =>
    -- Do we have enough echoes to vote?
    let echoesToVote := (st.seenEcho inst v).length ≥ threshEcho4Vote net;
    -- Do we have enough votes to vote?
    let votesToVote := (st.seenVote inst v).length ≥ thresVote4Vote net;
    -- Do we have enough votes to deliver?
    let votesToDeliver := (st.seenVote inst v).length ≥ thresVote4Deliver net;
    -- Make the required changes to the state
    let shouldVote := (st.haveVoted inst).isNone && (echoesToVote || votesToVote);
    let st' := if shouldVote then { st with haveVoted := st.haveVoted[inst ↦ v] } else st;
    let pkts' := if shouldVote then (Packet.broadcast st.id net (Message.voteMsg inst v)) else [];

    let shouldDeliver := (st.haveDelivered inst).isNone && votesToDeliver;
    let st' := if shouldDeliver then { st' with haveDelivered := st'.haveDelivered[inst ↦ v] } else st';
    let ev' := if shouldDeliver then [.deliver inst v] else [];

    (st', pkts', [], ev')

def procMsg (net : Network) (st : NodeState) (src : NodeID) (msg : Message) : NodeState × List Packet × List InternalEvent × List OutputEvent :=
  match msg with
  | .initMsg inst v =>
    if let .none := st.haveEchoed inst then
      let st' := { st with haveEchoed := st.haveEchoed[inst ↦ v] };
      let msg := Message.echoMsg inst v;
      (st', Packet.broadcast st.id net msg, [], [])
    else (st, [], [], [])
  | .echoMsg inst v =>
    let recvFrom := st.seenEcho inst v;
    if src ∈ recvFrom then (st, [], [], []) else
    let seenEcho' := src :: (st.seenEcho inst v);
    let st' := { st with seenEcho := st.seenEcho[inst, v ↦ seenEcho'] };
    (st', [], [.checkCounters inst v], [])
  | .voteMsg inst v =>
    let recvFrom := st.seenVote inst v;
    if src ∈ recvFrom then (st, [], [], []) else
    let seenVote' := src :: (st.seenVote inst v);
    let st' := { st with seenVote := st.seenVote[inst, v ↦ seenVote'] };
    (st', [], [.checkCounters inst v], [])

-- TODO: want to prove the correctness of this by refinement of the decidable protocol

instance RB : @NetworkProtocol NodeID NodeState InputEvent InternalEvent OutputEvent Message := {
  localInit := initLocalState,
  procInput := procInp,
  procInternal := procInt,
  procMessage := procMsg
}

end ReliableBroadcast
