import Examples.DAG.DAGConstruction

namespace DAGRider

variable {NodeID Block : Type} [DecidableEq NodeID] [Inhabited NodeID] [DecidableEq Block] [Inhabited Block]
local notation "Vertex" => @Vertex NodeID Block
abbrev Round := DAGConstruction.Round

-- local notation "DAGConstruct" => @DAGConstruction.DAGConstruct NodeID Block _ _
-- FIXME: we are implicitly assuming FIFO channels, which is probably what we want in any case

inductive Input where
  | atomicBroadcast (r : Round) (bl : Block)
local notation "Input" => @Input Block

abbrev InputEvent := Input ⊕ DAGConstruction.Output

abbrev InternalEvent := Unit

abbrev OutputEvent := @DAGConstruction.Input Block

local notation "InputEvent" => @InputEvent Block
local notation "OutputEvent" => @OutputEvent Block
local notation "InternalEvent" => @InternalEvent

def Message := Unit

local notation "Message" => @Message
local notation "Packet" => @Packet NodeID Message
local notation "Network" => @Network NodeID

structure NodeState :=
  /-- This node's ID -/
  id : NodeID

  decidedWave : Nat
  deliveredVertices : List Vertex
  leadersStack : List Vertex
local notation "NodeState" => @NodeState NodeID Block

-- def getWaveVertexLeader (w : Round)

def procInp (net : Network) (st : NodeState) (t : InputEvent) : NodeState × List Packet × List InternalEvent × List OutputEvent :=
  match t with
  | .inl (.atomicBroadcast r bl) =>
    (st, [], [], [.enqueueBlock bl])
  | .inr (.waveReady round) =>
    sorry
end DAGRider
