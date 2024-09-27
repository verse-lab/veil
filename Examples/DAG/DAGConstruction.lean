import Examples.DAG.DAG
import Examples.DAG.ReliableBroadcast

/- Algorithm 2 in the "All You Need is DAG" (DAG Rider) paper.-/
namespace DAGConstruction

variable {NodeID Block : Type} [DecidableEq NodeID] [Inhabited NodeID] [DecidableEq Block] [Inhabited Block]
local notation "Vertex" => @Vertex NodeID Block
local notation "Set" => List
local notation "DAG" => Array (Set Vertex)
abbrev Round := ReliableBroadcast.Round

local notation "RB" => @ReliableBroadcast.RB NodeID Vertex _ _
-- TODO: need some way to feed input into this protocol instance

inductive Input where
  | enqueueBlock (bl : Block)
local notation "Input" => @Input Block

abbrev InputEvent := Input ⊕ NetworkProtocol.OutputEvent RB

inductive InternalEvent where
  /-- Run a loop beginning at L6 and ending at L13 (inclusive) -/
  | runMainLoop
  /-- Run the code from L14 to L15 -/
  | createNewVertex

inductive Output where
  | waveReady (round : Round)

abbrev OutputEvent := NetworkProtocol.InputEvent RB ⊕ Output

local notation "InputEvent" => @InputEvent NodeID Block _
local notation "OutputEvent" => @OutputEvent NodeID Block _
local notation "InternalEvent" => @InternalEvent

/-- DAG construction is a purely local computation. All communication is via RB. -/
def Message := Unit

local notation "Message" => @Message
local notation "Packet" => @Packet NodeID Message
local notation "Network" => @Network NodeID

structure NodeState :=
  /-- This node's ID -/
  id : NodeID

  /-- An array of sets of vertices. -/
  dag : DAG
  /-- Enqueues valid blocks of transactions from clients -/
  blocksToPropose : Std.Queue Block

  /-- The round number. -/
  round : Round
  /-- Buffer of vertices to include in the DAG. A vertex can be added
  once the DAG contains all the vertices `v` has a strong edge or weak
  edge to. -/
  buffer : List Vertex

local notation "NodeState" => @NodeState NodeID Block

def initLocalState (id : NodeID) : NodeState := {
  id := id
  -- FIXME: spec says need to have 2f + 1 pre-defined vertices at round 0
  dag := #[]
  blocksToPropose := Std.Queue.empty
  round := 0
  buffer := []
}

/-- `n - f ≥ 2f + 1`-/
abbrev numNodes (net : Network) : ℕ := net.length
abbrev byzThres (net : Network) : ℕ := (numNodes net) / 3
/-- `n - f ≥ 2f + 1`-/
def threshVerticesToAdvance (net : Network) : ℕ := numNodes net - byzThres net

/-- We have all of `v`'s predecessors when all of its strong and weak
edges are in the DAG. L7 in Algorithm 2.-/
@[inline] def havePredecessors (st : NodeState) (v : Vertex) : Bool :=
  (v.strongEdges ∪ v.weakEdges).all st.dag.allVertices.contains

/-- Add complete buffer vertices up to round `r` to the dag. L6-9 in
    Algorithm 2.-/
def addBufferVerticesToDag (st : NodeState) (r : Round): NodeState :=
  let (vertices, buffer') := st.buffer.partition (fun v => v.round ≤ r && havePredecessors st v)
  let dag' := vertices.foldl (λ dag v => dag.addVertex v) st.dag
  { st with dag := dag', buffer := buffer' }

/-- Add weak eges to all unconnected vertices in the past. -/
def setWeakEdges (st : NodeState) (v : Vertex) (r : Round) : Set Vertex :=
  st.dag.allVertices.filter (λ u => 0 < u.round && u.round < r - 1 && !(DAG.path v u))
local notation "setWeakEdges" => @setWeakEdges NodeID Block _ _

def procInp (net : Network) (st : NodeState) (t : InputEvent) : NodeState × List Packet × List InternalEvent × List OutputEvent :=
  match t with
  | .inl $ .enqueueBlock bl =>
    let st := { st with blocksToPropose := st.blocksToPropose.enqueue bl }
    (st, [], [], [])
  -- upon `r_deliver`
  | .inr $ .deliver (_src, _r) v =>
    if v.strongEdges.length > threshVerticesToAdvance net then
      -- FIXME: check that `v.source = src` and `v.round = r`?
      let st := { st with buffer := v :: st.buffer }
      (st, [], [], [])
    else
      (st, [], [], [])

-- TODO: need a way to indicate initial InternalEvent queue when setting up a protocol
def procInt (net : Network) (st : NodeState) (t : InternalEvent) : NodeState × List Packet × List InternalEvent × List OutputEvent :=
  match t with
  | .runMainLoop =>
    let r := st.round
    -- L6-9
    let st := addBufferVerticesToDag st r
    if st.dag[r]!.length ≥ threshVerticesToAdvance net then
      let output := if r % 4 == 0 then [Sum.inr $ Output.waveReady r] else []
      let st := { st with round := r + 1 }
      (st, [], [.createNewVertex], output)
    else
      (st, [], [.runMainLoop], [])
  | .createNewVertex =>
    -- "wait until ¬ blocksToPropose.empty"
     match st.blocksToPropose.dequeue? with
     | none => (st, [], [.createNewVertex], [])
     | some (bl, blocksToPropose') =>
        let r := st.round
        let strongEdges := st.dag[r - 1]!
        let weakEdges := setWeakEdges st (.V r st.id bl [] strongEdges) r
        let v := .V r st.id bl weakEdges strongEdges
        let st := { st with blocksToPropose := blocksToPropose' }
        (st, [], [.runMainLoop], [Sum.inl $ .broadcast (st.id, r) v])

def procMsg (_net : Network) (st : NodeState) (_src : NodeID) (_msg : Message) : NodeState × List Packet × List InternalEvent × List OutputEvent :=
  (st, [], [], [])

instance DAGConstruct : @NetworkProtocol NodeID NodeState InputEvent InternalEvent OutputEvent Message := {
  localInit := initLocalState,
  procInput := procInp,
  procInternal := procInt,
  procMessage := procMsg
}

end DAGConstruction
