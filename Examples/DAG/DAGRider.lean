import Examples.DAG.DAGConstruction

namespace DAGRider

variable {NodeID Block : Type} [DecidableEq NodeID] [Inhabited NodeID] [DecidableEq Block] [Inhabited Block]
local notation "Vertex" => @Vertex NodeID Block
abbrev Round := DAGConstruction.Round
local notation "InstanceID" => (NodeID × Round)

/- Global perfect coin -/
variable {chooseLeader : Round → NodeID}

-- Instead of communicating with the DAG Construct protocol solely via events
-- (channels), we merge the state of the two protocols.
local notation "DAGState" => @DAGConstruction.NodeState NodeID Block

structure NodeState :=
  dagState : DAGState

  decidedWave : Nat
  deliveredVertices : List Vertex
  -- This does not actually need to be stored, since it always gets emptied at the end of `wave_ready`
  -- leadersStack : List Vertex
local notation "NodeState" => @NodeState NodeID Block

-- local notation "DAGConstruct" => @DAGConstruction.DAGConstruct NodeID Block _ _
-- FIXME: we are implicitly assuming FIFO channels, which is probably what we want in any case

inductive Input where
  | atomicBroadcast (r : Round) (bl : Block)
local notation "Input" => @Input Block

abbrev InputEvent := Input ⊕ DAGConstruction.Output

abbrev InternalEvent := Unit

inductive OutputEvent where
  | atomicDeliver (inst : InstanceID) (b : Block)

local notation "InputEvent" => @InputEvent Block
local notation "InternalEvent" => @InternalEvent
local notation "OutputEvent" => @OutputEvent NodeID Block

def Message := Unit

local notation "Message" => @Message
local notation "Packet" => @Packet NodeID Message
local notation "Network" => @Network NodeID

/-- Count decreasing from `start` to `endAt` (inclusive). -/
def iotaN (start : Nat) (endAt : Nat) :=
  let rec loop (n : Nat) (iterRemaining : Nat) (acc : List Nat) : List Nat :=
    if iterRemaining = 0 then acc else loop (n - 1) (iterRemaining - 1) (n :: acc)
  List.reverse $ loop start (start - endAt + 1) []

/-- What round is the `k`'th round in wave `w`? -/
def round (w : Round) (k : Round) : Round := 4 * (w - 1) + k

def getWaveVertexLeader (st : NodeState) (w : Round) : Option Vertex :=
  let p := chooseLeader w
  (st.dagState.dag[round w 1]!).find? (fun v => v.source = p)
local notation "getWaveVertexLeader" => @getWaveVertexLeader NodeID Block _ chooseLeader

def orderVertices (st : NodeState) (leaderStack : List Vertex) : List Vertex :=
  let rec loop (stack : List Vertex) (toDeliver : List Vertex) : List Vertex :=
    match stack with
    | [] => toDeliver
    | v :: stack' =>
      let verticesToDeliver := st.dagState.dag.allVertices.filter (fun v' =>
        -- NOTE: we do not update st.deliveredVertices here, but instead `∪ toDeliver`
        DAG.path v v' && !(st.deliveredVertices ∪ toDeliver).contains v')
      loop stack' (toDeliver ∪ verticesToDeliver)
  loop [] leaderStack

def procInp (net : Network) (st : NodeState) (t : InputEvent) : NodeState × List Packet × List InternalEvent × List OutputEvent :=
  match t with
  -- "upon `a_bcast`"
  | .inl $ .atomicBroadcast r bl =>
    let st := { st with dagState.blocksToPropose := st.dagState.blocksToPropose.enqueue bl }
    (st, [], [], [])
  | .inr $ .waveReady w =>
    match getWaveVertexLeader st w with
    | none => (st, [], [], []) -- return
    | some v =>
      let leaderSupports := (st.dagState.dag[round w 4]!).filter (fun u => DAG.strongPath u v)
      -- if < 2f + 1 vertices in the wave support the leader, then we do not (cannot) commit
      if leaderSupports.length < DAGConstruction.threshVerticesToAdvance net then
        (st, [], [], []) -- return
      else
        let range := iotaN (w - 1) (st.decidedWave + 1)
        let (leadersStack, v) := range.foldl (fun (leadersStack, v) (w' : Round) =>
            match getWaveVertexLeader st w' with
            | none => (leadersStack, v)
            | some v' => if DAG.strongPath v v' then (v' :: leadersStack, v') else (leadersStack, v)
        ) ([v], v)
        let toDeliver := orderVertices st leadersStack
        let st := { st with decidedWave := w, deliveredVertices := st.deliveredVertices ∪ toDeliver }
        let deliverEvents := toDeliver.map (fun v => OutputEvent.atomicDeliver (v.source, v.round) v.block.get!)
        (st, [], [], deliverEvents)

end DAGRider
