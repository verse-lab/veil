import Batteries.Data.List

variable {node bl : Type}
  [Inhabited node] [BEq node] [dec_node : DecidableEq node]
  [Inhabited bl] [BEq bl] [dec_block : DecidableEq bl]

local notation "Set" => List

/-- A vertex in DAG-rider is a rooted DAG (aka. downset). -/
inductive Vertex where
  | Root (source : node) : Vertex
  /--
    A vertex in DAG-rider is a rooted DAG (aka. downset). The edges
    point to previous rounds.

    Strong edges point to vertices in round `round - 1` and weak edges
    point to vertices in prior rounds (`r' < r - 1`) such that otherwise
    there is no path from this vertex `v` to them.

    Strong edges are used for *agreement* and weak edges are there to
    ensure that all vertices are eventually included in the total order
    (and thus ensure *validity*).
  -/
  | V (round : Nat) (source : node) (block : bl) (strongEdges : Set Vertex) (weakEdges : Set Vertex) : Vertex
deriving BEq, Inhabited

-- TODO: look into `@[elab_as_elim]`

local notation "Vertex" => @Vertex node bl

@[inline] def Vertex.hasDecEq (a b : Vertex) : Decidable (Eq a b) :=
   match a, b with
   | .Root a, .Root b => by rw [Vertex.Root.injEq]; apply (dec_node a b)
   | .V r s b se we, .V r' s' b' se' we' => sorry
   | .Root _, .V .. => isFalse (by rintro ⟨⟩)
   | .V .., .Root _ => isFalse (by rintro ⟨⟩)

instance : DecidableEq Vertex := Vertex.hasDecEq

def Vertex.round : Vertex → Nat
  | Vertex.Root _ => 0
  | Vertex.V round _ _ _ _ => round

def Vertex.source : Vertex → node
  | Vertex.Root source | Vertex.V _ source _ _ _ => source

def Vertex.block : Vertex → Option bl
  | Vertex.Root _ => none
  | Vertex.V _ _ block _ _ => some block

def Vertex.strongEdges : Vertex → Set Vertex
  | Vertex.Root _ => []
  | Vertex.V _ _ _ strongEdges _ => strongEdges

def Vertex.weakEdges : Vertex → Set Vertex
  | Vertex.Root _ => []
  | Vertex.V _ _ _ _ weakEdges => weakEdges

/-- Notation type class for the union operation `∪`. -/
-- class Union (α : Type u) where
--   /-- `a ∪ b` is the union of`a` and `b`. -/
--   union : α → α → α
instance : Union (Set Vertex) where
  -- TODO: make this behave like set union
  union := List.union

/-- A DAG consists of the vertices at each round. We represent rounds by
    indices in the array. -/
local notation "DAG" => Array (Set Vertex)

def Array.numRounds (dag : DAG) : Nat := dag.size

def Array.allVertices (dag : DAG) : Set Vertex :=
  dag.foldl (· ∪ ·) []

/- v ∈ ⋃_{r + 1} DAG[r] -/
instance : Membership Vertex DAG where
  mem s v := v ∈ Array.allVertices s

/-- Is the given vertex `v` at round `r` in the DAG? -/
def Array.vertexAtRound (dag : DAG) (v : Vertex) (r : Nat) : Prop :=
  r < dag.numRounds ∧ v ∈ dag[r]!

/-- Ensure `a` has at least size `sz`, filling empty space with default `α`. -/
def Array.ensureCapacity [Inhabited α] (a : Array α) (sz : Nat) : Array α :=
  if sz < a.size then a else
    let diff := sz - a.size
    let suffix := Array.mkArray diff default
    a.append suffix

/-- Add the given vertex to the DAG at the round indicated by `v.round`,
    extending the array if necessary. -/
def Array.addVertex (dag : DAG) (v : Vertex) : DAG :=
  let r := v.round;
  let newV := match dag.get? r with
    | none => [v]
    | some vs => v :: vs
  (dag.ensureCapacity r).setD r newV

/- Check if `p` is a (backwards) path consisting of strong and weak
   vertices from `v` to `u` in the DAG. -/
def Array.isPath (p : Array Vertex) (v u : Vertex) : Prop :=
  (0 < p.size ∧ p[0]! = v ∧ p[p.size - 1]! = u) ∧
  (∀ i,
    i ∈ [1 : p.size - 1] →
    let vᵢ := p[i]!
    let vₚ := p[i - 1]!
    vᵢ ∈ (vₚ.weakEdges ∪ vₚ.strongEdges))

/- Check if `p` is a (backwards) path consisting of only strong vertices
   from `v` to `u` in the DAG. -/
def Array.isStrongPath (p : Array Vertex) (v u : Vertex) : Prop :=
  (0 < p.size ∧ p[0]! = v ∧ p[p.size - 1]! = u) ∧
  (∀ i,
    i ∈ [1 : p.size - 1] →
    let vᵢ := p[i]!
    let vₚ := p[i - 1]!
    vᵢ ∈ vₚ.strongEdges)

/-- Are all the given `vs` in `dag`? -/
def Array.containsAll (dag : DAG) (vs : Array Vertex) : Bool :=
  vs.all (dag.allVertices.contains)

def Array.path (dag : DAG) (v u : Vertex) : Prop :=
  ∃ p, p.isPath v u ∧ dag.containsAll p

def Array.strongPath (dag : DAG) (v u : Vertex) : Prop :=
  ∃ p, p.isStrongPath v u ∧ dag.containsAll p

partial def DFS (startAt : Vertex) (strongOnly : Bool := true) : Set Vertex :=
  let rec DFS (visited : Set Vertex) (node : Vertex) : Set Vertex :=
    if visited.contains node then
      visited
    else
      let newVisited := node :: visited
      let toVisit := if strongOnly then node.strongEdges else node.weakEdges ∪ node.strongEdges
      /- Run DFS from each node in `toVisit`, progressively enhancing
      `visited` after each DFS. -/
      List.foldl DFS newVisited toVisit
  DFS [] startAt

def DAG.path (v u : Vertex) : Bool :=
  (DFS v (strongOnly := false)).contains u

def DAG.strongPath (v u : Vertex) : Bool :=
  (DFS v).contains u
