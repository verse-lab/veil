module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/SpanningTree/SpanTree.tla
-- Lamport's spanning tree: a node n with a neighbour m lowers dist[n] and takes m as mom[n].
-- `SpanTree.cfg` checks TypeOK, Safety and Liveness of Spec on a 5-node graph.

veil module SpanTree

type node
type nodeSet
instantiate nSet : TSet node nodeSet
immutable individual Nodes : nodeSet
param Edges : node → node → Bool
param Root : node
param MaxCardinality : Nat

function mom : node → node
function dist : node → Nat

#gen_state

-- ASSUME /\ Root \in Nodes  /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
--        /\ MaxCardinality \in Nat  /\ MaxCardinality >= Cardinality(Nodes)
assumption [Nodes_complete] ∀ n : node, n ∈ Nodes
assumption [Edges_symmetric] ∀ m n : node, Edges m n = Edges n m
assumption [Edges_irreflexive] ∀ n : node, ¬ Edges n n
assumption [MaxCardinality_ge_Nodes] MaxCardinality ≥ nSet.count Nodes

-- Nbrs(n) == {m \in Nodes : {m, n} \in Edges}
theory ghost relation Nbrs (n m : node) := m ∈ Nodes ∧ Edges m n

-- Init == mom = [n \in Nodes |-> n] /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
after_init {
  mom N := N
  dist N := if N = Root then 0 else MaxCardinality
}

-- Next == \E n \in Nodes : \E m \in Nbrs(n) : /\ dist[m] < 1 + dist[n]
--   /\ \E d \in (dist[m]+1) .. (dist[n] - 1) : dist' = [dist EXCEPT ![n] = d] /\ mom' = [mom EXCEPT ![n] = m]
-- Named `NextAction` because `#gen_spec` declares the module's next-state relation as `Next`.
action NextAction (n m : node) {
  require n ∈ Nodes
  require Nbrs n m
  require dist m < 1 + dist n
  let d ← pick { d // d ∈ List.range' (dist m + 1) (dist n - dist m - 1) }
  dist n := d.val
  mom n := m
}

-- \/ UNCHANGED vars — the stuttering that `[][Next]_vars` admits.
action stutter { pure () }

-- TypeOK == mom \in [Nodes -> Nodes] /\ dist \in [Nodes -> Nat] — Veil's typing, so no invariant.

-- ENABLED Next — a step exists iff some d does, since dist' and mom' are then determined.
ghost relation ENABLEDNext := ∃ n : node, n ∈ Nodes ∧ ∃ m : node,
  Nbrs n m ∧ dist m < 1 + dist n ∧ List.range' (dist m + 1) (dist n - dist m - 1) ≠ []

/-
PostCondition ==
  \A n \in Nodes :
    \/ n = Root /\ dist[n] = 0 /\ mom[n] = n
    \/ dist[n] = MaxCardinality /\ mom[n] = n /\ \A m \in Nbrs(n) : dist[m] = MaxCardinality
    \/ dist[n] \in 1..(MaxCardinality-1) /\ mom[n] \in Nbrs(n) /\ dist[n] = dist[mom[n]] + 1
-/
ghost relation PostCondition := ∀ n : node, n ∈ Nodes →
  (n = Root ∧ dist n = 0 ∧ mom n = n)
  ∨ (dist n = MaxCardinality ∧ mom n = n ∧ ∀ m : node, Nbrs n m → dist m = MaxCardinality)
  ∨ (1 ≤ dist n ∧ dist n ≤ MaxCardinality - 1 ∧ Nbrs n (mom n) ∧ dist n = dist (mom n) + 1)

-- Safety == []((~ ENABLED Next) => PostCondition)
invariant [Safety] ¬ ENABLEDNext → PostCondition

-- Liveness == <>(~ ENABLED Next)
temporal (only := check) [Liveness] 𝒲ℱ NextAction → ◇ ¬ Enabled NextAction

-- Not checked on TLC.
temporal (only := check) [ENABLEDNextAgrees] □ (Enabled NextAction ↔ ⌜ ENABLEDNext ⌝)

#gen_spec
#gen_executable

-- Edges = {{n1,n2}, {n1,n3}, {n2,n3}, {n2,n4}, {n3,n4}, {n3,n5}, {n4,n5}}, n1 .. n5 as 0 .. 4.
def Edges5 : Fin 5 → Fin 5 → Bool := fun m n =>
  let pairs : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (2, 4), (3, 4)]
  pairs.contains (m, n) || pairs.contains (n, m)

#model_check compiled
  { node := Fin 5, nodeSet := OrdList (Fin 5), Edges := Edges5, Root := 0, MaxCardinality := 6 }
  { Nodes := OrdList.ofList (List.finRange 5) }

#temporal_check compiled
  { node := Fin 5, nodeSet := OrdList (Fin 5), Edges := Edges5, Root := 0, MaxCardinality := 6 }
  { Nodes := OrdList.ofList (List.finRange 5) }

-- A second instance: the disconnected graph Edges = {{n1,n2}, {n3,n4}} with MaxCardinality = 4.
def Edges4 : Fin 4 → Fin 4 → Bool := fun m n =>
  let pairs : List (Fin 4 × Fin 4) := [(0, 1), (2, 3)]
  pairs.contains (m, n) || pairs.contains (n, m)

--#model_check
--  { node := Fin 4, nodeSet := OrdList (Fin 4), Edges := Edges4, Root := 0, MaxCardinality := 4 }
--  { Nodes := OrdList.ofList (List.finRange 4) }

--#temporal_check
--  { node := Fin 4, nodeSet := OrdList (Fin 4), Edges := Edges4, Root := 0, MaxCardinality := 4 }
--  { Nodes := OrdList.ofList (List.finRange 4) }

end SpanTree
