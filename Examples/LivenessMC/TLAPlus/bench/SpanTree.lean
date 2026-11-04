module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/SpanningTree/SpanTree.tla
-- Distributed spanning-tree distance computation, the graph fixed to SpanTree.cfg's 5-node
-- example. `advance` chooses ANY `d \in (dist[m]+1)..(dist[n]-1)`, as the TLA+ does.

veil module SpanTree

enum NodeE = { N1, N2, N3, N4, N5 }
-- MaxCardinality = 6 (SpanTree.cfg), so every `d` the TLA+ can choose is in 0..6. A plain `Fin`
-- abbrev keeps `advance`'s parameters enumerable.
abbrev Dist := Fin 7
function dist : NodeE → Nat
function mom : NodeE → NodeE

#gen_state

-- Edges == {{n1,n2},{n1,n3},{n2,n3},{n2,n4},{n3,n4},{n3,n5},{n4,n5}}
ghost relation isEdge (a b : NodeE) :=
  (a = N1 ∧ b = N2) ∨ (a = N2 ∧ b = N1) ∨ (a = N1 ∧ b = N3) ∨ (a = N3 ∧ b = N1) ∨
  (a = N2 ∧ b = N3) ∨ (a = N3 ∧ b = N2) ∨ (a = N2 ∧ b = N4) ∨ (a = N4 ∧ b = N2) ∨
  (a = N3 ∧ b = N4) ∨ (a = N4 ∧ b = N3) ∨ (a = N3 ∧ b = N5) ∨ (a = N5 ∧ b = N3) ∨
  (a = N4 ∧ b = N5) ∨ (a = N5 ∧ b = N4)

-- Init == mom = [n |-> n] /\ dist = [n |-> IF n = Root THEN 0 ELSE MaxCardinality]
after_init {
  dist N := if N = N1 then 0 else 6
  mom N := N
}

-- Next == ∃n, ∃m ∈ Nbrs(n) : dist[m] < 1+dist[n] ∧ ∃d ∈ (dist[m]+1)..(dist[n]-1) : dist[n] := d; mom[n] := m
action advance (n m : NodeE) (d : Dist) {
  require isEdge n m
  require dist m + 1 ≤ d.val ∧ d.val < dist n
  dist n := d.val
  mom n := m
}

-- \/ UNCHANGED vars — models TLA+'s implicit stuttering steps under `[][Next]_vars`.
action stutter {
  pure ()
}

ghost relation enabledNext := ∃ n m, isEdge n m ∧ dist m + 1 < dist n

-- PostCondition == every node is either the root at distance 0, unreachable at
-- MaxCardinality (with all neighbors also at MaxCardinality), or has a valid parent edge.
ghost relation postCondition :=
  ∀ n, (n = N1 ∧ dist n = 0 ∧ mom n = n)
     ∨ (dist n = 6 ∧ mom n = n ∧ ∀ m, isEdge n m → dist m = 6)
     ∨ (1 ≤ dist n ∧ dist n ≤ 5 ∧ isEdge n (mom n) ∧ dist n = dist (mom n) + 1)

-- Safety == [] ((~ ENABLED Next) => PostCondition)
invariant [safetyInv] ¬ enabledNext → postCondition

-- Not in the TLA+ source: `Liveness` is only ever checked against `Spec`, which bakes in WF_vars(Next).
-- Not checked on TLC.
temporal [terminates] ◇ ⌜ ¬ enabledNext ⌝

-- Liveness == <>(~ENABLED Next), checked against Spec == Init /\ [][Next]_vars /\ WF_vars(Next).
-- WF_vars(Next) == []<>(~ENABLED <<Next>>_vars \/ <<Next>>_vars): the `¬enabledNext` disjunct is what
-- makes a run that terminates fair. Without it (`□ ◇ ¬ T(stutter)` alone, an earlier version) every
-- run of this terminating algorithm was unfair, the assumption unsatisfiable, and the check vacuous.
temporal [terminatesFair]
  (□ ◇ (¬ T(stutter) ∨ ⌜ ¬ enabledNext ⌝)) → ◇ ⌜ ¬ enabledNext ⌝

#gen_spec

#temporal_check [terminatesFair] compiled { NodeE := NodeE_IndT } {} (route := .fair)

end SpanTree
