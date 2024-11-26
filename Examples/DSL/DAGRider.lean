import LeanSts.DSL
-- import Mathlib.Tactic

section DAGRider

-- set_option trace.dsl true
-- set_option trace.profiler true
-- set_option maxHeartbeats 2000000
-- set_option trace.Elab.command true

class TotalOrderWithZero (t : Type) :=
  -- relation: total order
  le (x y : t) : Prop

  -- zero
  zero : t
  zero_le (x : t) : le zero x

  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x

class Queue (α : Type) (queue : outParam Type) :=
  member (x : α) (q : queue) : Prop

  is_empty (q : queue) :=
    ∀ (e : α), ¬ member e q
  enqueue (x : α) (q q' : queue) :=
    ∀ (e : α), member e q' ↔ (member e q ∨ e = x)
  -- FIXME?: this is not a multi-set
  dequeue (x : α) (q q' : queue) :=
    ∀ (e : α), member e q' ↔ (member e q ∧ e ≠ x)

class ByzQuorum (node : Type) (is_byz : outParam (node → Prop)) (nset : outParam Type) :=
  member (a : node) (s : nset) : Prop
  supermajority (s : nset) : Prop       -- 2f + 1 nodes

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 : nset), ∃ (a : node), member a s1 ∧ member a s2 ∧ ¬ is_byz a

open ByzQuorum

type node
type quorum
-- type round
-- abbrev round := Int
type vertex
type block
type queue

-- FIXME: immutable relation?
variable (is_byz : node → Prop)
instantiate bq : ByzQuorum node is_byz quorum
variable [DecidableBinaryRel bq.member]
-- instantiate tot : TotalOrderWithZero round
instantiate q : Queue block queue

-- TODO: what's the proper way to respresent structs?
-- Vertex struct
relation vertexRound (v : vertex) (r : Int)
relation vertexSource (v : vertex) (n : node)
relation vertexBlock (v : vertex) (b : block)
-- set of vertices in `strongEdges`
relation vertexStrongEdge (v : vertex) (se : vertex)
-- set of vertices in `weakEdges`
relation vertexWeakEdge (v : vertex) (we : vertex)


-- State (for a single node); TODO: add node ID to state??
-- DAG: set of vertices at each round
relation dag (r : Int) (v : vertex)
individual r : Int
relation buffer (v : vertex)
individual blocksToPropose : queue

-- Ghost state
relation delivered (v : vertex) (r : Int) (src : node)

#gen_state

after_init {
    vertexRound _ _         := False;
    vertexSource _ _        := False;
    vertexBlock _ _         := False;
    vertexStrongEdge _ _    := False;
    vertexWeakEdge _ _      := False;

    dag _ _     := False;
    buffer _    := False;
    require q.is_empty blocksToPropose;
    r           := 0;

    -- Ghost state
    delivered _ _ _ := False
}

action dequeue (q0 : queue) = {
    require ¬ q.is_empty q0;
    fresh b : block in
    fresh q' : queue in
    require q.dequeue b q0 q';
    return (b, q')
}

-- #print dequeue.fn

-- Data invariants
-- FIXME: `partial function` keyword to define these automatically
invariant [vertexRound_coherence] ∀ v r r', vertexRound v r → vertexRound v r' → r = r'
invariant [vertexSource_coherence] ∀ v n n', vertexSource v n → vertexSource v n' → n = n'
invariant [vertexBlock_coherence] ∀ v b b', vertexBlock v b → vertexBlock v b' → b = b'

-- FIXME: round numbers are actually natural numbers
invariant [vertexRound_nonneg] ∀ v r, vertexRound v r → r ≥ 0
invariant [round_nonneg] r ≥ 0
invariant [dag_nonneg] ∀ r v, dag r v → r ≥ 0

-- TODO: if we're modelling DAG construction, should this be an external
-- action? (i.e. one with no implementation?)
action waveReady (r : Int) = { skip }
action r_bcast (v : vertex) (r : Int) = { skip }

open Classical in
action r_deliver (v : vertex) (r : Int) (src : node) = {
    require r ≥ 0;
    -- RB integrity guarantee: deliver at most once per round per source
    require ¬ ∃ v', delivered v' r src;
    -- We ignore vertices that have been delivered in the past
    require ¬ ∃ r' src', delivered v r' src';
    delivered v r src := True;
    -- FIXME: `partial function` should let us write `vertexSource v src := True`
    vertexSource v SRC := (SRC = src);
    vertexRound v R := (R = r);
    -- if |v.strongEdges| ≥ 2f + 1 then add v to buffer
    if (∃ q, ∀ n, member n q → (∃ v', vertexSource v' n ∧ vertexStrongEdge v v')) {
        buffer v := True
    }
}

action setWeakEdges (v : vertex) (r : Int) = {
  require r ≥ 0;
  -- `v.weakEdges ← {}`
  require (¬ ∃ we, vertexWeakEdge v we)
  -- NOTE: we cannot express the `path` predicate in the DSL
  -- or in FOL generally; see `Array.path` in `DAG.lean` to
  -- see how we express it in HOL (it quantifies over lists of vertices)
}

action createNewVertex (r : Int) = {
    require r ≥ 0;
    -- FIXME: "wait until ¬ blocksToPropose.empty"
    -- `v.block ← blocksToPropose.dequeue()`
    (b, q') : block × queue ← call !dequeue blocksToPropose in
    blocksToPropose := q';
    fresh v : vertex in
    -- this is a new, really "fresh", vertex
    require (¬ ∃ b, vertexBlock v b) ∧ (¬ ∃ n, vertexSource v n) ∧ (¬ ∃ r, vertexRound v r)
      ∧ (¬ ∃ se, vertexStrongEdge v se) ∧ (¬ ∃ we, vertexWeakEdge v we);
    vertexBlock v b := True;
    -- `v.strongEdges ← DAG[round - 1]`
    vertexStrongEdge v SE := dag (r - 1) SE;
    call !setWeakEdges v r;
    return v
 }

-- #print createNewVertex.tr

-- FIXME: To add `Decidable` instances for all propositions
open Classical in
action mainLoop = {
    -- Add to the DAG all vertices in the buffer that have all their predecessors in the DAG
    dag R V := dag R V ∨
        (buffer V ∧ vertexRound V R ∧
        (∀ V', vertexStrongEdge V V' → ∃ r, dag r V') ∧
        (∀ V', vertexWeakEdge V V' → ∃ r, dag r V'));
    -- If it'S in the DAG, remove it from the buffer
    buffer V := buffer V ∧ ¬ ∃ r, dag r V;
    -- There is a quorum of vertices in `dag[r]`
    if (∃ q, ∀ n, member n q → (∃ v, vertexSource v n ∧ dag r v)) {
        if (r % 4 = 0) {
            -- TODO: how to properly model signalling wave_ready?
            call !waveReady r
        };
        r := r + 1;
        v : vertex ← call !createNewVertex r in
        call !r_bcast v r
    }
}

-- #print mainLoop.tr

-- Invariant: the DAG has at most one vertex per round from each source node
-- We use this to relate vertices in the DAG to the quorum properties of nodes
-- (so as to avoid counting the vertices directly)
safety [dag_coherence]
    ∀ r v v' n, dag r v → dag r v' → vertexSource v n → vertexSource v' n → v = v'

-- Protocol properties

/- Sort stratification
  `vertex`
  `round`
  `node`
-/

-- inferred from `r_deliver`
invariant [buffer_implies_delivered] ∀ v, buffer v → ∃ r src, delivered v r src
invariant [delivered_round_is_vertex_round] ∀ v r src, delivered v r src → vertexRound v r
invariant [delivered_source_is_vertex_source] ∀ v r src, delivered v r src → vertexSource v src
invariant [vertex_round_implies_delivered] ∀ v r, vertexRound v r → ∃ src, delivered v r src
invariant [vertex_source_implies_delivered] ∀ v src, vertexSource v src → ∃ r, delivered v r src
invariant [one_vertex_per_round_per_source] ∀ r v v' src, delivered v r src → delivered v' r src → v = v'

-- Messes up the quantifier stratification:
-- invariant [buffer_implies_quorum_strong_edges]
--     ∀ v, buffer v → ∃ q, ∀ n, member n q → (∃ v', vertexSource v' n ∧ vertexStrongEdge v v')

-- inferred from `mainLoop`
invariant [dag_round_matches_vertex_round] ∀ r v, dag r v → vertexRound v r

#gen_spec DAGRider

set_option sauto.model.minimize true

#check_invariants

end DAGRider
