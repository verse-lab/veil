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
-- type Nat
-- abbrev round := Nat
type vertex
type block
type queue

-- FIXME: immutable relation?
variable (is_byz : node → Prop)
instantiate bq : ByzQuorum node is_byz quorum
variable [DecidableBinaryRel bq.member]
-- instantiate tot : TotalOrderWithZero Nat
instantiate q : Queue block queue

-- TODO: what's the proper way to respresent structs?
-- Vertex struct
relation vertexRound (v : vertex) (r : Nat)
relation vertexSource (v : vertex) (n : node)
relation vertexBlock (v : vertex) (b : block)
-- set of vertices in `strongEdges`
relation vertexStrongEdge (v : vertex) (se : vertex)
-- set of vertices in `weakEdges`
relation vertexWeakEdge (v : vertex) (we : vertex)


-- State (for a single node); TODO: add node ID to state??
-- DAG: set of vertices at each round
relation dag (r : Nat) (v : vertex)
individual r : Nat
relation buffer (v : vertex)
individual blocksToPropose : queue

-- Ghost state
relation delivered (v : vertex) (r : Nat) (src : node)

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

-- Data invariant: the DAG has at most one vertex per round from each source node
-- We use this to relate vertices in the DAG to the quorum properties of nodes
-- (so as to avoid counting the vertices directly)
safety [dag_coherence]
    ∀ r v v' n, dag r v → dag r v' → vertexSource v n → vertexSource v' n → v = v'

-- TODO: if we're modelling DAG construction, should this be an external
-- action? (i.e. one with no implementation?)
action waveReady (r : Nat) = { skip }
action r_bcast (v : vertex) (r : Nat) = { skip }

action r_deliver (v : vertex) (r : Nat) (src : node) = {
    require ¬ ∃ v', delivered v' r src; -- RB integrity guarantee: deliver at most once
    delivered v r src := True;
    -- `v` cannot be in the DAG (at any round)
    -- TODO: how exactly do we justify this?
    require ¬ dag R v;

    -- FIXME: `partial function` should let us write `vertexSource v src := True`
    vertexSource v SRC := (SRC = src);
    vertexRound v R := (R = r)

    -- TODO: if |v.strongEdges| ≥ 2f + 1 then add v to buffer
}

action setWeakEdges (v : vertex) (r : Nat) = {
  -- `v.weakEdges ← {}`
  require (¬ ∃ we, vertexWeakEdge v we)
  -- NOTE: we cannot express the `path` predicate in the DSL
  -- or in FOL generally; see `Array.path` in `DAG.lean` to
  -- see how we express it in HOL (it quantifies over lists of vertices)
}

action createNewVertex (r : Nat) = {
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

#print createNewVertex.tr

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
    if (∃ q, ∀ n, member n q → (∃ v, dag r v ∧ vertexSource v n)) {
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

-- Protocol properties
invariant [dag_round_matches_vertex_round] ∀ r v, dag r v → vertexRound v r

#gen_spec DAGRider
prove_inv_init by { solve_clause }
prove_inv_safe by { solve_clause }

set_option sauto.model.minimize false

-- #check_invariants


set_option sauto.smt.translator "lean-smt"
set_option sauto.model.minimize true
set_option trace.sauto.query true

@[invProof]
theorem mainLoop.tr_dag_coherence :
    ∀ (st st' : State node quorum vertex block queue is_byz),
      (DAGRider node quorum vertex block queue is_byz).inv st →
        (mainLoop.tr node quorum vertex block queue is_byz) st st' →
          (dag_coherence node quorum vertex block queue is_byz) st' :=
  -- by unhygienic intros; solve_clause[mainLoop.tr]
  by sorry


#print mainLoop.tr_dag_coherence

end DAGRider
