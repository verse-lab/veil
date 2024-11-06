import LeanSts.DSL
-- import Mathlib.Tactic

section DAGRider

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

class ByzQuorum (node : Type) (is_byz : outParam (node → Prop)) (nset : outParam Type) :=
  member (a : node) (s : nset) : Prop
  supermajority (s : nset) : Prop       -- 2f + 1 nodes

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 : nset), ∃ (a : node), member a s1 ∧ member a s2 ∧ ¬ is_byz a

open ByzQuorum

type node
type quorum
-- type roundNum
abbrev roundNum := Nat
type vertex
type block

-- FIXME: immutable relation?
variable (is_byz : node → Prop)
instantiate q : ByzQuorum node is_byz quorum
variable [DecidableBinaryRel q.member]
-- instantiate tot : TotalOrderWithZero roundNum

-- TODO: what's the proper way to respresent structs?
-- Vertex struct
relation vertexRound (v : vertex) (r : roundNum)
relation vertexSource (v : vertex) (n : node)
relation vertexBlock (v : vertex) (b : block)
-- set of vertices in `strongEdges`
relation vertexStrongEdge (v : vertex) (se : vertex)
-- set of vertices in `weakEdges`
relation vertexWeakEdge (v : vertex) (we : vertex)


-- State (for a single node); TODO: add node ID to state??
-- DAG: set of vertices at each roundNum
relation dag (r : roundNum) (v : vertex)
individual r : roundNum
relation buffer (v : vertex)

#gen_state

after_init {
    vertexRound _ _         := False;
    vertexSource _ _        := False;
    vertexBlock _ _         := False;
    vertexStrongEdge _ _    := False;
    vertexWeakEdge _ _      := False;

    dag _ _     := False;
    buffer _    := False;
    r           := 0
}

-- Data invariants
-- FIXME: `partial function` keyword to define these automatically
invariant [vertexRound_coherence] ∀ v r r', vertexRound v r → vertexRound v r' → r = r'
invariant [vertexSource_coherence] ∀ v n n', vertexSource v n → vertexSource v n' → n = n'
invariant [vertexBlock_coherence] ∀ v b b', vertexBlock v b → vertexBlock v b' → b = b'

-- Data invariant: the DAG has at most one vertex per roundNum from each source node
-- We use this to relate vertices in the DAG to the quorum properties of nodes
-- (so as to avoid counting the vertices directly)
invariant [dag_coherence]
    ∀ r v v' n n', dag r v → dag r v' → vertexSource v n → vertexSource v' n' → n = n'


-- TODO: if we're modelling DAG construction, should this be an external
-- action? (i.e. one with no implementation?)
action wave_ready (r : roundNum) = {
    skip
}

-- FIXME: To add `Decidable` instances for all propositions
open Classical in
action mainLoop = {
    -- Add to the DAG all vertices in the buffer that have all their predecessors in the DAG
    dag R V := dag R V ∨
        (buffer V ∧ vertexRound V R ∧
        (∀ V', vertexStrongEdge V V' → dag R V') ∧
        (∀ V', vertexWeakEdge V V' → dag R V'));
    -- If it'S in the DAG, remove it from the buffer
    buffer V := buffer V ∧ ¬ ∃ r, dag r V;
    -- There is a quorum of vertices in `dag[r]`
    if (∃ q, ∀ n, member n q → (∃ v, dag r v ∧ vertexSource v n)) {
        if (r % 4 = 0) {
            -- TODO: how to properly model signalling wave_ready?
            -- FIXME: this doesn't inline the `forall s'`
            call wave_ready.fn r
        };
        r := r + 1;
        skip
    }
}

-- #print mainLoop

safety [Trivial] True ∧ True

#gen_spec DAGRider
prove_inv_init by { solve_clause }
prove_inv_safe by { solve_clause }

#check_invariants


end DAGRider
