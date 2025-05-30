import Veil.DSL
import Test.TestUtil
import Veil.Std

veil module Test₁


type node

relation r (n : node) (m : node) : Prop
relation r' (n : Nat) (m : node) : Prop
individual nd : node

#gen_state

after_init {
  r N M := False
  r' N M := False
}

action f (n : Nat)  = {
  pure n
}

action foo (x : node) = {
  pure ()
}

action fresh_node (yy : node) = {
  let n <- fresh node
  nd := n
}


#guard_msgs(drop warning) in
#gen_spec

end Test₁

veil module Test₂


type node'
type node''

relation r'' (n : node') (m : node') : Prop
includes Test₁ node' node'_dec node'_ne as test
includes Test₁ node' _ _ as test'

#gen_state

after_init {
  r'' N M := False
}

action g = {
  -- let n <- fresh node'
  -- test.r' N n := True
  r'' := test.r
  r'' := test'.r
  let _ <- test.f 1
  test'.f 1
}

invariant True

#gen_spec

end Test₂


veil module ReliableBroadcast
type node
type nodeset
type round
type value

variable (is_byz : node → Prop)
instantiate nset : NodeSet node is_byz nodeset
open NodeSet

relation initial_msg (originator : node) (dst : node) (r : round) (v : value)
relation echo_msg (src : node) (dst : node) (originator : node) (r : round) (v : value)
relation vote_msg (src : node) (dst : node) (originator : node) (r : round) (v : value)

relation sent (n : node) (r : round)
relation echoed (n : node) (originator : node) (in_round : round) (v : value)
relation voted (n : node) (originator : node) (in_round : round) (v : value)
relation delivered (n : node) (originator : node) (in_round : round) (v : value)

#gen_state

ghost relation initial_value (n : node) (r : round) (v : value) := ∀ dst, initial_msg n dst r v

after_init {
  initial_msg O D R V := False;
  echo_msg S D O R V  := False;
  vote_msg S D O R V  := False;

  sent N R            := False;
  echoed N O R V      := False;
  voted N O R V       := False;
  delivered N O R V   := False
}

internal transition byz = {
  (∀ (src dst : node) (r : round) (v : value),
    (¬ is_byz src ∧ (initial_msg src dst r v ↔ initial_msg' src dst r v)) ∨
    (is_byz src ∧ (initial_msg src dst r v → initial_msg' src dst r v))) ∧
  (∀ (src dst originator : node) (r : round) (v : value),
    (¬ is_byz src ∧ (echo_msg src dst originator r v ↔ echo_msg' src dst originator r v)) ∨
    (is_byz src ∧ (echo_msg src dst originator r v → echo_msg' src dst originator r v))) ∧
  (∀ (src dst originator : node) (r : round) (v : value),
    (¬ is_byz src ∧ (vote_msg src dst originator r v ↔ vote_msg' src dst originator r v)) ∨
    (is_byz src ∧ (vote_msg src dst originator r v → vote_msg' src dst originator r v)))
  -- unchanged
  ∧ (sent = sent')
  ∧ (echoed = echoed')
  ∧ (voted = voted')
  ∧ (delivered = delivered')
}

action echo (n : node) (originator : node) (r : round) (v : value) = {
  require initial_msg originator n r v;
  require ∀ V, ¬ echoed n originator r V;
  echoed n originator r v := True;
  echo_msg n DST originator r v := True
}

safety [vote_integrity]
  ∀ (src dst : node) (r : round) (v : value),
     ¬ is_byz src ∧ ¬ is_byz dst ∧ voted dst src r v → (sent src r ∧ initial_value src r v)

#gen_spec

end ReliableBroadcast

veil module DAGConstruction
type node
type nodeset
type vertex
type block
type queue

variable (is_byz : node → Prop)
instantiate nset : NodeSet node is_byz nodeset
open NodeSet

includes ReliableBroadcast node node_dec node_ne nodeset nodeset_dec nodeset_ne Int _ _ vertex vertex_dec vertex_ne is_byz nset as rb

#gen_state

after_init { pure () }

action foo (n : node) (originator : node) (r : Int) (v : vertex) = {
  rb.echo n originator r v
}

#guard_msgs(drop warning) in
#gen_spec

-- This tests that all the simplification attributes exist
#guard_msgs(drop warning, error) in
sat trace { } by bmc_sat

end DAGConstruction
