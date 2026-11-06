module

public import Veil

/-! Byzantine faults. Byzantine nodes do not run the program; they send any
message, at any time, to any node (but cannot forge the sender). -/

-- Everyone adopts the value the leader sends: correct nodes agree when the
-- leader is correct (proved), and not when it is Byzantine, since it can
-- equivocate (found by bounded symbolic search).
veil module DistByzLeader

type node
type value
immutable individual leader : node
immutable individual input : value

network (synchrony := async) (faults := byzantine)

message val (v : value)

var decided : Bool := false
var decision : value := input

program (self : node) {
  if self = leader then
    broadcast (val input)
  recv (val v) from s
  require s = leader
  decision := v
  decided := true
}

safety [agreement]
  ¬ byz leader → correct A ∧ correct B ∧ decided A ∧ decided B → decision A = decision B

-- an honest leader only sends its input, so that is what correct nodes adopt
invariant [honest_leader_sends_input] ¬ byz leader → val_net leader D V → V = input
invariant [decision_is_input] ¬ byz leader ∧ correct N ∧ decided N → decision N = input

#gen_spec

-- a Byzantine leader tells two correct nodes different values
sat trace [equivocation] {
  node_start
  node_start
  net_byz_send_val
  net_byz_send_val
  node_recv1_val
  node_recv1_val
  assert (∃ a b, correct a ∧ correct b ∧ decided a ∧ decided b ∧ decision a ≠ decision b)
}

-- #check_invariants  -- pending reconstruction run

end DistByzLeader

-- One round of max-flooding: a Byzantine node can report a different
-- candidate to different nodes (found by bounded symbolic search).
veil module DistByzFloodMax

type node
instantiate tot : TotalOrder node
open TotalOrder

network (synchrony := sync) (faults := byzantine)

message cand (n : node)

var best : node := self
var decided : Bool := false

program (self : node) {
  broadcast (cand best)
  next_round
  let m :| received (cand m) ∧ ∀ x, received (cand x) → le x m
  best := m
  decided := true
}

/-- warning: you have not defined any invariants or temporal properties for this specification; did you forget? -/
#guard_msgs in
#gen_spec

sat trace [disagreement] {
  node_start
  node_start
  net_byz_send_cand
  net_next_round
  node_round1
  node_round1
  assert (∃ a b, correct a ∧ correct b ∧ decided a ∧ decided b ∧ best a ≠ best b)
}

end DistByzFloodMax
