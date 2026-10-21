module

public import Veil

/-! One round of max-flooding in a synchronous, fully connected network. The
same program agrees on a reliable network (proved) and disagrees on a lossy
one (found by bounded symbolic search). -/

veil module DistFloodMaxReliable

type node
instantiate tot : TotalOrder node
open TotalOrder

network (synchrony := sync) (complexity := true)

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

safety [agreement] decided A ∧ decided B → best A = best B
safety [one_round] net_rounds ≤ 1

-- round 0: every node announces itself
invariant [round0]
  net_rounds = 0 →
    (pc N = pc_start ∧ net_ready N) ∨ (pc N = pc_round1 ∧ ¬ net_ready N ∧ ∀ d, cand_out N d N)
invariant [round0_out] net_rounds = 0 → (cand_out S D X → X = S) ∧ cand_in S D X = false
invariant [round0_best] net_rounds = 0 → best N = N
-- round 1: everyone has heard everyone, and decides on the largest
invariant [round1]
  net_rounds = 1 → (pc N = pc_round1 ∧ net_ready N) ∨ (pc N = pc_done ∧ ¬ net_ready N)
invariant [round1_in] net_rounds = 1 → (cand_in S D X ↔ X = S)
invariant [decided_done] decided N ↔ pc N = pc_done
invariant [decided_max] decided N → le X (best N)

#gen_spec

#check_invariants

end DistFloodMaxReliable

veil module DistFloodMaxLossy

type node
instantiate tot : TotalOrder node
open TotalOrder

network (synchrony := sync) (loss := lossy)

message cand (n : node)

var best : node := self
var decided : Bool := false

program (self : node) {
  broadcast (cand best)
  next_round
  if ∃ x, received (cand x) then
    let m :| received (cand m) ∧ ∀ x, received (cand x) → le x m
    best := m
  decided := true
}

#gen_spec

-- two nodes decide differently: one of them lost the other's message
sat trace [disagreement] {
  any 6 actions
  assert (∃ a b, decided a ∧ decided b ∧ best a ≠ best b)
}

end DistFloodMaxLossy
