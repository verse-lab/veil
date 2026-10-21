module

public import Veil

/-! Several synchronous rounds: a `while` loop around `next_round`, `received`
with an explicit sender, and the complexity counters. -/

veil module DistSyncRounds

type node
instantiate tot : TotalOrder node
open TotalOrder

network (synchrony := sync) (complexity := true)

message cand (n : node)

var best : node := self
var r : Nat := 0

program (self : node) {
  while r < 2 do
    broadcast (cand best)
    next_round
    if ∃ x s, received (cand x) from s ∧ x ≠ best ∧ le best x then
      let m :| received (cand m) ∧ ∀ x, received (cand x) → le x m
      best := m
    r := r + 1
}

safety [agreement] halted A ∧ halted B → best A = best B
safety [two_rounds] net_rounds ≤ 2
safety [no_point_to_point] net_msgs = 0

-- a node always announces its current best, and sends nothing before its step
invariant [out_is_best] cand_out S D X → X = best S
invariant [silent_before_step] net_ready S → cand_out S D X = false
-- round 0: every node announces itself
invariant [round0]
  net_rounds = 0 →
    (pc N = pc_start ∧ net_ready N ∧ r N = 0) ∨
    (pc N = pc_round2 ∧ ¬ net_ready N ∧ r N = 0 ∧ ∀ d, cand_out N d N)
invariant [round0_state] net_rounds = 0 → best N = N ∧ cand_in S D X = false
-- round 1: everyone hears everyone, so after its step a node holds the maximum
invariant [round1]
  net_rounds = 1 →
    (pc N = pc_round2 ∧ net_ready N ∧ r N = 0 ∧ best N = N) ∨
    (pc N = pc_round2 ∧ ¬ net_ready N ∧ r N = 1 ∧ (∀ y, le y (best N)) ∧ ∀ d, cand_out N d (best N))
invariant [round1_in] net_rounds = 1 → (cand_in S D X ↔ X = S)
-- round 2: everyone already holds the maximum, and stops
invariant [round2]
  net_rounds = 2 →
    (pc N = pc_round2 ∧ net_ready N ∧ r N = 1) ∨ (pc N = pc_done ∧ ¬ net_ready N ∧ r N = 2)
invariant [round2_in] net_rounds = 2 → cand_in S D X → le Y X
invariant [max_after_round1] net_rounds = 2 → le Y (best N)

#gen_spec

-- #check_invariants  -- invariant still being developed in trusted mode

end DistSyncRounds
