module

public import Veil

/-! Consensus with crash faults: FloodMin, the single-value form of FloodSet
(`Examples/Tutorial/FloodSet.lean`). In a synchronous network where at most
`f` nodes crash, every node floods the smallest estimate it has seen for
`f + 1` rounds and then decides it. Correct nodes agree (proved), but not with
one round fewer (found by bounded symbolic search). A node that crashes during
a round may have sent its messages of that round to only some nodes. -/

veil module DistFloodMin

type node
type value
instantiate ord : TotalOrder value
open TotalOrder
immutable individual f : Nat
immutable function input : node → value

network (synchrony := sync) (faults := crash f) (complexity := true)

message est (v : value)

var x : value := input self
var r : Nat := 0
var decided : Bool := false

program (self : node) {
  while r < f + 1 do
    broadcast (est x)
    next_round
    let m :| (m = x ∨ received (est m)) ∧ le m x ∧ ∀ w, received (est w) → le m w
    x := m
    r := r + 1
  decided := true
}

safety [agreement] correct A ∧ correct B ∧ decided A ∧ decided B → x A = x B
safety [validity] ∃ n, x A = input n

invariant [crash_bound] net_crashes ≤ f
invariant [rounds_bound] net_rounds ≤ f + 1
-- where the nodes are
invariant [round0]
  net_rounds = 0 →
    (pc N = pc_start ∧ net_ready N ∧ r N = 0) ∨
    (pc N = pc_round2 ∧ ¬ net_ready N ∧ r N = 0) ∨
    (pc N = pc_crashed ∧ ¬ net_ready N ∧ r N = 0)
invariant [later_rounds]
  net_rounds ≥ 1 →
    (pc N = pc_round2 ∧ net_ready N ∧ r N + 1 = net_rounds) ∨
    (pc N = pc_round2 ∧ ¬ net_ready N ∧ r N = net_rounds ∧ r N < f + 1) ∨
    (pc N = pc_done ∧ ¬ net_ready N ∧ r N = f + 1 ∧ net_rounds = f + 1) ∨
    (pc N = pc_crashed ∧ ¬ net_ready N ∧ r N ≤ net_rounds)
invariant [decided_done] decided N ↔ pc N = pc_done
invariant [crashing_crashed] net_crashing N → pc N = pc_crashed
-- the messages of the round
invariant [out_value]
  est_out S D V → V = x S ∧ r S = net_rounds ∧ (pc S = pc_round2 ∨ net_crashing S)
invariant [out_complete] pc S = pc_round2 ∧ ¬ net_ready S → est_out S D (x S)
invariant [round0_in] net_rounds = 0 → est_in S D V = false
invariant [in_inputs] est_in S D V → ∃ n, V = input n
-- Settled: the nodes taking part in the round all end it with the same estimate.
-- A node takes part if it has not crashed, or crashed in this round after its
-- step (its messages may still be delivered). A node that has taken its step
-- ends with its current estimate; one that has not, with the smallest of its
-- own and those it received. A round with no crash settles the run, and a
-- settled run stays settled; so the run is settled unless there was a crash
-- in every round so far.
invariant [settled_stepped]
  (net_crashes < net_rounds ∨ ((∃ n, net_crashing n) ∧ net_crashes ≤ net_rounds)) →
  (pc A ≠ pc_crashed ∨ (net_crashing A ∧ r A = net_rounds)) →
  (pc B ≠ pc_crashed ∨ (net_crashing B ∧ r B = net_rounds)) →
  ¬ net_ready A ∧ ¬ net_ready B → x A = x B
invariant [settled_ready_stepped]
  (net_crashes < net_rounds ∨ ((∃ n, net_crashing n) ∧ net_crashes ≤ net_rounds)) →
  (pc A ≠ pc_crashed ∨ (net_crashing A ∧ r A = net_rounds)) →
  (pc B ≠ pc_crashed ∨ (net_crashing B ∧ r B = net_rounds)) →
  net_ready A ∧ ¬ net_ready B →
    (x B = x A ∨ ∃ s, est_in s A (x B)) ∧ le (x B) (x A) ∧ ∀ s w, est_in s A w → le (x B) w
invariant [settled_ready]
  (net_crashes < net_rounds ∨ ((∃ n, net_crashing n) ∧ net_crashes ≤ net_rounds)) →
  (pc A ≠ pc_crashed ∨ (net_crashing A ∧ r A = net_rounds)) →
  (pc B ≠ pc_crashed ∨ (net_crashing B ∧ r B = net_rounds)) →
  net_ready A ∧ net_ready B →
    ∀ u, ((u = x A ∨ ∃ s, est_in s A u) ∧ le u (x A) ∧ ∀ s w, est_in s A w → le u w) →
         ((u = x B ∨ ∃ s, est_in s B u) ∧ le u (x B) ∧ ∀ s w, est_in s B w → le u w)
invariant [crashing_counted] net_crashing N → net_crashes ≥ 1

set_option veil.smt.timeout 900

#gen_spec

-- #check_invariants  -- pending reconstruction run

end DistFloodMin

veil module DistFloodMinTooFewRounds

type node
type value
instantiate ord : TotalOrder value
open TotalOrder
immutable individual f : Nat
immutable function input : node → value

network (synchrony := sync) (faults := crash f)

message est (v : value)

var x : value := input self
var r : Nat := 0
var decided : Bool := false

program (self : node) {
  -- one round too few
  while r < f do
    broadcast (est x)
    next_round
    let m :| (m = x ∨ received (est m)) ∧ le m x ∧ ∀ w, received (est w) → le m w
    x := m
    r := r + 1
  decided := true
}

#gen_spec

-- with `f = 1`: a node crashes after reaching only some of the others
sat trace [disagreement] {
  node_start
  node_start
  node_start
  net_crash
  net_drop_est
  net_next_round
  node_round2
  node_round2
  assert (∃ a b, correct a ∧ correct b ∧ decided a ∧ decided b ∧ x a ≠ x b)
}

end DistFloodMinTooFewRounds
