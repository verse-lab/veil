module

public import Veil

/-! Two-phase commit: multi-way and selective `recv`, a `while` loop that
blocks inside its body, and per-node function-valued variables. -/

veil module DistTwoPhaseCommit

type node
immutable individual coord : node
immutable relation willing : node → Bool

network (synchrony := async)

message prepare
message vote (yes : Bool)
message outcome (commit : Bool)

var heard : node → Bool := fun _ => false
var aborted : Bool := false
var decided : Bool := false
var commit : Bool := false

program (self : node) {
  if self = coord then
    broadcast prepare
    while ¬ aborted ∧ ¬ (∀ n, n ≠ coord → heard n) do
      recv
      | (vote true) from p => heard p := true
      | (vote false) from _p => aborted := true
    decided := true
    commit := decide (¬ aborted)
    broadcast (outcome (decide (¬ aborted)))
  else
    recv prepare from c
    send (vote (willing self)) to c
    recv (outcome b)
    decided := true
    commit := b
}

safety [agreement] decided A ∧ decided B → commit A = commit B
safety [validity] decided A ∧ commit A → N = coord ∨ willing N

-- the coordinator and the participants run different branches
invariant [coord_branch] pc coord ≠ pc_recv1 ∧ pc coord ≠ pc_recv2
invariant [participant_branch] N ≠ coord → pc N ≠ pc_recv4
-- what the messages in flight say
invariant [prepare_from_coord] prepare_net S D → S = coord
invariant [vote_is_willingness] vote_net S D B → D = coord ∧ S ≠ coord ∧ B = willing S
invariant [outcome_is_decision] outcome_net S D B → S = coord ∧ decided coord ∧ B = commit coord
-- the coordinator only records a yes from willing nodes, and decides once
invariant [heard_willing] heard coord N → willing N
invariant [coord_decides_last] decided coord ↔ pc coord = pc_done
invariant [coord_commit]
  decided coord → (commit coord ↔ ¬ aborted coord ∧ ∀ n, n ≠ coord → heard coord n)
-- participants copy the coordinator's decision
invariant [participant_copies] N ≠ coord ∧ decided N → decided coord ∧ commit N = commit coord

#gen_spec

#check_invariants

end DistTwoPhaseCommit
