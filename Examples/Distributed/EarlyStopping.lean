module

public import Veil

/-! # Early-deciding consensus: round complexity that depends on the run

Consensus in a synchronous network where up to `t` nodes may crash. Plain
FloodSet always takes `t + 1` rounds. Here a node decides as soon as it sees a
round without a new crash -- it hears from every node it heard from in the
previous round -- and then tells the others, who decide one round later. So
the number of rounds depends on the number of crashes `f` that actually
happen, not on the budget `t`: at most `min (f + 1, t + 1)` rounds
(`rounds_bound` and `rounds_cap` below).

Both ends of the bound are reached in the instance checked below (3 nodes,
`t = 2`). A run without crashes takes a single round: every node hears
everyone, so they all decide right away. A run with 2 crashes can take all
`t + 1 = 3` rounds: if nodes 0 and 2 crash in the first round, node 1 hears
from fewer nodes in each round than in the one before, so it never sees a
crash-free round.

The bound is checked by the model checker. Proving it for all instances needs
a counting argument -- each extra round is paid for by a different crashed
node -- that SMT cannot do directly, so it would be an interactive proof.
-/

veil module DistEarlyStopping

type node
type value
instantiate ord : TotalOrder value
open TotalOrder
immutable individual t : Nat
immutable function input : node → value

network (synchrony := sync) (faults := crash t) (complexity := true)

message est (v : value)
message early (v : value)

var x : value := input self
var heardPrev : node → Bool := fun _ => true
var r : Nat := 0
var isEarly : Bool := false
var decided : Bool := false
var decision : value := input self

program (self : node) {
  while r < t + 1 ∧ ¬ isEarly do
    broadcast (est x)
    next_round
    r := r + 1
    if ∃ v, received (early v) then
      -- someone decided early: adopt its value
      let v :| received (early v) ∧ ∀ w, received (early w) → le v w
      x := v
      isEarly := true
    else
      let m :| (m = x ∨ received (est m)) ∧ le m x ∧ ∀ w, received (est w) → le m w
      x := m
      -- no new crash: everyone heard last round was heard again
      if ∀ s, heardPrev s → ∃ v, received (est v) from s then
        isEarly := true
      heardPrev S := decide (∃ v, received (est v) from S)
  if isEarly then
    broadcast (early x)
  decision := x
  decided := true
}

#desugar_program

safety [agreement] correct A ∧ correct B ∧ decided A ∧ decided B → decision A = decision B
safety [validity] decided A → ∃ n, decision A = input n
invariant [rounds_bound] net_rounds ≤ net_crashes + 1
invariant [rounds_cap] net_rounds ≤ t + 1
termination [correct_nodes_decide] ∀ n, correct n → decided n

#gen_spec

#model_check { node := Fin 3, value := Fin 2 } { t := 2, input := fun n => if n = 0 then 0 else 1 }

-- #check_invariants

end DistEarlyStopping
