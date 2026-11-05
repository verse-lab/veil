module

public import Veil

/-! # FloodSet as a distributed program

The FloodSet consensus protocol of `Examples/Demo/FloodSet/FloodSet.lean`, written as
the program every node runs. The network is synchronous, and at most `f` nodes
crash; a node that crashes during a round may have sent its messages of that
round to only some of the nodes. Every node starts with its own input, and for
`f + 1` rounds broadcasts every value it has seen and adds the values it
receives. It then decides the smallest value it has seen.
-/

veil module FloodSetProgram

type node
type value
instantiate val_ord : TotalOrder value
open TotalOrder

immutable individual f : Nat

network (synchrony := sync) (faults := crash f) (complexity := true)

message est (v : value)

var input : value := *                 -- initial proposal
var W : value → Bool := fun _ => false -- values seen so far
var r : Nat := 0                       -- rounds completed
var decided : Bool := false
var decision : value := *

program (self : node) {
  W V := decide (V = input)
  while r < f + 1 do
    broadcast (est V) if W V
    next_round
    W V := decide (W V ∨ received (est V))
    r := r + 1
  let v :| W v ∧ ∀ w, W w → le v w
  decision := v
  decided := true
}

/-! ## Properties -/

safety [agreement] decided A ∧ decided B → decision A = decision B
safety [validity] decided A → ∃ n, decision A = input n

/-! ## Inductive invariant

The argument: at most `f` of the `f + 1` rounds have a crash, and after a
round without one every node that is still running holds the same set `W`,
because every running node sent it its whole set. From then on the nodes only
receive values from each other, so their sets stay equal, and they decide the
same minimum.

`seen n` is the set `n` holds once it has taken its step in the current round:
`W n` after the step, `W n` with the values received before it. -/

ghost relation seen (n : node) (v : value) :=
  (net_ready n ∧ (W n v ∨ ∃ s, est_in s n v)) ∨ (¬ net_ready n ∧ W n v)

-- `n` takes part in the current round: it is running, or it crashed in this
-- round after taking its step (so some of its messages may still arrive).
ghost relation participant (n : node) :=
  pc n ≠ pc_crashed ∨ (net_crashing n ∧ r n = net_rounds)

-- bounds
invariant [crash_bound] net_crashes ≤ f
invariant [rounds_bound] net_rounds ≤ f + 1
invariant [crashing_counted] net_crashing N → net_crashes ≥ 1
invariant [crashing_crashed] net_crashing N → pc N = pc_crashed
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
invariant [decision_min] decided N → W N (decision N) ∧ ∀ w, W N w → le (decision N) w
-- the messages of the round
invariant [silent_before_step] net_ready S → est_out S D V = false
invariant [out_value]
  est_out S D V → W S V ∧ r S = net_rounds ∧ (pc S = pc_round2 ∨ net_crashing S)
invariant [out_complete] pc S = pc_round2 ∧ ¬ net_ready S → W S V → est_out S D V
-- validity: every value around is someone's input
invariant [W_inputs] W N V → ∃ n, V = input n
invariant [in_inputs] est_in S D V → ∃ n, V = input n
-- agreement: after a round without a crash, the participants hold the same set
invariant [settled]
  (net_crashes < net_rounds ∨ ((∃ n, net_crashing n) ∧ net_crashes ≤ net_rounds)) →
  participant A → participant B → (seen A V ↔ seen B V)

set_option veil.smt.trust false

#gen_spec

#model_check { node := Fin 3, value := Fin 2 } { f := 1 }

-- SMT proves this one, but its proof does not reconstruct. A node that has not
-- started is in round 0 with `r = 0`, so its first step never decides.
prove_veil_invariant_goal node_start decision_min using wp by
  rcases hinv with ⟨-, -, -, -, -, -, hround0, hlater, hdone, hmin, -⟩
  have hd := pc_label_Enum.distinct
  simp only [distinctN_cons, List.mem_cons, List.not_mem_nil] at hd
  intro hstart _
  have hr : st.r self = 0 := by
    by_cases h0 : st.net_rounds = 0
    · rcases hround0 self h0 with ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp_all
    · rcases hlater self (by omega) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp_all
  rw [if_pos (by omega)]
  intro N hdec
  have hne : self ≠ N := by
    rintro rfl
    simp_all
  simp only [hne, if_false]
  exact hmin N hdec

#check_invariants

end FloodSetProgram
