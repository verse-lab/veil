import Veil

-- https://github.com/aman-goel/ivybench/blob/5db7eccb5c3bc2dd14dfb58eddb859b036d699f5/ex/ivy/ring.ivy

veil module Ring


type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node -> Bool
relation pending : node -> node -> Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
}

action send (n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := true
}

action recv (sender n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  -- message may or may not be removed
  -- this models that multiple messages might be in flight
  let b ← pick Bool
  pending sender n := b
  if (sender = n) then
    leader n := true
  else
    -- pass message to next node
    if (le n sender) then
      pending sender next := true
}

safety [single_leader] leader N ∧ leader M → N = M
invariant [leader_greatest] leader L → le N L
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L
termination true = true

#gen_spec

#check_invariants

#model_check { node := Fin 5 } { }

sat trace [can_elect_leader_explicit] {
  send
  assert (∃ n next, pending n next)
  recv
  recv
  assert (∃ l, leader l)
} by { sorry }

sat trace [can_elect_leader] {
  any 3 actions
  send
  assert (∃ l, leader l)
} by { sorry }

unsat trace [trace_any] {
  any 6 actions
  assert ¬ (leader L → le N L)
} by { sorry }


end Ring
--
