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
  pending sender n := false
  if (sender = n) then
    leader n := true
  else
    if (le n sender) then
      pending sender next := true
}

safety [single_leader] leader N ∧ leader M → N = M
invariant [leader_greatest] leader L → le N L
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

#time #gen_spec

#check_invariants

set_option trace.veil.desugar true
#model_check { node := Fin 6 }

sat trace {
  any 3 actions
  assert (∃ l, leader l)
}

unsat trace {
  any 5 actions
  assert (∃ n₁ n₂, n₁ ≠ n₂ ∧ leader n₁ ∧ leader n₂)
}

end Ring
--
