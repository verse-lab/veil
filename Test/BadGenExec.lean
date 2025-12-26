import Veil

-- https://github.com/aman-goel/ivybench/blob/5db7eccb5c3bc2dd14dfb58eddb859b036d699f5/ex/ivy/ring.ivy

-- set_option trace.veil.desugar true

veil module Ring

type node
-- type foo

-- inductive Action (node : Type) where
--   | send (n next : node)
--   | recv (sender n next : node)
-- deriving Inhabited, Ord, Lean.ToJson, Hashable, BEq, Repr

instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node -> Bool
relation pending : node -> node -> Bool

#time #gen_state

after_init {
  -- log := []
  leader N := false
  pending M N := false
}

-- transition skip {
--   leader' = leader
-- }

action send (n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  -- log := log ++ [Action.send n next]
  pending n next := true
}

action recv (sender n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  -- log := log ++ [Action.recv sender n next]
  pending sender n := false
  if (sender = n) then
    leader n := true
  else
    -- pass message to next node
    if (le n sender) then
      pending sender next := true
}

-- action nondet_log  {
--   log := *
-- }

safety [single_leader] leader N ∧ leader M → N = M
-- invariant [leader_greatest] leader L → le N L
invariant [inv_1] pending S D ∧ btw S N D → le N S
invariant [inv_2] pending L L → le N L

#gen_spec

#check_invariants

#time #model_check { node := Fin 5, foo := Fin 1 } { }

end Ring
