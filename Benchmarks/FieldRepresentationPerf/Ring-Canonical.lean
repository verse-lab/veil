module

public import Veil

veil module Ring

type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node → Bool
relation pending : node → node → Bool

veil_set_field_representation relation Veil.CanonicalField
veil_set_field_representation function Veil.CanonicalField

#gen_state

after_init {
  leader N := false
  pending M N := false
}

ghost relation isNext (n : node) (next : node) :=
  ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)

action send (n next : node) {
  require isNext n next
  pending n next := true
}

action recv (sender n next : node) {
  require isNext n next
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
invariant [self_msg_greatest] pending L L → le N L
invariant [drop_smaller] pending S D ∧ btw S N D → le N S

#time #gen_spec

#model_check compiled { node := Fin 8 } { } (seenSet := HAMTMapShard)

-- sat trace {
--   any 3 actions
--   assert (∃ l, leader l)
-- }

-- unsat trace {
--   any 5 actions
--   assert (∃ n₁ n₂, n₁ ≠ n₂ ∧ leader n₁ ∧ leader n₂)
-- }

-- Uncomment to check
-- #check_invariants

end Ring
