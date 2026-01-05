import Veil

set_option linter.unusedVariables false

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
invariant [inv_1] pending S D ∧ btw S N D → le N S
invariant [inv_2] pending L L → le N L

#gen_spec

#check_invariants

#model_check { node := Fin 5 } { }

end Ring
