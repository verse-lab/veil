import Veil

veil module DijkstraRing

class FiniteRing (t : Type) where
  -- relation: strict total order
  le (x y : t) : Prop
  -- axioms
  le_refl (x : t) : le x x
  le_trans (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total (x y : t) : le x y ∨ le y x

  -- relation: nonstrict total order
  lt (x y : t) : Prop
  le_lt (x y : t) : lt x y ↔ (le x y ∧ x ≠ y)

  bottom : t
  bottom_lt (x : t) : le bottom x

  top : t
  top_gt (x : t) : le x top

  bottom_neq_top : bottom ≠ top

  -- successor on the ring
  next (x y : t) : Prop
  next_def (x y : t) : next x y ↔ ((lt x y ∧ ∀ z, lt x z → le y z) ∨ (y = top ∧ x = bottom))


type node
instantiate ring : FiniteRing node

open FiniteRing

function x : node → Prop
function up : node → Prop

#gen_state

invariant [up_bottom] up (ring.bottom) = True
invariant [up_top] up (ring.top) = False


ghost relation hasPrivilege (s : node) :=
  ∀ (l r : node), next l s ∧ next s r →
    if s = ring.bottom then
      (x s = x r) ∧ (¬ up r)
    else if s == ring.top then
      x s ≠ x l
    else
      (x s ≠ x l) ∨ ((x s = x r) ∧ (up s) ∧ (¬ up r))

safety [at_least_one_privilege] ∃ n, hasPrivilege n

after_init {
  up (ring.bottom) := True
  up (ring.top) := False
}

action step (s : node) = {
  let (l, r) :| next l s ∧ next s r
  if s = ring.bottom then
    if x s = x r ∧ (¬ up r) then
      x s := ¬ x s
  else
    if s = ring.top then
      if x s ≠ x l then
          x s := ¬ x s
    else
      if x s ≠ x l then
        x s := ¬ x s
        up s := True
      if x s = x r ∧ up s ∧ (¬ up r) then
        up s := False
}

#gen_spec

#check_invariants

set_option veil.smt.translator "lean-smt"
set_option veil.smt.solver "cvc5"
set_option maxHeartbeats 10000000

sat trace [initial_state_exists] { } by bmc_sat

unsat trace [cannot_revert_to_more_than_one_privilege] {
  assert (∃ (a : node), hasPrivilege a ∧ (∀ (b : node), a ≠ b → ¬ hasPrivilege b))
  any 10 actions
  assert (∃ (a b : node), a ≠ b ∧ hasPrivilege a ∧ hasPrivilege b)
} by bmc

unsat trace [bounded_safety] {
  any 10 actions
  assert ¬ at_least_one_privilege
} by { bmc }


end DijkstraRing
