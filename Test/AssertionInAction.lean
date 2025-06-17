import Veil

veil module Foo

type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node → Prop
relation pending : node → node → Prop

#gen_state

safety [single_leader] leader L → le N L
invariant [inv_1] pending S D ∧ btw S N D → le N S
invariant [inv_2] pending L L → le N L

#guard_msgs in
after_init {
  assume single_leader
  assume inv_1
  require inv_2
}

ghost relation isNext (n next : node) :=
  (n ≠ next) ∧ (∀ N', (N' ≠ n ∧ N' ≠ next) → ¬ btw n N' next)

#guard_msgs in
procedure foo = {
  assert inv_1
}

#guard_msgs in
action send (n next : node) = {
  require isNext n next
  pending n next := True
}

#gen_spec

#guard_msgs(drop info, drop warning) in
sat trace { assert inv_1 } by bmc_sat

end Foo
