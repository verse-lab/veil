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
  assert inv_1
}

#gen_spec

/--
info: Initialization must establish the invariant:
  single_leader ... ✅
  inv_1 ... ✅
  inv_2 ... ✅
The following set of actions must preserve the invariant:
  send
    single_leader ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
---
warning: Trusting the SMT solver for 6 theorems.
-/
#guard_msgs in
#check_invariants

#guard_msgs(drop info, drop warning) in
sat trace { assert inv_1 } by bmc_sat

#guard_msgs(drop info, drop warning) in
unsat trace {
   any 3 actions
   assert ¬ (single_leader ∧ inv_1 ∧ inv_2)
} by bmc

end Foo
