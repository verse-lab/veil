import Veil.DSL
import Examples.DSL.Std

namespace Ring
open Classical

type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node → Prop
relation pending : node → node → Prop

#gen_state

after_init {
  leader N := False
  pending M N := False
}

action send (n next : node) = {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := True
}

action recv (sender n next : node) = {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  pending sender n := *
  if (sender = n) then
    leader n := True
  else
    if (le n sender) then
      pending sender next := True
}

safety [single_leader] leader L → le N L
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

#gen_spec


/-- info:
Initialization must establish the invariant:
  Ring.single_leader ... ✅
  Ring.inv_1 ... ✅
  Ring.inv_2 ... ✅
The following set of actions must preserve the invariant:
  send
    Ring.single_leader ... ✅
    Ring.inv_1 ... ✅
    Ring.inv_2 ... ✅
  recv
    Ring.single_leader ... ✅
    Ring.inv_1 ... ✅
    Ring.inv_2 ... ✅
-/
#guard_msgs in
#check_invariants

/-- info:
The following set of actions must preserve the invariant:
  recv
    Ring.single_leader ... ✅
    Ring.inv_1 ... ✅
    Ring.inv_2 ... ✅
-/
#guard_msgs in
#check_action recv

/-- info:
The following set of actions must preserve the invariant:
  send
    Ring.single_leader ... ✅
    Ring.inv_1 ... ✅
    Ring.inv_2 ... ✅
-/
#guard_msgs in
#check_action send

end Ring
