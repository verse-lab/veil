import Veil

veil module Foo

type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node → Bool
relation pending : node → node → Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
}

procedure send_msg (fromNode : node) (toNode : node) {
  pending fromNode toNode := true
}

action send (n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  send_msg n next
}

safety [single_leader] leader L → le N L
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

#gen_spec

-- Note that `send_msg` doesn't show up in the invariant check, because
-- it's not an action.

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  single_leader ... ✅
  inv_0 ... ✅
  inv_1 ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  send
    doesNotThrow ... ✅
    single_leader ... ✅
    inv_0 ... ✅
    inv_1 ... ✅
-/
#guard_msgs(info, drop warning) in
#check_invariants

end Foo
