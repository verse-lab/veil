import Veil

/- TODO: fix it when we add procedures and specifications
veil module Foo

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

procedure send_msg (fromNode : node) (toNode : node) = {
  pending fromNode toNode := True
}

action send (n next : node) = {
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
  single_leader ... ✅
  inv_1 ... ✅
  inv_2 ... ✅
The following set of actions must preserve the invariant:
  send
    single_leader ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
-/
#guard_msgs(info, drop warning) in
#check_invariants

end Foo
-/
