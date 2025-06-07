import Veil

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


end Foo

-- You can continue working on the same module, even in a different file!
/-- info: Module Foo already exists. Importing it here. -/
#guard_msgs in
veil module Foo

-- the same section variables are available
/-- info: node : Type -/
#guard_msgs in
#check node
/-- info: tot : TotalOrder node -/
#guard_msgs in
#check tot


-- You can do all the checks
/--
info: Initialization must establish the invariant:
  single_leader ... ✅
  inv_1 ... ✅
  inv_2 ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  send
    termination ... ✅
    single_leader ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
  recv
    termination ... ✅
    single_leader ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
-/
#guard_msgs(info, drop warning) in
#check_invariants

end Foo
