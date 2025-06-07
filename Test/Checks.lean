import Veil.DSL
import Veil.Std

veil module Ring


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
#guard_msgs(info, error, drop warning) in
#check_invariants

/--
info: The following set of actions must preserve the invariant and successfully terminate:
  recv
    termination ... ✅
    single_leader ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
-/
#guard_msgs(info, error, drop warning) in
#check_action recv

/--
info: The following set of actions must preserve the invariant and successfully terminate:
  send
    termination ... ✅
    single_leader ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
-/
#guard_msgs(info, error, drop warning) in
#check_action send

/--
info: Initialization must establish the invariant:
  single_leader ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  send
    termination ... ✅
    single_leader ... ✅
  recv
    termination ... ✅
    single_leader ... ✅
-/
#guard_msgs(info, error, drop warning) in
#check_invariant single_leader

end Ring
