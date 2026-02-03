import Veil

veil module Ring


type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node → Bool
relation pending : node → node → Bool
individual flag : Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
  flag := false
}

action fail {
  assert false
}

action fail_req {
  require false
}

action call_fail_req {
  fail_req
}

safety [single_leader] leader L → le N L
invariant [not_flag] ¬ flag
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

/--
error: This assertion might fail when called from fail
---
error: This assertion might fail when called from call_fail_req
-/
#guard_msgs in
#gen_spec

set_option veil.printCounterexamples false

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  single_leader ... ✅
  not_flag ... ✅
  inv_1 ... ✅
  inv_2 ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  fail
    doesNotThrow ... ❌
    single_leader ... ✅
    not_flag ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
  call_fail_req
    doesNotThrow ... ❌
    single_leader ... ✅
    not_flag ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
  fail_req
    doesNotThrow ... ✅
    single_leader ... ✅
    not_flag ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
-/
#guard_msgs in
#check_invariants

end Ring
