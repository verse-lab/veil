import Veil.DSL
import Veil.Std

veil module Ring


type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node → Prop
relation pending : node → node → Prop
individual flag : Prop

#gen_state

after_init {
  leader N := False
  pending M N := False
  flag := False
}


action fail = {
  assert False
}

action fail_req = {
  require False
}

action call_fail_req = {
  fail_req
}

safety [single_leader] leader L → le N L
invariant [not_flag] ¬ flag
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

#gen_spec

/--
error: This assertion might fail when called from Ring.fail
---
info: The following set of actions must preserve the invariant and successfully terminate:
  fail
    termination ... ❌
    single_leader ... ✅
    not_flag ... ✅
    inv_2 ... ✅
    inv_3 ... ✅
---
info: Run with `set_option veil.printCounterexamples true` to print counter-examples.
---
error: The invariant is not inductive: one clause is not preserved!
-/
#guard_msgs(info, error, drop warning) in
#check_action fail

/--
info: The following set of actions must preserve the invariant and successfully terminate:
  fail_req
    termination ... ✅
    single_leader ... ✅
    not_flag ... ✅
    inv_2 ... ✅
    inv_3 ... ✅
-/
#guard_msgs(info, error, drop warning) in
#check_action fail_req

/--
error: This assertion might fail when called from Ring.call_fail_req
---
info: The following set of actions must preserve the invariant and successfully terminate:
  call_fail_req
    termination ... ❌
    single_leader ... ✅
    not_flag ... ✅
    inv_2 ... ✅
    inv_3 ... ✅
---
info: Run with `set_option veil.printCounterexamples true` to print counter-examples.
---
error: The invariant is not inductive: one clause is not preserved!
-/
#guard_msgs(info, error, drop warning) in
#check_action call_fail_req


/--
error: This assertion might fail when called from Ring.call_fail_req
---
info: The following set of actions must preserve the invariant and successfully terminate:
  call_fail_req
    termination ... ❌
    single_leader ... ✅
    not_flag ... ✅
    inv_2 ... ✅
    inv_3 ... ✅
---
info: Run with `set_option veil.printCounterexamples true` to print counter-examples.
---
error: The invariant is not inductive: one clause is not preserved!
-/
#guard_msgs(info, error, drop warning) in
#check_action call_fail_req

end Ring
