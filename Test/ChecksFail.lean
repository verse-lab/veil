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


action ruin_inv = {
  flag := True
}

safety [single_leader] leader L → le N L
invariant [not_flag] ¬ flag
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

#gen_spec

/--
info: The following set of actions must preserve the invariant:
  ruin_inv
    single_leader ... ✅
    not_flag ... ❌
    inv_2 ... ✅
    inv_3 ... ✅
---
info: Run with `set_option veil.printCounterexamples true` to print counter-examples.
---
error: The invariant is not inductive: one clause is not preserved!
-/
#guard_msgs(info, error, drop warning) in
#check_action ruin_inv

/--
info: The following set of actions must preserve the invariant:
  ruin_inv
    single_leader ... ✅
    not_flag ... ❌
    inv_2 ... ✅
    inv_3 ... ✅
---
info: Run with `set_option veil.printCounterexamples true` to print counter-examples.
---
warning: Trusting the SMT solver for 3 theorems.
---
warning: The invariant is not inductive: one clause is not preserved!
-/
#guard_msgs in
set_option veil.failedCheckThrowsError false in
#check_action ruin_inv

end Ring
