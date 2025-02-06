import Veil.DSL
import Veil.Std

namespace Ring
open Classical

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

/-- info:
The following set of actions must preserve the invariant:
  ruin_inv
    single_leader ... ✅
    not_flag ... ❌
    inv_2 ... ✅
    inv_3 ... ✅
-/
#guard_msgs in
#check_action ruin_inv

end Ring
