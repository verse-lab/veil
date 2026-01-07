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


action ruin_inv {
  flag := true
}

safety [single_leader] leader L → le N L
invariant [not_flag] ¬ flag
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

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
  ruin_inv
    doesNotThrow ... ✅
    single_leader ... ✅
    not_flag ... ❌
    inv_1 ... ✅
    inv_2 ... ✅
-/
#guard_msgs in
#check_invariants

end Ring
