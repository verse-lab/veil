import Veil
import Test.TestUtil

set_option linter.unusedVariables false

veil module Test

type block
individual blist : List block

type blockSet
instantiate inst1 : TSet block blockSet
individual bset : blockSet

type blockMultiset
instantiate inst2 : TMultiset block blockMultiset
individual bmset : blockMultiset

#gen_state

after_init {
  pure ()
}

#guard_msgs in
action pick_pick_pick {
  let b1 :| b1 ∈ blist
  let b2 : block :| b2 ∈ bset
  let b3 : block :| b3 ∈ bmset
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``pick_pick_pick

invariant true

#guard_msgs in
#gen_spec
