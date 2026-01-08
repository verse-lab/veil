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

immutable function natToBlock : Nat → block

individual pickedBlock : block

#gen_state

after_init {
  blist := [natToBlock 3]
  bset := inst1.insert (natToBlock 1) (inst1.insert (natToBlock 2) (inst1.insert (natToBlock 4) inst1.empty))
  bmset := inst2.insert (natToBlock 5) (inst2.insert (natToBlock 5) (inst2.insert (natToBlock 5) inst2.empty))
  pickedBlock := natToBlock 0
}

#guard_msgs in
action pick_from_list {
  let b1 :| b1 ∈ blist
  pickedBlock := b1
}

#guard_msgs in
action pick_from_set {
  let b2 : block :| b2 ∈ bset
  pickedBlock := b2
}

#guard_msgs in
action pick_from_multiset {
  let b3 : block :| b3 ∈ bmset
  pickedBlock := b3
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``pick_from_list

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``pick_from_set

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``pick_from_multiset

invariant pickedBlock ≠ natToBlock 6

#guard_msgs in
#gen_spec

#model_check interpreted { block := Nat
                           blockSet := Std.ExtTreeSet Nat
                           blockMultiset := Std.ExtTreeMap Nat Nat } { natToBlock := id }
