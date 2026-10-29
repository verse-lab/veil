module

public import Veil

set_option veil.smt.trust false
set_option veil.printCounterexamples false

namespace UniversalAssignmentGlobals
public abbrev N : Bool := false
end UniversalAssignmentGlobals

open UniversalAssignmentGlobals

veil module UniversalAssignmentTemplate

relation filled : Bool → Bool
individual imported : Bool

-- An unbound capitalized target coordinate is universal even when a Lean
-- declaration has the same name. Imports must not change this program.
after_init {
  filled N := true
  imported := N
}
action fill { filled N := true }

invariant [all_filled] ∀ b : Bool, filled b
invariant [global_value] imported = false

#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
end UniversalAssignmentTemplate

veil module UniversalAssignmentComposition

isolate table : UniversalAssignmentTemplate

safety [all_filled] (∀ b : Bool, table.filled b) ∧ table.imported = false

#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems
#check all_filled.is_inv

end UniversalAssignmentComposition

veil module PointCapitalTemplate

individual chosen : Bool
relation selected : Bool → Bool

after_init {
  chosen := false
  selected B := false
  selected chosen := true
}

-- The parameter N is a point coordinate, despite its capitalization and
-- the global N. B is an independent universal binder scoped to its write.
action choose (N : Bool) {
  chosen := N
  selected B := false
  selected N := true
}

invariant [exact_choice] ∀ b : Bool, selected b ↔ b = chosen

#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
end PointCapitalTemplate

veil module PointCapitalComposition

isolate table : PointCapitalTemplate
safety [exact_choice] ∀ b : Bool, table.selected b ↔ b = table.chosen

#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems
#check exact_choice.is_inv

end PointCapitalComposition

veil module DeferredCapitalTemplate

param source : UniversalAssignmentTemplate
individual N : Bool
relation selected : Bool → Bool

after_init {
  N := false
  selected B := false
  selected N := true
}

action choose (n : Bool) {
  N := n
  selected B := false
  selected N := true
}

invariant [exact_choice] ∀ b : Bool, selected b ↔ b = N

#gen_spec
end DeferredCapitalTemplate

veil module DeferredCapitalComposition

isolate provider : UniversalAssignmentTemplate
isolate table : DeferredCapitalTemplate (source := provider) with provider

safety [exact_choice] ∀ b : Bool, table.selected b ↔ b = table.N

#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems
#check exact_choice.is_inv

end DeferredCapitalComposition
