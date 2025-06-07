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

macro "test_check_invariants" : command => `(command|
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
---
warning: Trusting the SMT solver for 11 theorems.
-/
#guard_msgs in
#check_invariants)

macro "test_check_invariants'" : command => `(command|
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
---
warning: Trusting the SMT solver for 9 theorems.
-/
#guard_msgs in
#check_invariants)


macro "test_check_action_recv" : command => `(command|
/--
info: The following set of actions must preserve the invariant and successfully terminate:
  recv
    termination ... ✅
    single_leader ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
---
warning: Trusting the SMT solver for 4 theorems.
-/
#guard_msgs in
#check_action $(Lean.mkIdent `recv))

macro "test_check_action_send" : command => `(command|
/--
info: The following set of actions must preserve the invariant and successfully terminate:
  send
    termination ... ✅
    single_leader ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
---
warning: Trusting the SMT solver for 4 theorems.
-/
#guard_msgs in
#check_action $(Lean.mkIdent `send))

macro "test_check_invariant_single_leader" : command => `(command|
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
---
warning: Trusting the SMT solver for 5 theorems.
-/
#guard_msgs in
#check_invariant $(Lean.mkIdent `single_leader))


set_option veil.smt.translator "lean-smt"
set_option veil.smt.solver "z3"

test_check_invariants'
test_check_action_recv
test_check_action_send
test_check_invariant_single_leader

set_option veil.smt.translator "lean-smt"
set_option veil.smt.solver "cvc5"

test_check_invariants
test_check_action_recv
test_check_action_send
test_check_invariant_single_leader

set_option veil.smt.translator "lean-auto"
set_option veil.smt.solver "z3"

test_check_invariants
test_check_action_recv
test_check_action_send
test_check_invariant_single_leader

set_option veil.smt.translator "lean-auto"
set_option veil.smt.solver "cvc5"

test_check_invariants
test_check_action_recv
test_check_action_send
test_check_invariant_single_leader

end Ring


/-
The following set of actions must preserve the invariant and successfully terminate:
  recv
    termination ... ✅
    single_leader ... ✅
    inv_1 ... ✅
    inv_2 ... ✅

The following set of actions must preserve the invariant and successfully terminate:
  recv
    termination ... ✅
    single_leader ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
-/
