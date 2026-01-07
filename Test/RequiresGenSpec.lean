import Veil

/-!
# Tests that commands requiring finalized spec throw errors without #gen_spec

These tests verify that `#check_invariants`, `#model_check`, and `sat trace`/`unsat trace`
all throw an appropriate error message when called before `#gen_spec`.
-/

veil module TestCheckInvariants

individual flag : Bool

#gen_state

after_init { flag := false }

action set_flag { flag := true }

invariant ¬ flag

/-- error: The specification of module TestCheckInvariants has not been finalized. Please call #gen_spec first! -/
#guard_msgs in
#check_invariants

end TestCheckInvariants


veil module TestModelCheck

individual flag : Bool

#gen_state

after_init { flag := false }

action set_flag { flag := true }

invariant ¬ flag

/-- error: The specification of module TestModelCheck has not been finalized. Please call #gen_spec first! -/
#guard_msgs in
#model_check (Fin 2)

end TestModelCheck


veil module TestSatTrace

individual flag : Bool

#gen_state

after_init { flag := false }

action set_flag { flag := true }

invariant ¬ flag

/-- error: The specification of module TestSatTrace has not been finalized. Please call #gen_spec first! -/
#guard_msgs in
sat trace { }

end TestSatTrace


veil module TestUnsatTrace

individual flag : Bool

#gen_state

after_init { flag := false }

action set_flag { flag := true }

invariant ¬ flag

/-- error: The specification of module TestUnsatTrace has not been finalized. Please call #gen_spec first! -/
#guard_msgs in
unsat trace {
  any 1 actions
  assert flag
}

end TestUnsatTrace
