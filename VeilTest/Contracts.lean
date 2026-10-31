module

public import Veil

set_option veil.smt.trust false
set_option veil.printCounterexamples false
set_option veil.solver "grind+smt"

/-! Checked postconditions and invocation-local entry snapshots. -/

veil module CheckedContracts

type node
individual flag : Bool
relation entries : node → Bool

after_init {
  flag := false
  entries B := false
}

-- This helper temporarily breaks the action-boundary invariant. Its contract
-- is established from arbitrary input states, without assuming that invariant.
procedure toggle {
  flag := !flag
  ensure flag = !old(flag)
}

procedure insert (b : node) {
  entries b := true
  ensure ∀ u : node, entries u ↔ old(entries u) ∨ u = b
}

action roundtrip (b : node) {
  toggle
  toggle
  insert b
  ensure flag = old(flag)
  ensure ∀ u : node, old(entries u) → entries u
}

-- A final return follows all checks and preserves the real procedure result.
procedure result_after_check (b : Bool) {
  ensure b = b
  return b
}

-- External certificates may require the boundary invariant. The corresponding
-- premise must stay in the certificate; it is never granted at internal calls.
action boundary_guarantee {
  ensure ¬flag
}

invariant [flag_false] ¬flag

#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems

end CheckedContracts

veil module ContractDiagnostics

individual flag : Bool

after_init { flag := false }

/-- error: Error in action old_outside_ensure: `old` is only available inside an `ensure` postcondition -/
#guard_msgs(error, drop warning) in
action old_outside_ensure {
  assert old(flag)
}

/-- error: Error in action old_body_local: `old` cannot refer to body-local `answer`: it is unavailable at invocation entry -/
#guard_msgs(error, drop warning) in
action old_body_local {
  let answer := flag
  ensure old(answer) = answer
}

/-- error: Error in action bypass_postcondition: early returns in an action with `ensure` are not supported: a return could bypass its postconditions -/
#guard_msgs(error, drop warning) in
action bypass_postcondition {
  if flag then
    return ()
  ensure flag
}

procedure set_flag_true {
  flag := true
  return flag
}

/-- error: Error in action effect_after_postcondition: effects in the final return of an action with `ensure` are not supported: evaluate the return value before its postconditions -/
#guard_msgs(error, drop warning) in
action effect_after_postcondition {
  require ¬flag
  ensure ¬flag
  return (← set_flag_true)
}

macro "hiddenFlagEffect" : term => `((← set_flag_true))

/-- error: Error in action effectful_postcondition: effects are not supported inside `ensure` postconditions -/
#guard_msgs(error, drop warning) in
action effectful_postcondition {
  ensure hiddenFlagEffect
}

/-- error: effects are not supported in contract entry requirements: evaluate effects before calling the procedure -/
#guard_msgs(error, drop warning) in
action effectful_entry_requirement {
  require hiddenFlagEffect
  ensure flag
}

/-- error: Error in action hidden_effect_after_postcondition: effects in the final return of an action with `ensure` are not supported: evaluate the return value before its postconditions -/
#guard_msgs(error, drop warning) in
action hidden_effect_after_postcondition {
  ensure ¬flag
  return hiddenFlagEffect
}

end ContractDiagnostics

-- An unused procedure must still establish its own ensure. Giving it the
-- owner's invariant would make this invalid contract appear provable.
set_option veil.solver "smt"

veil module RejectedContract

individual flag : Bool
after_init { flag := true }

procedure unjustified {
  ensure flag
}

procedure explicit_requirement {
  require flag
  ensure flag
}

action idle { pure () }
invariant [flag_true] flag

#gen_spec

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  flag_true ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  unjustified
    contract ... ❌
  explicit_requirement
    contract ... ✅
  idle
    doesNotThrow ... ✅
    flag_true ... ✅
-/
#guard_msgs(error, drop info, drop warning) in
#check_invariants

end RejectedContract
