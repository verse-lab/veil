module

public import Veil

-- Assertions must be checked even when the invariant is the empty conjunction.
veil module AssertWithoutInvariants

type node
relation r : node → Bool
#gen_state

after_init { r N := false }

action a (n : node) {
  require r n
  assert r n
}

/-- warning: you have not defined any invariants or temporal properties for this specification; did you forget? -/
#guard_msgs in
#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  a
    doesNotThrow ... ✅
-/
#guard_msgs in
#check_invariants

end AssertWithoutInvariants

-- Also check deferred generation and ensure a false assertion is rejected.
veil module DeferredAssertWithoutInvariants
set_option veil.deferVCGeneration true
set_option veil.printCounterexamples false

individual flag : Bool
#gen_state
after_init { flag := false }
action fail { assert false }

/-- warning: you have not defined any invariants or temporal properties for this specification; did you forget? -/
#guard_msgs in
#gen_spec

/--
error: This assertion might fail when called from fail
---
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  fail
    doesNotThrow ... ❌
-/
#guard_msgs in
#check_invariants

end DeferredAssertWithoutInvariants
