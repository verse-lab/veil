import Veil.Core

veil module CoreRelationalTransition
individual flag : Bool
after_init { flag := false }
transition toggle { flag' = !flag }
invariant !flag
#gen_spec

/--
warning: Explicit state model checking of transitions is SLOW!

The current implementation enumerates all possible states and filters those satisfying the transition relation. Your specification has 1 transition: toggle

Consider encoding transitions as imperative actions where possible.
---
error: ❌ Violation: safety_failure (violates: inv_0)
  State 0 (via init):
    flag = false
  State 1 (via toggle):
    flag = true
-/
#guard_msgs in
#model_check interpreted {} {} (sequential := true)
end CoreRelationalTransition

veil module CoreAssertionCounterexample
individual flag : Bool
after_init { flag := false }
action fail_assert { assert flag }
invariant true
#gen_spec

/--
error: ❌ Violation: assertion_failure
  State 0 (via init):
    flag = false
  State 1 (via fail_assert):
    flag = false
-/
#guard_msgs in
#model_check interpreted {} {} (sequential := true)
end CoreAssertionCounterexample
