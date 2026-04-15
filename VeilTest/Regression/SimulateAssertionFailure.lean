import Veil

set_option linter.unusedVariables false

veil module SimulateAssertionFailure

type node

relation pending : node -> node -> Bool

#gen_state

after_init {
  pending M N := false
}

action send (n next : node) {
  assert false
  pending n next := true
}

invariant true

/-- error: This assertion might fail when called from send -/
#guard_msgs in
#gen_spec

/--
error: ❌ Violation: assertion_failure
  State 0 (via init):
    pending = []
  State 1 (via send(n=0, next=0)):
    pending = []
-/
#guard_msgs in
#simulate interpreted { node := Fin 2 } {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

end SimulateAssertionFailure
