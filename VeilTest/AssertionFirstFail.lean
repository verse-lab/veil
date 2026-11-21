module

public import Veil

set_option linter.unusedVariables false

veil module Ring

type node

relation pending : node -> node -> Bool

#gen_state

after_init {
  pending M N := false
}

action send (n next : node) {
  let b ← pick Bool
  if b then
    assert false
  pending n next := true
}

invariant true

/-- warning: This assertion can fail even if the module's invariants hold when `send` starts. -/
#guard_msgs in
#gen_spec

/--
error: ❌ Violation: assertion_failure
  State 0 (via init):
    pending = {}
  State 1 (via send(n=0, next=0)):
    choices: b = true
    pending = {}
-/
#guard_msgs in
#model_check interpreted { node := Fin 2 } {}

end Ring

veil module InitAssertion

individual ready : Bool
after_init {
  ready := false
  assert ready
}
action reset { ready := true }
invariant ready

/-- warning: This assertion can fail during initialization. -/
#guard_msgs in
#gen_spec

end InitAssertion
