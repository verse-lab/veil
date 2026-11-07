module

public import VeilTest.ActionExecution
public meta import VeilTest.ActionExecution

/-!
Adding a proof binder must still elaborate a ghost predicate with implicit
theory/state arguments. A generated subtype pattern must not attempt to
match its proof before those arguments' metavariables have been resolved.
-/

set_option linter.unusedVariables false

open VeilTest.ActionExecution

veil module ProofBinderGhostPredicates

type node
relation marker : node → Bool

#gen_state

ghost relation same_as (n m : node) := n = m

-- Controls: the same predicate without a proof, and the proof forms that
-- bind their result directly rather than generating a pattern match.
procedure plain_pick (n : node) {
  let x : node :| same_as n x
  return x
}

procedure plain_assume (n m : node) {
  assume same_as n m
  return n
}

procedure require_proof (n : node) {
  require h : same_as n n
}

procedure assert_proof (n : node) {
  assert h : same_as n n
}

procedure pick_proof (n : node) {
  let x : node :| h : same_as n x
  have : n = x := h
  return x
}

procedure assume_proof (n m : node) {
  assume h : same_as n m
  have : n = m := h
  return n
}

def initial : State (FieldConcreteType Bool) := { marker := default }

#guard [false, true].all fun n =>
  exactlyOneSuccess (__veil_exec_action% { node := Bool } {} initial (pick_proof n)) fun x _ => x == n
#guard [false, true].all fun n =>
  __veil_exec_action% { node := Bool } {} initial (pick_proof n) ==
    __veil_exec_action% { node := Bool } {} initial (plain_pick n)
#guard [false, true].all fun n => [false, true].all fun m =>
  __veil_exec_action% { node := Bool } {} initial (assume_proof n m) ==
    __veil_exec_action% { node := Bool } {} initial (plain_assume n m)
#guard hasNoExecutions (__veil_exec_action% { node := Bool } {} initial (assume_proof true false))

end ProofBinderGhostPredicates
