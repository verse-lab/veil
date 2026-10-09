module

public import VeilTest.ActionExecution
public meta import VeilTest.ActionExecution

/-!
# Regression: state reads through types, generated syntax and captured values

Field reads must observe the state at their program point when they occur
in type annotations, tactics, term macros or syntax antiquotations. Closures
retain their captured values, and field operands following lifted calls see
the callee's updates. Internal expressions use the state bindings of their
enclosing statement.

Each procedure runs on four distinct initial states. Independent expected
results check the return value and the entire post-state.
-/

set_option linter.unusedVariables false

open VeilTest.ActionExecution

veil module StateReadContexts

individual x : Nat
individual y : Nat
individual flag : Bool
individual pair : Nat × Nat

#gen_state

def inputs : List (State FieldConcreteType) := [
  { x := 0, y := 3, flag := false, pair := (2, 5) },
  { x := 7, y := 0, flag := true, pair := (17, 19) },
  { x := 42, y := 9, flag := false, pair := (31, 37) },
  { x := 0, y := 5, flag := true, pair := (47, 53) }]

macro "state_read_case " id:ident "{" body:doSeq "}" "expect " expected:term : command => do
  let exec := Lean.mkIdent (id.getId.appendAfter "_exec")
  `(section
    procedure $id { $body }
    def $exec (s : State FieldConcreteType) := __veil_exec_action% {} {} s $id
    #guard inputs.all fun s =>
      let (expectedValue, expectedState) := ($expected) s
      exactlyOneSuccess ($exec s) fun value state =>
        value == expectedValue && state == expectedState
    end)

procedure increment_x_and_toggle_flag { x := x + 1; flag := !flag; return x }

macro "current_x" : term => `($(Lean.mkIdent `x))
macro "twice_current_x" : term => `(current_x + current_x)

def finDomainSize {n : Nat} (_ : Fin n → Nat) : Nat := n

-- The projections are dotted identifiers whose root is a mutable field.
state_read_case swap_pair_and_read_projections {
  pair := (pair.snd, pair.fst)
  return pair.fst + pair.snd
}
expect (fun s => (s.pair.fst + s.pair.snd, { s with pair := (s.pair.snd, s.pair.fst) }))

-- The local statement mentions `x` only in its type. Observe that type's
-- bound through an inferred argument, so a stale read changes the result.
state_read_case read_state_in_local_type {
  x := x + 1
  let f : Fin (x + 1) → Nat := fun i => i.val
  return finDomainSize f
}
expect (fun s => (s.x + 2, { s with x := s.x + 1 }))

-- Two rounds of term-macro expansion must resolve the post-write field.
state_read_case read_state_through_nested_macros { x := x + 1; return twice_current_x }
expect (fun s => (2 * (s.x + 1), { s with x := s.x + 1 }))

state_read_case read_state_in_tactic { x := x + 1; let v : Nat := by exact x; return v }
expect (fun s => (s.x + 1, { s with x := s.x + 1 }))

-- An antiquotation executes code that reads a field while constructing syntax.
state_read_case read_state_in_antiquotation {
  x := x + 1
  let stx := Lean.Unhygienic.run `(term| $(Lean.Syntax.mkNatLit x))
  return stx.raw.isNatLit?.getD 99
}
expect (fun s => (s.x + 1, { s with x := s.x + 1 }))

-- A closure captures its creation-time value; the later plain read is fresh.
state_read_case capture_state_before_write {
  let readSnapshot := fun _ : Unit => x
  x := x + 1
  return readSnapshot () + x
}
expect (fun s => (2 * s.x + 1, { s with x := s.x + 1 }))

-- A field operand in the same expression as a lifted call sees its effects.
state_read_case read_state_after_lifted_call {
  let v := (← increment_x_and_toggle_flag) + x
  return v
}
expect (fun s => (2 * (s.x + 1), { s with x := s.x + 1, flag := !s.flag }))

-- The internal expression inherits the `if` statement's state opening.
-- Cover an untaken branch, a successful branch and a discarded execution.
procedure read_state_in_internal_branch {
  if flag then
    veil_do_internal_expr% (if x = 0 then assume False else pure ())
  return y
}
def internalBranchExec (s : State FieldConcreteType) :=
  __veil_exec_action% {} {} s read_state_in_internal_branch
#guard inputs.all fun s =>
  if s.flag && s.x == 0 then hasNoExecutions (internalBranchExec s)
  else exactlyOneSuccess (internalBranchExec s) fun value state => value == s.y && state == s

end StateReadContexts
