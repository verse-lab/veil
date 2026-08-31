import Veil

/-!
# Concrete execution tests for Veil's extensible `do` notation

These tests extract individual actions into the executable nondeterministic
semantics and run them from explicit theory and state values.  Unlike the
symbolic regressions in `ExtensibleDo.lean`, every assertion below observes a
return value, a concrete post-state, or an assertion failure.
-/

set_option linter.unusedVariables false

namespace VeilTest.ActionExecution

open Veil.Extract

/-- Check that an extracted action has one successful execution satisfying
`p`, with no discarded, failing, or divergent alternatives. -/
def exactlyOneSuccess (results : List (ExecutionResult ε σ α))
    (p : α → σ → Bool) : Bool :=
  match results with
  | [.success value state] => p value state
  | _ => false

/-- Check every extracted alternative and its expected cardinality without
depending on the extractor's enumeration order. -/
def exactlyNSuccesses (n : Nat) (results : List (ExecutionResult ε σ α))
    (p : α → σ → Bool) : Bool :=
  results.length == n && results.all fun
    | .success value state => p value state
    | _ => false

def hasSuccess (results : List (ExecutionResult ε σ α))
    (p : α → σ → Bool) : Bool :=
  results.any fun
    | .success value state => p value state
    | _ => false

def hasAssertionFailure (results : List (ExecutionResult ε σ α))
    (p : ε → σ → Bool) : Bool :=
  results.any fun
    | .assertionFailure error state => p error state
    | _ => false

def hasNoExecutions (results : List (ExecutionResult ε σ α)) : Bool :=
  results.isEmpty

end VeilTest.ActionExecution

veil module ActionExecutionSmoke

individual x : Nat
individual y : Nat

#gen_state

procedure add_and_return (delta : Nat) {
  x := x + delta
  return x
}

def initial : State FieldConcreteType := { x := 1, y := 2 }

def result := __veil_exec_action% {} {} initial (add_and_return 4)

#guard result == [.success 5 { x := 5, y := 2 }]

end ActionExecutionSmoke
