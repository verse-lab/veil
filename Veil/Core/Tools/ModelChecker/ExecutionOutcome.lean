/-!
# Execution Results and Outcomes

This file defines the `ExecutionResult` type which represents the possible
results of executing an action: success (carrying the action's return value
and post-state), assertion failure, or divergence.

Unlike `Option σ`, this preserves information about assertion failures that
can be used as counter-examples by the model checker.
-/

namespace Veil

/-- Possible results when executing an action. Unlike `Option σ`, this
preserves information about assertion failures (exceptions) that can be used
as counter-examples by the model checker. -/
inductive ExecutionResult (ε σ α : Type) where
  /-- The action executed successfully, returning `returnValue` and producing
  a post-state. -/
  | success (returnValue : α) (state : σ)
  /-- The action threw an assertion failure exception. We record both the
  exception ID and the state at the point of failure (for trace construction). -/
  | assertionFailure (error : ε) (state : σ)
  /-- The action diverged (did not terminate). -/
  | divergence
deriving Repr, BEq, Inhabited

/-- The result of an execution whose return value carries no information, typically
used by the model checker. -/
abbrev ExecutionOutcome (ε σ : Type) := ExecutionResult ε σ Unit

/-- Successful outcome of an execution with no return value. This is tagged
`@[match_pattern]`, so it can be used in patterns just like a constructor. -/
@[match_pattern]
abbrev ExecutionOutcome.success {ε σ : Type} (state : σ) : ExecutionOutcome ε σ :=
  ExecutionResult.success () state

namespace ExecutionResult

/-- Convert an execution result to an optional post-state, discarding return
values, assertion failures and divergence. This is the behavior expected for
normal transition exploration. -/
@[inline]
def toPostState : ExecutionResult ε σ α → Option σ
  | .success _ st => .some st
  | .assertionFailure _ _ => .none
  | .divergence => .none

/-- Check if the result is a successful transition. -/
@[inline]
def isSuccess : ExecutionResult ε σ α → Bool
  | .success _ _ => true
  | _ => false

/-- Check if the result is an assertion failure. -/
@[inline]
def isAssertionFailure : ExecutionResult ε σ α → Bool
  | .assertionFailure _ _ => true
  | _ => false

/-- Check if the result is divergence. -/
@[inline]
def isDivergence : ExecutionResult ε σ α → Bool
  | .divergence => true
  | _ => false

/-- Extract the state from a successful result. -/
@[inline]
def getSuccessState? : ExecutionResult ε σ α → Option σ
  | .success _ st => some st
  | _ => none

/-- Extract the error and state from an assertion failure. -/
@[inline]
def getAssertionFailure? : ExecutionResult ε σ α → Option (ε × σ)
  | .assertionFailure e st => some (e, st)
  | _ => none

/-- Extract just the exception ID from an assertion failure. -/
@[inline]
def exceptionId? : ExecutionResult ε σ α → Option ε
  | .assertionFailure e _ => some e
  | _ => none

end ExecutionResult

end Veil
