/-!
# Execution Outcomes

This file defines the `ExecutionOutcome` type which represents the possible
outcomes when executing an action: success, assertion failure, or divergence.

Unlike `Option σ`, this preserves information about assertion failures that
can be used as counter-examples by the model checker.
-/

namespace Veil

/-- Possible outcomes when executing an action. Unlike `Option σ`, this
preserves information about assertion failures (exceptions) that can be used
as counter-examples by the model checker. -/
inductive ExecutionOutcome (ε σ : Type) where
  /-- The action executed successfully and produced a post-state. -/
  | success (state : σ)
  /-- The action threw an assertion failure exception. We record both the
  exception ID and the state at the point of failure (for trace construction). -/
  | assertionFailure (error : ε) (state : σ)
  /-- The action diverged (did not terminate). -/
  | divergence
deriving Repr, BEq, DecidableEq, Inhabited

namespace ExecutionOutcome

/-- Convert an execution outcome to an optional post-state, discarding assertion
failures and divergence. This is the behavior expected for normal transition exploration. -/
@[inline]
def toPostState : ExecutionOutcome ε σ → Option σ
  | .success st => .some st
  | .assertionFailure _ _ => .none
  | .divergence => .none

/-- Extract just the exception ID from an assertion failure. -/
@[inline]
def exceptionId? : ExecutionOutcome ε σ → Option ε
  | .assertionFailure e _ => some e
  | _ => none

end ExecutionOutcome

end Veil
