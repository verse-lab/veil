module



@[expose] public section

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
deriving Repr, BEq, DecidableEq, Inhabited

/-- The result of an execution whose return value carries no information, typically
used by the model checker. -/
abbrev ExecutionOutcome (ε σ : Type) := ExecutionResult ε σ Unit

/-- Successful outcome of an execution with no return value. This is tagged
`@[match_pattern]`, so it can be used in patterns just like a constructor. -/
@[match_pattern]
abbrev ExecutionOutcome.success {ε σ : Type} (state : σ) : ExecutionOutcome ε σ :=
  ExecutionResult.success () state

@[match_pattern]
abbrev ExecutionOutcome.assertionFailure {ε σ : Type} (error : ε) (state : σ) : ExecutionOutcome ε σ :=
  ExecutionResult.assertionFailure error state

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

/-- A transition whose execution raised an assertion: its label, the exception, and the state at
the point of failure (for trace construction). -/
structure FailedTransition (l ε σ : Type) where
  label : l
  error : ε
  state : σ
deriving Repr, Inhabited

/-- The transitions out of a state, as the model checker consumes them: the post-states of the
successful executions, each with its label, and the assertion failures. Divergence is not
recorded; no consumer looked at it. `(label, outcome) ∈ ts` is membership in the matching list,
so `EnumerableTransitionSystem.next` and `reachable` read as before. -/
structure Transitions (l ε σ : Type) where
  successes : List (l × σ)
  failures : List (FailedTransition l ε σ)
deriving Repr, Inhabited

namespace Transitions

variable {l ε σ : Type}

instance : Membership (l × ExecutionOutcome ε σ) (Transitions l ε σ) where
  mem ts
    | (label, .success s) => (label, s) ∈ ts.successes
    | (label, .assertionFailure e s) => ⟨label, e, s⟩ ∈ ts.failures
    | (_, .divergence) => False

/-! The three lemmas below are not `simp` lemmas on purpose: the search's proofs treat
`(label, outcome) ∈ sys.tr th st` as an opaque atom (as they did when `tr` returned a list), and a
`simp` call rewriting some occurrences but not others would hide that they are the same atom. -/

theorem mem_success_iff {ts : Transitions l ε σ} {label : l} {s : σ} :
    (label, ExecutionOutcome.success s) ∈ ts ↔ (label, s) ∈ ts.successes := Iff.rfl

theorem mem_assertionFailure_iff {ts : Transitions l ε σ} {label : l} {e : ε} {s : σ} :
    (label, ExecutionOutcome.assertionFailure e s) ∈ ts ↔ ⟨label, e, s⟩ ∈ ts.failures := Iff.rfl

theorem not_mem_divergence {ts : Transitions l ε σ} {label : l} :
    ¬ (label, (ExecutionResult.divergence : ExecutionOutcome ε σ)) ∈ ts := fun h => h

/-- Only to satisfy the `Std.Stream` requirement of `EnumerableTransitionSystem`: the transitions
as `(label, outcome)` pairs, successes first. -/
instance : Std.Stream (Transitions l ε σ) (l × ExecutionOutcome ε σ) where
  next? ts :=
    match ts.successes with
    | (label, s) :: rest => some ((label, .success s), { ts with successes := rest })
    | [] =>
      match ts.failures with
      | f :: rest => some ((f.label, .assertionFailure f.error f.state), { ts with failures := rest })
      | [] => none

end Transitions

end Veil
