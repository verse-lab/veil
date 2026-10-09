module

public import Veil.Core.Tools.ModelChecker.Concrete.Sequential
public import Veil.Core.Tools.ModelChecker.Concrete.MapReduce

/-! Reachable-state injectivity suffices even when an unreachable state shares
the initial state's fingerprint. Seen fingerprints must retain reachable
representatives without implying that every state with that fingerprint is reachable. -/

open Veil Veil.ModelChecker Veil.ModelChecker.Concrete

namespace ModelCheckReachableInjectivity

inductive State where
  | initial | successor | unreachable
  deriving DecidableEq

instance fingerprint : StateFingerprint State Bool where
  beq := BEq.beq
  rfl := BEq.rfl
  eq_of_beq := LawfulBEq.eq_of_beq
  hash_eq := LawfulHashable.hash_eq
  view
    | .successor => true
    | _ => false

def sys : EnumerableTransitionSystem Unit (List Unit) State (List State)
    Int Unit (Transitions Unit Int State) () where
  initStates := [.initial]
  tr _
    | .initial => ⟨[((), .successor)], []⟩
    | _ => ⟨[], []⟩

def params : SearchParameters Unit State where
  invariants := []
  earlyTerminationConditions := []

theorem reachable_ne_unreachable {s : State} (h : sys.reachable s) :
    s ≠ .unreachable := by
  induction h with
  | init s hs => simp [sys] at hs; subst s; decide
  | step u v _ hn _ =>
    rcases hn with ⟨label, hn⟩
    cases u <;> simp [sys, Transitions.mem_success_iff] at hn
    subst v; decide

theorem injective_on_reachable : Function.InjectiveOn fingerprint.view sys.reachable := by
  intro a ha b hb heq
  have ha' := reachable_ne_unreachable ha
  have hb' := reachable_ne_unreachable hb
  cases a <;> cases b <;> simp_all

example : ¬ Veil.Function.Injective fingerprint.view := by
  intro h
  have := h (a := .initial) (b := .unreachable) rfl
  contradiction

abbrev Stats := VectorForActionStatUpdate ActionStat Unit

def initial : SequentialSearchContext State Unit Bool Stats :=
  SequentialSearchContext.initial sys

example : SequentialSearchContextInvariants sys params .none initial :=
  SequentialSearchContextInvariants.initial sys params

-- The unreachable state has a seen fingerprint, but is still unreachable.
example : fingerprint.view State.unreachable ∈ initial.1.log := by
  exact (SequentialSearchContextInvariants.initial (asm := Stats) sys params).init_states_included
    .initial (by simp [sys])

example : ¬ sys.reachable .unreachable := fun h => reachable_ne_unreachable h rfl

example {sctx : SequentialSearchContext State Unit Bool Stats}
    (h_invs : SequentialSearchContextInvariants sys params .none sctx)
    (h_finished : sctx.1.finished = some .exploredAllReachableStates) :
    ∀ s, sys.reachable s → fingerprint.view s ∈ sctx.1.log :=
  SequentialSearchContext.bfs_completeness sys params h_invs h_finished injective_on_reachable

example {Shard : Type} [Membership Bool Shard]
    {mctx : MapReduceSearchContextMain State Unit Bool Stats Shard}
    (h_invs : MapReduceSearchContextMainInvariants sys params mctx)
    (h_finished : mctx.base.finished = some .exploredAllReachableStates) :
    ∀ s, sys.reachable s → fingerprint.view s ∈ mctx.globalSeen :=
  MapReduceSearchContextMainInvariants.bfs_completeness h_invs h_finished injective_on_reachable

end ModelCheckReachableInjectivity
