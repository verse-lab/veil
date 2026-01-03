import Veil.Core.Tools.ModelChecker.ExecutionOutcome

namespace Veil

structure TransitionSystem (ρ : Type) (σ : Type) (l : outParam Type) where

/-- A relational transition system is parametrised by:
  - `ρ` - the type of the background theory (immutable state) it operates in
  - `σ` - the type of the state it operates on
  - `l` - the type of the transition labels (including the names of the
  transitions and the parameters they take)
  - `assumptions` - the set of acceptable background theories
  - `init` - the set of initial states, indexed by background theory they
  operate in
  - `tr` - the transition relation

A relational transition system might or might be executable, depending on
whether `assumptions`, `init`, and `tr` are decidable.
-/
@[grind]
structure RelationalTransitionSystem (ρ : Type) (σ : Type) (l : outParam Type) extends TransitionSystem ρ σ l where
  /-- The set of acceptable background theories -/
  assumptions : ρ → Prop
  /-- The set of initial states, indexed by background theory -/
  init : ρ → σ → Prop
  /-- The transition relation -/
  tr : ρ → σ → l → σ → Prop

attribute [grind] RelationalTransitionSystem.assumptions RelationalTransitionSystem.init RelationalTransitionSystem.tr

structure LawfulRelationalTransitionSystem (ρ : Type) (σ : Type) (l : outParam Type) extends RelationalTransitionSystem ρ σ l where
  /-- The initial states satisfy the assumptions -/
  initSatisfiesAssumptions : ∀ (th : ρ) (s : σ), init th s → assumptions th

namespace RelationalTransitionSystem

/-- A version of the transition relation that "hides" which particular
transition was taken. -/
@[grind]
def next (sys : RelationalTransitionSystem ρ σ l) (th : ρ) (s s' : σ) : Prop :=
  ∃ label, sys.tr th s label s'

/-- Reachability relation, indexed by background theory -/
@[grind cases, grind intro]
inductive reachable (sys : RelationalTransitionSystem ρ σ l) (th : ρ) : σ → Prop where
  | init : ∀ (s : σ), sys.assumptions th → sys.init th s → sys.reachable th s
  | step : ∀ (s s' : σ), sys.reachable th s → sys.next th s s' → sys.reachable th s'

/-- Assumptions hold in all reachable states. -/
@[grind .]
theorem reachable_assumptions (sys : RelationalTransitionSystem ρ σ l) (th : ρ) (s : σ) (h : reachable sys th s) : sys.assumptions th := by
  induction h with
  | init s has hinit => assumption
  | step s s' h2 hn ih => assumption

/-- Reachability is preserved under inclusion of transition systems. -/
@[grind .]
theorem reachable_inclusion (sys : RelationalTransitionSystem ρ σ l) (sys' : RelationalTransitionSystem ρ σ l)
  (hass_implies : ∀ (r : ρ), sys.assumptions r → sys'.assumptions r)
  (hinit_implies : ∀ (r : ρ) (st : σ), sys.init r st → sys'.init r st)
  (hnext_implies : ∀ (r : ρ) (st st' : σ), sys.next r st st' → sys'.next r st st') :
  ∀ (r : ρ) (st : σ), sys.reachable r st → sys'.reachable r st := by
  intro r st h
  induction h with
  | init s has hinit => apply reachable.init _ (hass_implies r has) (hinit_implies r s hinit)
  | step s s' h2 hn ih => apply reachable.step ; apply ih ; apply hnext_implies ; assumption

end RelationalTransitionSystem

/-- An enumerable transition system that tracks execution outcomes including
assertion failures. The `tr` function returns a set of labeled outcomes,
where each outcome can be a successful transition, an assertion failure,
or divergence.

Parameters:
- `ρ` - the type of the background theory (immutable state)
- `σ` - the type of the mutable state
- `ε` - the type of exceptions/assertion failure identifiers
- `l` - the type of transition labels
- `th` - the specific background theory this system operates under -/
structure EnumerableTransitionSystem
  (ρ : Type) (ρSet : outParam Type) [Std.Stream ρSet ρ]
  (σ : Type) (σSet : outParam Type) [Std.Stream σSet σ]
  (ε : Type)
  (l : outParam Type)
  (outcomeSet : Type) [Std.Stream outcomeSet (l × ExecutionOutcome ε σ)]
  (th : ρ)
  extends TransitionSystem ρ σ l where
  /-- The (enumerable) set of initial states -/
  initStates : σSet
  /-- The (enumerable) set of transition labels and execution outcomes.
  Each outcome may be a successful post-state, an assertion failure, or divergence. -/
  tr : ρ → σ → outcomeSet

attribute [grind] EnumerableTransitionSystem.initStates EnumerableTransitionSystem.tr

namespace EnumerableTransitionSystem

/-- Extract only successful transitions (ignoring assertion failures and divergence). -/
@[grind]
def next
  [Std.Stream ρSet ρ] [Std.Stream σSet σ] [Std.Stream outcomeSet (l × ExecutionOutcome ε σ)]
  [Membership (l × ExecutionOutcome ε σ) outcomeSet]
  (sys : EnumerableTransitionSystem ρ ρSet σ σSet ε l outcomeSet th) (s s' : σ) : Prop :=
  ∃ label, (label, ExecutionOutcome.success s') ∈ sys.tr th s

@[grind]
def toRelational
  [Std.Stream ρSet ρ] [Std.Stream σSet σ] [Std.Stream outcomeSet (l × ExecutionOutcome ε σ)]
  [Membership ρ ρSet] [Membership σ σSet] [Membership (l × ExecutionOutcome ε σ) outcomeSet]
  (sys : EnumerableTransitionSystem ρ ρSet σ σSet ε l outcomeSet th) :
  RelationalTransitionSystem ρ σ l
where
  assumptions := fun th' => th' = th
  init := fun _ st => st ∈ sys.initStates
  tr := fun th st label st' => (label, ExecutionOutcome.success st') ∈ sys.tr th st


/-- Reachability relation, indexed by background theory.
Only considers successful transitions (assertion failures don't lead to new reachable states). -/
@[grind]
inductive reachable
  [Std.Stream ρSet ρ] [Std.Stream σSet σ] [Std.Stream outcomeSet (l × ExecutionOutcome ε σ)]
  [Membership ρ ρSet] [Membership σ σSet] [Membership (l × ExecutionOutcome ε σ) outcomeSet]
  (sys : EnumerableTransitionSystem ρ ρSet σ σSet ε l outcomeSet th)
  : σ → Prop
where
  | init : ∀ (s : σ), s ∈ sys.initStates → sys.reachable s
  | step : ∀ (s s' : σ), sys.reachable s → sys.next s s' → sys.reachable s'

theorem reachable_equiv_relational
  [Std.Stream ρSet ρ] [Std.Stream σSet σ] [Std.Stream outcomeSet (l × ExecutionOutcome ε σ)]
  [Membership ρ ρSet] [Membership σ σSet] [Membership (l × ExecutionOutcome ε σ) outcomeSet]
  (sys : EnumerableTransitionSystem ρ ρSet σ σSet ε l outcomeSet th)
  :
  sys.reachable s ↔ (sys.toRelational.reachable th s) := by
  constructor <;> (intro hreach ; induction hreach with | _ => grind)

end EnumerableTransitionSystem

end Veil
