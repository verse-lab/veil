import Veil.Core.Tools.ModelChecker.Data
namespace Veil

class TransitionSystem (ρ : Type) (σ : Type) (l : outParam Type) where

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
class RelationalTransitionSystem (ρ : Type) (σ : Type) (l : outParam Type) extends TransitionSystem ρ σ l where
  /-- The set of acceptable background theories -/
  assumptions : ρ → Prop
  /-- The set of initial states, indexed by background theory -/
  init : ρ → σ → Prop
  /-- The transition relation -/
  tr : ρ → σ → l → σ → Prop

attribute [grind] RelationalTransitionSystem.assumptions RelationalTransitionSystem.init RelationalTransitionSystem.tr

class LawfulRelationalTransitionSystem (ρ : Type) (σ : Type) (l : outParam Type) extends RelationalTransitionSystem ρ σ l where
  /-- The initial states satisfy the assumptions -/
  initSatisfiesAssumptions : ∀ (th : ρ) (s : σ), init th s → assumptions th

namespace RelationalTransitionSystem

/-- A version of the transition relation that "hides" which particular
transition was taken. -/
@[grind]
def next [RelationalTransitionSystem ρ σ l] (th : ρ) (s s' : σ) : Prop :=
  ∃ label, tr th s label s'

/-- Reachability relation, indexed by background theory -/
@[grind cases, grind intro]
inductive reachable [sys : RelationalTransitionSystem ρ σ l] (th : ρ) : σ → Prop where
  | init : ∀ (s : σ), sys.assumptions th → sys.init th s → RelationalTransitionSystem.reachable th s
  | step : ∀ (s s' : σ), RelationalTransitionSystem.reachable th s → sys.next th s s' → RelationalTransitionSystem.reachable th s'

/-- Assumptions hold in all reachable states. -/
@[grind .]
theorem reachable_assumptions [sys : RelationalTransitionSystem ρ σ l] (th : ρ) (s : σ) (h : reachable th s) : sys.assumptions th := by
  induction h with
  | init s has hinit => assumption
  | step s s' h2 hn ih => assumption

/-- Reachability is preserved under inclusion of transition systems. -/
@[grind .]
theorem reachable_inclusion [sys : RelationalTransitionSystem ρ σ l] [sys' : RelationalTransitionSystem ρ σ l]
  (hass_implies : ∀ (r : ρ), sys.assumptions r → sys'.assumptions r)
  (hinit_implies : ∀ (r : ρ) (st : σ), sys.init r st → sys'.init r st)
  (hnext_implies : ∀ (r : ρ) (st st' : σ), sys.next r st st' → sys'.next r st st') :
  ∀ (r : ρ) (st : σ), reachable (sys := sys) r st → reachable (sys := sys') r st := by
  intro r st h
  induction h with
  | init s has hinit => apply reachable.init _ (hass_implies r has) (hinit_implies r s hinit)
  | step s s' h2 hn ih => apply reachable.step ; apply ih ; apply hnext_implies ; assumption

end RelationalTransitionSystem

class ExecutableTransitionSystem
  (ρ : Type) (ρSet : outParam Type) [Std.Stream ρSet ρ]
  (σ : Type) (σSet : outParam Type) [Std.Stream σSet σ]
  (l : outParam Type)
  (nextSet : Type) [Std.Stream nextSet (l × σ)]
  extends TransitionSystem ρ σ l where
  /-- The (enumerable) set of background theories -/
  theories : ρSet
  /-- The (enumerable) set of initial states -/
  initStates : ρ → σSet
  /-- The (enumerable) set of transition labels and post-states -/
  tr : ρ → σ → nextSet
  /- The (enumerable) set of next states, for a specific transition label.
  This is used to simulate specific traces. -/
  -- next : ρ → σ → l → σSet

attribute [grind] ExecutableTransitionSystem.theories ExecutableTransitionSystem.initStates ExecutableTransitionSystem.tr

namespace ExecutableTransitionSystem

@[grind]
def next
  [Std.Stream ρSet ρ] [Std.Stream σSet σ] [Std.Stream nextSet (l × σ)]
  [Membership (l × σ) nextSet]
  [sys : ExecutableTransitionSystem ρ ρSet σ σSet l nextSet] (th : ρ) (s s' : σ) : Prop :=
  ∃ label, (label, s') ∈ sys.tr th s

@[grind]
def toRelational
  [Std.Stream ρSet ρ] [Std.Stream σSet σ] [Std.Stream nextSet (l × σ)]
  [Membership ρ ρSet] [Membership σ σSet] [Membership (l × σ) nextSet]
  (sys : ExecutableTransitionSystem ρ ρSet σ σSet l nextSet) :
  RelationalTransitionSystem ρ σ l
where
  assumptions := fun th => th ∈ sys.theories
  init := fun th st => st ∈ sys.initStates th
  tr := fun th st label st' => (label, st') ∈ sys.tr th st


/-- Reachability relation, indexed by background theory. -/
@[grind]
inductive reachable
  [Std.Stream ρSet ρ] [Std.Stream σSet σ] [Std.Stream nextSet (l × σ)]
  [Membership ρ ρSet] [Membership σ σSet] [Membership (l × σ) nextSet]
  [sys : ExecutableTransitionSystem ρ ρSet σ σSet l nextSet]
  (th : ρ) : σ → Prop
where
  | init : ∀ (s : σ), th ∈ sys.theories → s ∈ sys.initStates th → reachable th s
  | step : ∀ (s s' : σ), reachable th s → sys.next th s s' → reachable th s'

theorem reachable_equiv_relational
  [Std.Stream ρSet ρ] [Std.Stream σSet σ] [Std.Stream nextSet (l × σ)]
  [Membership ρ ρSet] [Membership σ σSet] [Membership (l × σ) nextSet]
  (sys : ExecutableTransitionSystem ρ ρSet σ σSet l nextSet)
  :
  sys.reachable th s ↔ (sys.toRelational.reachable th s) := by
  constructor <;> (intro hreach ; induction hreach with | _ => grind)

end ExecutableTransitionSystem

end Veil
