module

public import Veil.Core.Tools.ModelChecker.TransitionSystem

/-!
# Invariants of relational transition systems

This file proves the facts about Veil's `RelationalTransitionSystem` that the certificates of
`#synthesize_invariants` apply: a safety certificate is an inductive invariant that implies the
property, and a refutation is a reachable state that violates it.

## Main definitions

* `Veil.RelationalTransitionSystem.Invariant`: a predicate that holds in every reachable state.

## Main statements

* `Veil.RelationalTransitionSystem.invariant_of_inductive`: a predicate that holds initially and
  is preserved by every transition is an invariant.
* `Veil.RelationalTransitionSystem.Invariant.mono`: a consequence of an invariant is one.
* `Veil.RelationalTransitionSystem.not_invariant_of_reachable`: a reachable state that violates a
  predicate refutes it.
-/

@[expose] public section

namespace Veil.RelationalTransitionSystem

variable {ρ σ l : Type} (sys : RelationalTransitionSystem ρ σ l)

/-- `p` holds in every reachable state, under every theory. -/
def Invariant (p : ρ → σ → Prop) : Prop := ∀ th s, sys.reachable th s → p th s

variable {sys} {p q : ρ → σ → Prop}

/-- A predicate that holds in every initial state and is preserved by every transition, under the
assumptions, holds in every reachable state. -/
theorem invariant_of_inductive (hinit : ∀ th s, sys.assumptions th → sys.init th s → p th s)
    (hstep : ∀ th s lbl s', sys.assumptions th → p th s → sys.tr th s lbl s' → p th s') :
    sys.Invariant p := by
  intro th s h
  induction h with
  | init s has hs => exact hinit th s has hs
  | step s s' hr hn ih =>
    obtain ⟨lbl, htr⟩ := hn
    exact hstep th s lbl s' (sys.reachable_assumptions th s hr) ih htr

/-- A consequence of an invariant is an invariant. -/
theorem Invariant.mono (h : sys.Invariant p) (hpq : ∀ th s, p th s → q th s) : sys.Invariant q :=
  fun th s hr ↦ hpq th s (h th s hr)

/-- A reachable state that violates `p` refutes it as an invariant. -/
theorem not_invariant_of_reachable {th : ρ} {s : σ} (hr : sys.reachable th s) (hs : ¬ p th s) :
    ¬ sys.Invariant p :=
  fun h ↦ hs (h th s hr)

end Veil.RelationalTransitionSystem
