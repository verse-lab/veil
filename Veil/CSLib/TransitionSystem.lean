module

public import Veil.Core.Tools.ModelChecker.TransitionSystem
public import Cslib.Foundations.Semantics.LTS.Basic

public section

/-!
Adapt Veil's relational transition systems to CSLib. The background theory is
fixed before constructing the LTS; assumptions and initial states remain in Veil.
This module is opt-in and is not imported by `Veil`.
-/

namespace Veil.RelationalTransitionSystem

/-- The CSLib LTS of a Veil system at a fixed background theory. This uses the
same successful-transition relation as Veil's reachability and invariant proofs. -/
@[expose] def toLTS (sys : RelationalTransitionSystem ρ σ l) (th : ρ) : Cslib.LTS σ l where
  Tr := sys.tr th

@[simp] theorem toLTS_tr (sys : RelationalTransitionSystem ρ σ l) (th : ρ)
    (s : σ) (label : l) (s' : σ) :
    (sys.toLTS th).Tr s label s' ↔ sys.tr th s label s' := Iff.rfl

/-- A CSLib finite execution preserves Veil reachability. -/
theorem reachable_of_mTr {sys : RelationalTransitionSystem ρ σ l} {th : ρ}
    {s s' : σ} {labels : List l} (hr : sys.reachable th s)
    (h : (sys.toLTS th).MTr s labels s') : sys.reachable th s' := by
  induction h with
  | refl => exact hr
  | stepL htr _ ih => exact ih (.step _ _ hr ⟨_, htr⟩)

/-- A CSLib reachability witness preserves Veil reachability. -/
theorem reachable_of_canReach {sys : RelationalTransitionSystem ρ σ l} {th : ρ}
    {s s' : σ} (hr : sys.reachable th s)
    (h : (sys.toLTS th).CanReach s s') : sys.reachable th s' := by
  obtain ⟨_, h⟩ := h
  exact reachable_of_mTr hr h

/-- Veil reachability is exactly CSLib reachability from an initial state, with
the background assumptions. CSLib's `LTS` itself has no initial-state predicate. -/
theorem reachable_iff_canReach (sys : RelationalTransitionSystem ρ σ l)
    (th : ρ) (s : σ) :
    sys.reachable th s ↔ sys.assumptions th ∧
      ∃ s₀, sys.init th s₀ ∧ (sys.toLTS th).CanReach s₀ s := by
  constructor
  · intro hr
    induction hr with
    | init s hass hinit =>
      exact ⟨hass, s, hinit, Cslib.LTS.CanReach.refl _ s⟩
    | step s s' _ hnext ih =>
      obtain ⟨hass, s₀, hinit, labels, hpath⟩ := ih
      obtain ⟨label, htr⟩ := hnext
      exact ⟨hass, s₀, hinit, labels ++ [label], hpath.stepR _ htr⟩
  · rintro ⟨hass, s₀, hinit, hpath⟩
    exact reachable_of_canReach (.init s₀ hass hinit) hpath

end Veil.RelationalTransitionSystem
