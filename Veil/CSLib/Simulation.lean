module

public import Veil.CSLib.TransitionSystem
public import Cslib.Foundations.Semantics.LTS.Simulation

public section

/-!
Transport Veil reachability and invariants using CSLib's `LTS.IsSimulation`.
No separate Veil simulation predicate is needed. Fixing the two theories before
stating a simulation also permits abstract state types that depend on the
concrete theory, as in the dissertation's ring-election refinement proof.
-/

namespace Veil.RelationalTransitionSystem

variable {concrete : RelationalTransitionSystem ρc σc lc}
    {abstract : RelationalTransitionSystem ρa σa la}
    {thConcrete : ρc} {thAbstract : ρa} {rel : σc → σa → Prop}

/-- Transfer reachability through a CSLib simulation into an abstract LTS.
`hsteps` connects that LTS to the abstract Veil system: each of its edges must
represent a finite abstract execution. This accommodates relabeling, stuttering,
and multiple abstract steps without changing CSLib's simulation definition. -/
theorem reachable_of_simulation_into {target : Cslib.LTS σa lc}
    (hass : concrete.assumptions thConcrete → abstract.assumptions thAbstract)
    (hinit : ∀ sc, concrete.assumptions thConcrete → concrete.init thConcrete sc →
      ∃ sa, abstract.init thAbstract sa ∧ rel sc sa)
    (hsim : concrete.assumptions thConcrete →
      Cslib.LTS.IsSimulation (concrete.toLTS thConcrete) target rel)
    (hsteps : ∀ sa label sa', target.Tr sa label sa' →
      (abstract.toLTS thAbstract).CanReach sa sa')
    {sc : σc} (hr : concrete.reachable thConcrete sc) :
    ∃ sa, abstract.reachable thAbstract sa ∧ rel sc sa := by
  have hc := concrete.reachable_assumptions _ _ hr
  induction hr with
  | init sc _ hi =>
    obtain ⟨sa, ha, hrel⟩ := hinit sc hc hi
    exact ⟨sa, .init sa (hass hc) ha, hrel⟩
  | step sc sc' _ hnext ih =>
    obtain ⟨sa, ha, hrel⟩ := ih
    obtain ⟨label, htr⟩ := hnext
    obtain ⟨sa', htr', hrel'⟩ := hsim hc sc sa hrel label sc' htr
    exact ⟨sa', reachable_of_canReach ha (hsteps sa label sa' htr'), hrel'⟩

/-- Transfer reachability using an ordinary CSLib simulation between two Veil
systems with the same labels. -/
theorem reachable_of_simulation {abstract : RelationalTransitionSystem ρa σa lc}
    (hass : concrete.assumptions thConcrete → abstract.assumptions thAbstract)
    (hinit : ∀ sc, concrete.assumptions thConcrete → concrete.init thConcrete sc →
      ∃ sa, abstract.init thAbstract sa ∧ rel sc sa)
    (hsim : concrete.assumptions thConcrete → Cslib.LTS.IsSimulation
      (concrete.toLTS thConcrete) (abstract.toLTS thAbstract) rel)
    {sc : σc} (hr : concrete.reachable thConcrete sc) :
    ∃ sa, abstract.reachable thAbstract sa ∧ rel sc sa :=
  reachable_of_simulation_into hass hinit hsim
    (fun _ label _ h => ⟨[label], .single _ h⟩) hr

/-- Transfer an abstract invariant using a CSLib simulation into a relabeled or
closed abstract LTS. The abstract proof can be a generated `<clause>.is_inv`
theorem, specialized to `thAbstract`. -/
theorem invariant_of_simulation_into {target : Cslib.LTS σa lc}
    (hass : concrete.assumptions thConcrete → abstract.assumptions thAbstract)
    (hinit : ∀ sc, concrete.assumptions thConcrete → concrete.init thConcrete sc →
      ∃ sa, abstract.init thAbstract sa ∧ rel sc sa)
    (hsim : concrete.assumptions thConcrete →
      Cslib.LTS.IsSimulation (concrete.toLTS thConcrete) target rel)
    (hsteps : ∀ sa label sa', target.Tr sa label sa' →
      (abstract.toLTS thAbstract).CanReach sa sa')
    {pConcrete : σc → Prop} {pAbstract : σa → Prop}
    (hinv : ∀ sa, abstract.reachable thAbstract sa → pAbstract sa)
    (hrel : ∀ sc sa, rel sc sa → pAbstract sa → pConcrete sc)
    {sc : σc} (hr : concrete.reachable thConcrete sc) : pConcrete sc := by
  obtain ⟨sa, ha, hrel'⟩ := reachable_of_simulation_into hass hinit hsim hsteps hr
  exact hrel sc sa hrel' (hinv sa ha)

/-- Transfer an abstract invariant using an ordinary CSLib simulation. -/
theorem invariant_of_simulation {abstract : RelationalTransitionSystem ρa σa lc}
    (hass : concrete.assumptions thConcrete → abstract.assumptions thAbstract)
    (hinit : ∀ sc, concrete.assumptions thConcrete → concrete.init thConcrete sc →
      ∃ sa, abstract.init thAbstract sa ∧ rel sc sa)
    (hsim : concrete.assumptions thConcrete → Cslib.LTS.IsSimulation
      (concrete.toLTS thConcrete) (abstract.toLTS thAbstract) rel)
    {pConcrete : σc → Prop} {pAbstract : σa → Prop}
    (hinv : ∀ sa, abstract.reachable thAbstract sa → pAbstract sa)
    (hrel : ∀ sc sa, rel sc sa → pAbstract sa → pConcrete sc)
    {sc : σc} (hr : concrete.reachable thConcrete sc) : pConcrete sc := by
  obtain ⟨sa, ha, hrel'⟩ := reachable_of_simulation hass hinit hsim hr
  exact hrel sc sa hrel' (hinv sa ha)

end Veil.RelationalTransitionSystem
