module

public import Veil.CSLib.Simulation

public section

/-!
Weak simulations using CSLib's `HasTau`, `STr`, and `LTS.saturate`.
An observation map classifies each native action label as either internal (τ)
or visible. Simulations use CSLib's existing `IsSimulation` predicate with a
saturated target, preserving visible events while allowing internal steps.
-/

namespace Veil.RelationalTransitionSystem

/-- Relabel a system by its observations. Several native labels may have the
same observation. CSLib's `mapLabel` pulls labels back in the opposite direction,
so it cannot directly express this many-to-one classification. -/
@[expose] def toObservedLTS (sys : RelationalTransitionSystem ρ σ l) (th : ρ)
    (observe : l → obs) : Cslib.LTS σ obs where
  Tr s event s' := ∃ label, observe label = event ∧ sys.tr th s label s'

/-- A native finite execution induces the corresponding observed execution. -/
theorem observed_mTr_of_mTr {sys : RelationalTransitionSystem ρ σ l} {th : ρ}
    (observe : l → obs) {s s' : σ} {labels : List l}
    (h : (sys.toLTS th).MTr s labels s') :
    (sys.toObservedLTS th observe).MTr s (labels.map observe) s' := by
  induction h with
  | refl => exact .refl
  | stepL htr _ ih => exact .stepL ⟨_, rfl, htr⟩ ih

variable {obs : Type} [Cslib.HasTau obs]

/-- Internal observed executions are real finite executions of the native system. -/
theorem canReach_of_observed_tauSTr {sys : RelationalTransitionSystem ρ σ l} {th : ρ}
    {observe : l → obs} {s s' : σ}
    (h : (sys.toObservedLTS th observe).τSTr s s') :
    (sys.toLTS th).CanReach s s' := by
  induction h with
  | refl => exact ⟨[], .refl⟩
  | tail _ htr ih =>
    obtain ⟨labels, hpath⟩ := ih
    obtain ⟨label, _, hstep⟩ := htr
    exact ⟨labels ++ [label], hpath.stepR _ hstep⟩

/-- Saturation adds edges representing real finite executions, including the
empty execution for τ. It introduces no new reachable native states. -/
theorem canReach_of_observed_sTr {sys : RelationalTransitionSystem ρ σ l} {th : ρ}
    {observe : l → obs} {s s' : σ} {event : obs}
    (h : (sys.toObservedLTS th observe).STr s event s') :
    (sys.toLTS th).CanReach s s' := by
  cases h with
  | refl => exact ⟨[], .refl⟩
  | tr hbefore hstep hafter =>
    obtain ⟨before, hb⟩ := canReach_of_observed_tauSTr hbefore
    obtain ⟨label, _, ht⟩ := hstep
    obtain ⟨after, ha⟩ := canReach_of_observed_tauSTr hafter
    exact ⟨(before ++ [label]) ++ after, (hb.stepR _ ht).comp _ ha⟩

/-- Hiding every action recovers exactly the previous unlabelled path closure. -/
theorem all_internal_sTr_iff_canReach (sys : RelationalTransitionSystem ρ σ l)
    (th : ρ) (s s' : σ) :
    (sys.toObservedLTS th (fun _ => (Cslib.HasTau.τ : obs))).STr
        s Cslib.HasTau.τ s' ↔ (sys.toLTS th).CanReach s s' := by
  constructor
  · exact canReach_of_observed_sTr
  · rintro ⟨labels, h⟩
    induction h with
    | refl => exact .refl
    | stepL htr _ ih =>
      exact .tr .refl ⟨_, rfl, htr⟩ ((Cslib.LTS.sTr_τSTr_iff _).mp ih)

variable {concrete : RelationalTransitionSystem ρc σc lc}
    {abstract : RelationalTransitionSystem ρa σa la}
    {thConcrete : ρc} {thAbstract : ρa} {rel : σc → σa → Prop}
    {observeConcrete : lc → obs} {observeAbstract : la → obs}

/-- A CSLib simulation into a saturated observed LTS transfers Veil reachability.
Initialization and background assumptions are supplied separately because CSLib's
simulation predicate concerns only transitions. -/
theorem reachable_of_weakSimulation
    (hass : concrete.assumptions thConcrete → abstract.assumptions thAbstract)
    (hinit : ∀ sc, concrete.assumptions thConcrete → concrete.init thConcrete sc →
      ∃ sa, abstract.init thAbstract sa ∧ rel sc sa)
    (hsim : concrete.assumptions thConcrete → Cslib.LTS.IsSimulation
      (concrete.toObservedLTS thConcrete observeConcrete)
      (abstract.toObservedLTS thAbstract observeAbstract).saturate rel)
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
    obtain ⟨sa', htr', hrel'⟩ :=
      hsim hc sc sa hrel (observeConcrete label) sc' ⟨label, rfl, htr⟩
    exact ⟨sa', reachable_of_canReach ha (canReach_of_observed_sTr htr'), hrel'⟩

/-- Transfer an abstract reachable-state invariant, including a generated
`<clause>.is_inv`, through CSLib's weak simulation encoding. -/
theorem invariant_of_weakSimulation
    (hass : concrete.assumptions thConcrete → abstract.assumptions thAbstract)
    (hinit : ∀ sc, concrete.assumptions thConcrete → concrete.init thConcrete sc →
      ∃ sa, abstract.init thAbstract sa ∧ rel sc sa)
    (hsim : concrete.assumptions thConcrete → Cslib.LTS.IsSimulation
      (concrete.toObservedLTS thConcrete observeConcrete)
      (abstract.toObservedLTS thAbstract observeAbstract).saturate rel)
    {pConcrete : σc → Prop} {pAbstract : σa → Prop}
    (hinv : ∀ sa, abstract.reachable thAbstract sa → pAbstract sa)
    (hrel : ∀ sc sa, rel sc sa → pAbstract sa → pConcrete sc)
    {sc : σc} (hr : concrete.reachable thConcrete sc) : pConcrete sc := by
  obtain ⟨sa, ha, hr'⟩ := reachable_of_weakSimulation hass hinit hsim hr
  exact hrel sc sa hr' (hinv sa ha)

end Veil.RelationalTransitionSystem
