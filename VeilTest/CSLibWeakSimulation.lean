module

public import Veil.CSLib.WeakSimulation

public section

namespace CSLibWeakSimulationTest

open Veil Veil.RelationalTransitionSystem

inductive Event where
  | τ | a | b
  deriving DecidableEq

instance : Cslib.HasTau Event := ⟨.τ⟩

inductive Phase where
  | start | middle | done

inductive Location where
  | entry | ready | afterA | afterCleanup | done

inductive ConcreteLabel where
  | idle | first | second

inductive AbstractLabel where
  | prepare | first | cleanup | second

def observeConcrete : ConcreteLabel → Event
  | .idle => .τ
  | .first => .a
  | .second => .b

-- Two different native labels are hidden by the same observation map.
def observeAbstract : AbstractLabel → Event
  | .prepare | .cleanup => .τ
  | .first => .a
  | .second => .b

def concrete : RelationalTransitionSystem Unit Phase ConcreteLabel where
  assumptions _ := True
  init _ s := s = .start
  tr _ s label s' := match label with
    | .idle => s' = s
    | .first => s = .start ∧ s' = .middle
    | .second => s = .middle ∧ s' = .done

def abstract : RelationalTransitionSystem Unit Location AbstractLabel where
  assumptions _ := True
  init _ s := s = .entry
  tr _ s label s' := match label with
    | .prepare => s = .entry ∧ s' = .ready
    | .first => s = .ready ∧ s' = .afterA
    | .cleanup => s = .afterA ∧ s' = .afterCleanup
    | .second => s = .afterCleanup ∧ s' = .done

def representative : Phase → Location
  | .start => .entry
  | .middle => .afterCleanup
  | .done => .done

def related (sc : Phase) (sa : Location) : Prop := sa = representative sc

abbrev source := concrete.toObservedLTS () observeConcrete
abbrev target := abstract.toObservedLTS () observeAbstract

/-- A visible step matches τ; a; τ, while idle matches the empty execution. -/
theorem simulation : Cslib.LTS.IsSimulation source target.saturate related := by
  intro sc sa hrel event sc' htr
  change sa = representative sc at hrel
  subst sa
  obtain ⟨label, rfl, htr⟩ := htr
  cases label with
  | idle =>
    change sc' = sc at htr
    subst sc'
    exact ⟨representative sc, .refl, rfl⟩
  | first =>
    obtain ⟨rfl, rfl⟩ := htr
    refine ⟨.afterCleanup, ?_, rfl⟩
    exact .tr (.single ⟨.prepare, rfl, rfl, rfl⟩)
      ⟨.first, rfl, rfl, rfl⟩ (.single ⟨.cleanup, rfl, rfl, rfl⟩)
  | second =>
    obtain ⟨rfl, rfl⟩ := htr
    exact ⟨.done, .single ⟨.second, rfl, rfl, rfl⟩, rfl⟩

-- CSLib's own theorem extends this to a simulation of both saturated systems.
theorem saturated_simulation :
    Cslib.LTS.IsSimulation source.saturate target.saturate related :=
  simulation.isSimulation_saturate_left

theorem reachable (sc : Phase) (hr : concrete.reachable () sc) :
    ∃ sa, abstract.reachable () sa ∧ related sc sa := by
  exact reachable_of_weakSimulation (fun _ => trivial)
    (fun _ _ hi => by cases hi; exact ⟨.entry, rfl, rfl⟩)
    (fun _ => simulation) hr

-- Hiding every action recovers arbitrary finite paths, including this path
-- containing two visible events under the original observation policy.
theorem hidden_path :
    (abstract.toObservedLTS () (fun _ => Event.τ)).STr .entry .τ .done := by
  apply (all_internal_sTr_iff_canReach abstract () .entry .done).mpr
  exact ⟨[.prepare, .first, .cleanup, .second],
    .stepL ⟨rfl, rfl⟩ (.stepL ⟨rfl, rfl⟩
      (.stepL ⟨rfl, rfl⟩ (.single _ ⟨rfl, rfl⟩)))⟩

/-! Negative checks: saturation must preserve the chosen visible events. -/

def visibleOnly : RelationalTransitionSystem Unit Nat Event where
  assumptions _ := True
  init _ s := s = 0
  tr _ s event s' := event = .a ∧ s' = s + 1

abbrev observedVisibleOnly := visibleOnly.toObservedLTS () id

private theorem tau_eq {s s' : Nat} (h : observedVisibleOnly.τSTr s s') : s = s' := by
  induction h with
  | refl => rfl
  | tail _ ht _ =>
    obtain ⟨label, hlabel, hl, _⟩ := ht
    cases hl
    cases hlabel

private theorem visible_steps {s s' : Nat} {event : Event}
    (h : observedVisibleOnly.STr s event s') :
    (event = .τ ∧ s' = s) ∨ (event = .a ∧ s' = s + 1) := by
  cases h with
  | refl => exact .inl ⟨rfl, rfl⟩
  | tr hb ht ha =>
    obtain rfl := tau_eq hb
    obtain rfl := tau_eq ha
    obtain ⟨label, rfl, rfl, hs⟩ := ht
    exact .inr ⟨rfl, hs⟩

theorem visible_cannot_stutter : ¬observedVisibleOnly.STr 0 .a 0 := by
  intro h
  rcases visible_steps h with ⟨he, hs⟩ | ⟨he, hs⟩
  · cases he
  · cases hs

theorem visible_cannot_change_label : ¬observedVisibleOnly.STr 0 .b 1 := by
  intro h
  rcases visible_steps h with ⟨he, _⟩ | ⟨he, _⟩ <;> cases he

theorem visible_cannot_absorb_two_steps : ¬observedVisibleOnly.STr 0 .a 2 := by
  intro h
  rcases visible_steps h with ⟨he, hs⟩ | ⟨he, hs⟩
  · cases he
  · cases hs

theorem visible_cannot_be_hidden : ¬observedVisibleOnly.STr 0 .τ 1 := by
  intro h
  rcases visible_steps h with ⟨he, hs⟩ | ⟨he, hs⟩
  · cases hs
  · cases he

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``simulation, ``saturated_simulation, ``reachable, ``hidden_path,
      ``visible_cannot_stutter, ``visible_cannot_change_label,
      ``visible_cannot_absorb_two_steps, ``visible_cannot_be_hidden] do
    for ax in ← collectAxioms name do
      unless allowed.contains ax do
        throwError "unexpected axiom {ax} in {name}"

end CSLibWeakSimulationTest
