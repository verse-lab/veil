module

public import Veil
public import Veil.CSLib.Simulation

@[expose] public section

set_option veil.smt.trust false
set_option veil.solver "grind"

/-! An abstract DSL specification whose generated invariant is reused below. -/
veil module CSLibAbstractCounter

immutable individual lower : Nat
individual count : Nat
#gen_state
after_init { count := lower }
action tick { count := count + 1 }
safety [above_lower] lower ≤ count
#gen_spec
#gen_theorems

end CSLibAbstractCounter

namespace CSLibSimulationTest

open Veil Veil.RelationalTransitionSystem
open scoped CSLibAbstractCounter

noncomputable abbrev abstractCounter := CSLibAbstractCounter.relationalTransitionSystem
abbrev AbstractState := CSLibAbstractCounter.State CSLibAbstractCounter.FieldAbstractType

theorem abstract_init (th : CSLibAbstractCounter.Theory) (s : AbstractState) :
    abstractCounter.init th s ↔ (⟨th.lower⟩ : AbstractState) = s := by
  simp only [abstractCounter, CSLibAbstractCounter.relationalTransitionSystem,
    CSLibAbstractCounter.Init, nextSimp, substateSimp,
    CSLibAbstractCounter.State.Label.toCodomain]
  rfl

theorem abstract_tick (th : CSLibAbstractCounter.Theory) (s : AbstractState) :
    (abstractCounter.toLTS th).Tr s .tick ⟨s.count + 1⟩ := by
  simp only [toLTS, abstractCounter, CSLibAbstractCounter.relationalTransitionSystem,
    CSLibAbstractCounter.Next, CSLibAbstractCounter.NextAct, nextSimp,
    CSLibAbstractCounter.FieldAbstractType, CSLibAbstractCounter.State.Label.toCodomain]

inductive ConcreteLabel where
  | idle
  | burst

/-- The concrete counter starts at `n + 1` and takes either zero or two ticks. -/
def concreteCounter : RelationalTransitionSystem Nat Nat ConcreteLabel where
  assumptions n := 0 < n
  init n s := s = n + 1
  tr _ s label s' := match label with
    | .idle => s' = s
    | .burst => s' = s + 2

def abstractTheory (n : Nat) : CSLibAbstractCounter.Theory := ⟨n + 1⟩
def related (sc : Nat) (sa : AbstractState) : Prop := sa.count = sc

/-- An LTS whose edges are finite abstract executions. Labels are deliberately
different from the abstract counter's labels. There is no new simulation
definition: CSLib's `IsSimulation` applies directly to this CSLib LTS. -/
noncomputable def abstractPaths (n : Nat) : Cslib.LTS AbstractState ConcreteLabel where
  Tr sa _ sa' := (abstractCounter.toLTS (abstractTheory n)).CanReach sa sa'

theorem simulation (n : Nat) : Cslib.LTS.IsSimulation
    (concreteCounter.toLTS n) (abstractPaths n) related := by
  intro sc sa hrel label sc' htr
  cases label with
  | idle =>
    change sc' = sc at htr
    subst sc'
    exact ⟨sa, ⟨[], .refl⟩, hrel⟩
  | burst =>
    change sc' = sc + 2 at htr
    subst sc'
    refine ⟨⟨sa.count + 1 + 1⟩, ?_, ?_⟩
    · exact ⟨[.tick, .tick], .stepL (abstract_tick _ sa)
        (.single _ (abstract_tick _ ⟨sa.count + 1⟩))⟩
    · change sa.count + 1 + 1 = sc + 2
      change sa.count = sc at hrel
      rw [hrel]

theorem concrete_above_lower : concreteCounter.isInvariant (fun n s => n + 1 ≤ s) := by
  intro n sc hr
  apply invariant_of_simulation_into (abstract := abstractCounter)
    (thAbstract := abstractTheory n)
    (fun _ => by
      simp [abstractCounter, CSLibAbstractCounter.relationalTransitionSystem,
        CSLibAbstractCounter.Assumptions])
    (fun sc _ hi => ?_) (fun _ => simulation n)
    (fun _ _ _ h => h)
    (CSLibAbstractCounter.above_lower.is_inv (abstractTheory n))
    (fun sc sa hrel hinv => ?_) hr
  · refine ⟨⟨n + 1⟩, (abstract_init _ _).mpr rfl, ?_⟩
    exact hi.symm
  · change n + 1 ≤ sa.count at hinv
    exact hrel ▸ hinv

/-! A direct, label-preserving simulation with different theory and state types. -/

def source : RelationalTransitionSystem Nat Nat Unit where
  assumptions n := 0 < n
  init n s := s = n
  tr _ s _ s' := s' = s + 1

def target : RelationalTransitionSystem (Nat × Bool) (Nat × Unit) Unit where
  assumptions th := 0 < th.1 ∧ th.2 = true
  init th s := s.1 = th.1
  tr _ s _ s' := s'.1 = s.1 + 1

theorem direct_simulation (n : Nat) : Cslib.LTS.IsSimulation
    (source.toLTS n) (target.toLTS (n, true)) (fun sc sa => sc = sa.1) := by
  intro sc sa hrel label sc' htr
  refine ⟨(sc', ()), ?_, rfl⟩
  change sc' = sc + 1 at htr
  change sc' = sa.1 + 1
  rw [← hrel]
  exact htr

theorem direct_reachable (n s : Nat) (hr : source.reachable n s) :
    ∃ sa, target.reachable (n, true) sa ∧ s = sa.1 := by
  exact reachable_of_simulation (abstract := target) (thAbstract := (n, true))
    (rel := fun sc sa => sc = sa.1) (fun h => ⟨h, rfl⟩)
    (fun sc _ hi => ⟨(sc, ()), hi, rfl⟩) (fun _ => direct_simulation n) hr

-- The CSLib LTS deliberately contains no assumption check; the bridge must
-- retain Veil's assumptions even for a zero-length execution.
example : (source.toLTS 0).CanReach 0 0 := ⟨[], .refl⟩
example : ¬source.reachable 0 0 := by
  intro hr
  have := source.reachable_assumptions _ _ hr
  exact Nat.lt_irrefl 0 this

/-! The abstract state type can depend on the fixed concrete theory. -/

def boundedCounter : RelationalTransitionSystem Nat Nat Unit where
  assumptions _ := True
  init n s := s = n
  tr n s _ s' := s' = min (s + 1) n

def finiteCounter (n : Nat) : RelationalTransitionSystem Unit (Fin (n + 1)) Unit where
  assumptions _ := True
  init _ s := s.val = n
  tr _ s _ s' := s'.val = min (s.val + 1) n

theorem finite_simulation (n : Nat) : Cslib.LTS.IsSimulation
    (boundedCounter.toLTS n) ((finiteCounter n).toLTS ())
    (fun sc sa => sc = sa.val) := by
  intro sc sa hrel label sc' htr
  let sa' : Fin (n + 1) :=
    ⟨min (sa.val + 1) n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  refine ⟨sa', rfl, ?_⟩
  change sc' = min (sa.val + 1) n
  change sc' = min (sc + 1) n at htr
  simpa only [hrel] using htr

theorem bounded_invariant : boundedCounter.isInvariant (fun n s => s ≤ n) := by
  intro n sc hr
  exact invariant_of_simulation (abstract := finiteCounter n) (thAbstract := ())
    (rel := fun sc sa => sc = sa.val) (fun _ => trivial)
    (fun sc _ hi => ⟨⟨n, Nat.lt_succ_self n⟩, rfl, hi⟩)
    (fun _ => finite_simulation n)
    (pConcrete := fun s => s ≤ n)
    (pAbstract := fun sa => sa.val ≤ n)
    (fun sa _ => Nat.le_of_lt_succ sa.isLt)
    (fun _ _ hrel hinv => by simpa only [hrel] using hinv) hr

-- Verify that all example proofs, including the generated invariant used by
-- invariant transport, were checked without admitting a proof.
open Lean in
run_cmd do
  for name in #[``simulation, ``concrete_above_lower, ``direct_reachable,
      ``bounded_invariant] do
    if (← collectAxioms name).contains ``sorryAx then
      throwError "unexpected sorry in {name}"

end CSLibSimulationTest
