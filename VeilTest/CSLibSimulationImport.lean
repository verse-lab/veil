module

public import VeilTest.CSLibSimulation

public section

-- The adapter and transported proofs remain usable from an importing module.
example (n s : Nat) (hr : CSLibSimulationTest.concreteCounter.reachable n s) :
    n + 1 ≤ s := CSLibSimulationTest.concrete_above_lower n s hr

example (n s : Nat) (hr : CSLibSimulationTest.boundedCounter.reachable n s) :
    s ≤ n := CSLibSimulationTest.bounded_invariant n s hr

example (n s : Nat) :
    CSLibSimulationTest.source.reachable n s ↔ 0 < n ∧
      ∃ s₀, s₀ = n ∧ (CSLibSimulationTest.source.toLTS n).CanReach s₀ s :=
  Veil.RelationalTransitionSystem.reachable_iff_canReach _ _ _
