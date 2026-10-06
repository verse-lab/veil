module

public import Veil

/-! # Veil-Style — "Dining Philosophers", with fairness
    This test can have two failures:
    - Phil. 0 starves because P1 and P2 trade forks forever
    - Phil. 0 starves because of deadlock: All 3 pick up their left fork at the same time,
        none can put it down before eating

    `#liveness_check` reports the second error, the deadlock, which its search reaches first.
    See `PhilosophersFairnessCAVA.lean` for the same system in the CAVA `BoolProgs` style.
-/

veil module Philosophers

abbrev Philosopher := Fin 3

relation free: Philosopher -> Bool
relation one: Philosopher -> Bool
relation eat: Philosopher -> Bool

#gen_state

after_init {
  free P := true
  one P := false
  eat P := false
}

action pickup1 (p : Philosopher) {
  require eat p = false ∧ free p = true

  one p := true
  free p := false
}
action pickup2 (p : Philosopher) {
  require one p = true ∧ free ((p + 1) % 3) = true

  one p := false
  free ((p + 1) % 3) := false
  eat p := true
}
action putdown (p : Philosopher) {
  require eat p = true

  free p := true
  free ((p + 1) % 3) := true
  eat p := false
}

-- Adjacent philosophers share a fork, so they can never eat simultaneously.
safety [mutex01] ¬(eat 0 = true ∧ eat 1 = true)
safety [mutex12] ¬(eat 1 = true ∧ eat 2 = true)
safety [mutex20] ¬(eat 2 = true ∧ eat 0 = true)

-- `#liveness_check` checks the properties in declaration order and stops at the first
-- counterexample, so the property that holds comes first.

-- (fairness assumption) → phil0EventuallyEats.
liveness [phil0EventuallyEatsFair]
  ((□ (◇ (¬ ⌜ eat 0 = false ∧ one 0 = false ⌝) ∨ ◇ ⌜ eat 0 = true ∨ one 0 = true ⌝))
   ∧ (□ (◇ (¬ ⌜ eat 0 = false ∧ one 0 = true ⌝) ∨ ◇ ⌜ eat 0 ⌝)))
  → □ ◇ ⌜ eat 0 = true ⌝

-- False without fairness: Deadlock on all 3 philosophers holding a single fork.
liveness [phil0EventuallyEats] □ ◇ ⌜ eat 0 = true ⌝

#gen_spec

set_option veil.violationIsError false in
#liveness_check {}

end Philosophers
