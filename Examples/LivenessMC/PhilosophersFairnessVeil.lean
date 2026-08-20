import Veil
import LTLLib

/-! # Veil-Style — "Dining Philosophers", with fairness
    This test can have two failures:
    - Phil. 0 starves because P1 and P2 trade forks forever
    - Phil. 0 starves because of deadlock: All 3 pick up their left fork at the same time,
        none can put it down before eating

    This style surfaces the second error as a counter-example (since it finds it first).
    See "PhilosophersFairness" for an example surfacing the first counter-example.
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

-- False without fairness: Deadlock on all 3 philosophers holding a single fork.
liveness [phil0EventuallyEats] □ ◇ ⌜ eat 0 = true ⌝

-- (fairness assumption) → phil0EventuallyEats.
liveness [phil0EventuallyEatsFair]
  ((□ (◇ (¬ ⌜ eat 0 = false ∧ one 0 = false ⌝) ∨ ◇ ⌜ eat 0 = true ∨ one 0 = true ⌝))
   ∧ (□ (◇ (¬ ⌜ eat 0 = false ∧ one 0 = true ⌝) ∨ ◇ ⌜ eat 0 ⌝)))
  → □ ◇ ⌜ eat 0 = true ⌝

#gen_spec

#model_check {}

#eval Veil.LivenessMC.checkResultToString "Philosophers" "□◇(eat 0)"
  (Veil.LivenessMC.check (enumerableTransitionSystem {})
    (phil0EventuallyEats Theory (State FieldConcreteType) FieldConcreteType)
    (by native_decide) (by native_decide))

#eval Veil.LivenessMC.checkResultToString "Philosophers" "(fairness for phil0) → □◇(eat0)"
  (Veil.LivenessMC.check (enumerableTransitionSystem {})
    (phil0EventuallyEatsFair Theory (State FieldConcreteType) FieldConcreteType)
    (by native_decide) (by native_decide))

end Philosophers
