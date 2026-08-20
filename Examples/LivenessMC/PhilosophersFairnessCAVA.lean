import Veil

/-! # CAVA `BoolProgs` — "Dining Philosophers", with fairness.
    This test can have two failures:
    - Phil. 0 starves because P1 and P2 trade forks forever
    - Phil. 0 starves because of deadlock: All 3 pick up their left fork at the same time,
        none can put it down before eating

    Writing it this "CAVA BoolProgs" style surfaces the first
    error as a counter-example (since it finds it first).
-/

veil module BoolProgPhilosophers

individual free0 : Bool
individual free1 : Bool
individual free2 : Bool
individual one0 : Bool
individual one1 : Bool
individual one2 : Bool
individual eat0 : Bool
individual eat1 : Bool
individual eat2 : Bool

enum Taken = {
  init_T,
  pickup1_0_T,
  pickup2_0_T,
  putdown_0_T,
  pickup1_1_T,
  pickup2_1_T,
  putdown_1_T,
  pickup1_2_T,
  pickup2_2_T,
  putdown_2_T
}
individual action_taken : Taken

#gen_state

after_init {
  free0 := true
  free1 := true
  free2 := true
  one0 := false
  one1 := false
  one2 := false
  eat0 := false
  eat1 := false
  eat2 := false

  action_taken := init_T
}

ghost relation pickup1_0_e := eat0 = false ∧ free0 = true
ghost relation pickup2_0_e := one0 = true ∧ free1 = true
ghost relation putdown_0_e := eat0 = true

ghost relation pickup1_1_e := eat1 = false ∧ free1 = true
ghost relation pickup2_1_e := one1 = true ∧ free2 = true
ghost relation putdown_1_e := eat1 = true

ghost relation pickup1_2_e := eat2 = false ∧ free2 = true
ghost relation pickup2_2_e := one2 = true ∧ free0 = true
ghost relation putdown_2_e := eat2 = true

-- Philosopher 0 uses forks 0 and 1.
action pickup1_0 { require pickup1_0_e; one0 := true; free0 := false; action_taken := pickup1_0_T }
action pickup2_0 { require pickup2_0_e; one0 := false; free1 := false; eat0 := true; action_taken := pickup2_0_T }
action putdown_0 { require putdown_0_e; free0 := true; free1 := true; eat0 := false; action_taken := putdown_0_T }

-- Philosopher 1 uses forks 1 and 2.
action pickup1_1 { require pickup1_1_e; one1 := true; free1 := false; action_taken := pickup1_1_T }
action pickup2_1 { require pickup2_1_e; one1 := false; free2 := false; eat1 := true; action_taken := pickup2_1_T }
action putdown_1 { require putdown_1_e; free1 := true; free2 := true; eat1 := false; action_taken := putdown_1_T }

-- Philosopher 2 uses forks 2 and 0.
action pickup1_2 { require pickup1_2_e; one2 := true; free2 := false; action_taken := pickup1_2_T }
action pickup2_2 { require pickup2_2_e; one2 := false; free0 := false; eat2 := true; action_taken := pickup2_2_T }
action putdown_2 { require putdown_2_e; free2 := true; free0 := true; eat2 := false; action_taken := putdown_2_T }

-- Adjacent philosophers share a fork, so they can never eat simultaneously.
safety [mutex01] ¬(eat0 = true ∧ eat1 = true)
safety [mutex12] ¬(eat1 = true ∧ eat2 = true)
safety [mutex20] ¬(eat2 = true ∧ eat0 = true)

-- False without fairness: philosophers 1 and 2 can trade forks 1/2 forever, starving philosopher 0.
liveness [phil0EventuallyEats] □ ◇ ⌜ eat0 = true ⌝

-- (fairness assumption) → phil0EventuallyEats.
liveness [phil0EventuallyEatsFair]
  ((□ (◇ (¬ ⌜ eat0 = false ∧ one0 = false ⌝) ∨ ◇ ⌜ action_taken = pickup1_0_T ⌝))
   ∧ (□ (◇ (¬ ⌜ one0 = true ∧ eat0 = false ⌝) ∨ ◇ ⌜ action_taken = pickup2_0_T ⌝)))
  → □ ◇ ⌜ eat0 = true ⌝

#gen_spec

#model_check {}

#eval Veil.LivenessMC.checkResultToString "BoolProgPhilosophers" "□◇(eat0)"
  (Veil.LivenessMC.check (enumerableTransitionSystem Taken_IndT {})
    (phil0EventuallyEats (Theory Taken_IndT) (State (FieldConcreteType Taken_IndT))
      Taken_IndT (FieldConcreteType Taken_IndT))
    (by native_decide) (by native_decide))

#eval Veil.LivenessMC.checkResultToString "BoolProgPhilosophers" "(fairness for phil0) → □◇(eat0)"
  (Veil.LivenessMC.check (enumerableTransitionSystem Taken_IndT {})
    (phil0EventuallyEatsFair (Theory Taken_IndT) (State (FieldConcreteType Taken_IndT))
      Taken_IndT (FieldConcreteType Taken_IndT))
    (by native_decide) (by native_decide))

end BoolProgPhilosophers
