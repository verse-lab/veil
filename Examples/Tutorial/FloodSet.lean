module

public import Veil

veil module FloodSet

/-! ## Parameters and theory -/

type node
type value
instantiate val_ord : TotalOrder value

immutable individual f : Nat

/-! ## State -/

individual round : Nat                              -- current round number (0 to f+1)
function initialValue : node → value                -- initial proposal for each node
relation W (n : node) (v : value) : Bool            -- W set per node
relation decision (n : node) (v : value) : Bool     -- decision value per node, initially ∅
function crashed (n : node) : Bool                  -- has this node crashed?
function crashedInRound (n : node) : Nat            -- which round did it crash in?
individual numCrashed : Nat                         -- total number of crashes so far

/-! ## Ghost definitions -/

ghost relation alive (n : node) := ¬crashed n
ghost relation crashedInAPreviousRound (n : node) := (crashed n ∧ crashedInRound n < round)

/-! ## Initial state -/

after_init {
  initialValue := *
  round := 0
  W N V := (V == initialValue N)
  decision N V := false
  crashed N := false
  crashedInRound N := 0
  numCrashed := 0
}

/-! ## Transitions -/

action crash (n : node) {
  require numCrashed < f
  require alive n
  crashed n := true
  crashedInRound n := round
  numCrashed := numCrashed + 1
}

action advanceRound {
  require round < f + 1
  let delivery : (node → node → Bool) :|
    (∀ (sender : node),
      (crashedInAPreviousRound sender → (∀ (receiver : node), ¬ delivery sender receiver)) ∧
      (alive sender → (∀ (receiver : node), delivery sender receiver)))
  W N V := decide $ W N V ∨ (alive N ∧ ∃ sender, delivery sender N ∧ W sender V)
  round := round + 1
}

procedure deterministicDecision (n : node) {
  let v ← pick value
  assume W n v ∧ (∀ v', W n v' → val_ord.le v v')
  return v
}

action nodeDecide (n : node) {
  require round = f + 1
  require alive n
  require ¬(∃ v, decision n v)
  let v ← deterministicDecision n
  decision n v := true
}

/-! ## Safety properties -/

safety [agreement]
  ∀ n₁ n₂ v₁ v₂, decision n₁ v₁ ∧ decision n₂ v₂ → v₁ = v₂

safety [strong_validity]
  ∀ n v, decision n v → ((∃ m, initialValue m = v))

/-! ## Inductive invariant -/

invariant [every_seen_is_someones_initial]
  ∀ n v, W n v → (∃ m, initialValue m = v)

-- invariant [decision_minimum_seen]
--   ∀ n v, decision n v → (∀ v', W n v' → val_ord.le v v')

-- invariant [crash_limit]
--   numCrashed ≤ f

-- invariant [no_crashes_def]
--   numCrashed = 0 ↔ ∀ n, ¬ crashed n

-- invariant [decision_crashed_after_end]
--   ∀ n v, (decision n v ∧ crashed n) → crashedInRound n ≥ f + 1

-- invariant [decision_only_at_end]
--   ∀ n v, decision n v → round ≥ f + 1

-- invariant [crashed_in_round_le_round]
--   ∀ n, crashedInRound n ≤ round

-- invariant [initial_value_in_W]
--   ∀ n, W n (initialValue n)

-- invariant [decided_in_seen]
--   ∀ n v, decision n v → W n v

-- invariant [crashedInRound_default]
--   ∀ n, alive n → crashedInRound n = 0

/-! ## Saturation: crash-free rounds -/

-- ghost relation crashedNow (n : node) := crashed n ∧ crashedInRound n = round
-- ghost relation roundParticipant (n : node) := alive n ∨ crashedNow n
-- ghost relation crashFreeRound (r : Nat) :=
--   ∀ n, ¬ crashed n ∨ crashedInRound n ≠ r
-- ghost relation hadCrashFreeRound := ∃ r, r < round ∧ crashFreeRound r

-- invariant [crash_round_gap]
--   numCrashed < round → hadCrashFreeRound

-- invariant [crash_round_gap_or_current]
--   numCrashed = round → hadCrashFreeRound ∨ crashFreeRound round

-- invariant [participants_have_equal_W_after_crash_free]
--   hadCrashFreeRound → ∀ n₁ n₂ v, roundParticipant n₁ ∧ roundParticipant n₂ → (W n₁ v = W n₂ v)

set_option veil.smt.trust false

#gen_spec

/-! ## Explicit-state model checking -/

#model_check { node := Fin 3, value := Fin 2 } { f := 1 }

/-! ## Bounded model checking -/

-- sat trace [initial_state] {}

-- sat trace [multiple_nodes_can_decide] {
--   any 3 actions
--   assert (∃ n₁ n₂ v₁ v₂,
--     n₁ ≠ n₂ ∧ decision n₁ v₁ ∧ decision n₂ v₂)
-- }

-- unsat trace [agreement_violation] {
--   any 3 actions
--   assert (¬ ∀ n₁ n₂ v₁ v₂, decision n₁ v₁ ∧ decision n₂ v₂ → v₁ = v₂)
-- }

/-! ## Checking the Inductive Invariant -/

-- #check_invariants

end FloodSet
