module

public import Veil
veil module FloodSet

type node
type value
instantiate val_ord : TotalOrder value

immutable individual f : Nat                        -- maximum number of crash failures

individual round : Nat                              -- current round number (0 to f+1)
function initialValue : node → value                -- initial proposal for each node
relation W (n : node) (v : value) : Bool            -- W set per node
relation decision (n : node) (v : value) : Bool     -- decision value per node, initially ∅
function crashed (n : node) : Bool                  -- has this node crashed?
function crashedInRound (n : node) : Nat            -- which round did it crash in?
individual numCrashed : Nat                         -- total number of crashes so far

veil_set_field_representation relation Veil.ArrayAsFinset
veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

ghost relation alive (n : node) := ¬crashed n
ghost relation crashedInAPreviousRound (n : node) := (crashed n ∧ crashedInRound n < round)

after_init {
  initialValue := *
  round := 0
  W N V := (V == initialValue N)
  decision N V := false
  crashed N := false
  crashedInRound N := 0
  numCrashed := 0
}

action crash (n : node) {
  require numCrashed < f
  require alive n
  crashed n := true
  crashedInRound n := round
  numCrashed := numCrashed + 1
}

action advanceRound {
  require round < f + 1
  -- We model message delivery by picking a delivery relation that determines
  -- which messages from each sender are received by which receivers.
  let delivery : (node → node → Bool) :|
    (∀ (sender : node),
      (crashedInAPreviousRound sender → (∀ (receiver : node), ¬ delivery sender receiver)) ∧
      (alive sender → (∀ (receiver : node), delivery sender receiver)))
  -- A node knows a value at the end of this round iff it either already knew it,
  -- or received it from some sender that knew it.
  W N V := decide $ W N V ∨ (alive N ∧ ∃ sender, delivery sender N ∧ W sender V)
  round := round + 1
}

procedure deterministicDecision (n : node) {
  let v ← pick value
  assume (W n v ∧ (∀ v', W n v' → val_ord.le v v'))
  return v
}

action nodeDecide (n : node) {
  require round = f + 1
  require alive n
  require ¬(∃ v, decision n v)
  let v ← deterministicDecision n
  decision n v := true
}

safety [agreement]
  ∀ n₁ n₂ v₁ v₂, decision n₁ v₁ ∧ decision n₂ v₂ → v₁ = v₂

safety [strong_validity]
  ∀ n v, decision n v → ((∃ m, initialValue m = v))


invariant [decision_minimum_seen]
  ∀ n v, decision n v → (∀ v', W n v' → val_ord.le v v')

invariant [every_seen_is_someones_initial]
  ∀ n v, W n v → (∃ m, initialValue m = v)

invariant [initial_value_in_W]
  ∀ n, W n (initialValue n)

invariant [decision_crashed_after_end]
  ∀ n v, decision n v ∧ crashed n → crashedInRound n ≥ f + 1

invariant [decision_only_at_end]
  ∀ n v, decision n v → round ≥ f + 1

ghost relation allAliveSameSeen :=
  ∀ n₁ n₂ v, alive n₁ ∧ alive n₂ → (W n₁ v = W n₂ v)

invariant [no_crash_then_synced]
  numCrashed < round → allAliveSameSeen

invariant [no_crashes_def]
  numCrashed = 0 ↔ ∀ n, alive n

invariant [max_crashes]
  numCrashed ≤ f

invariant [decided_value_seen_by_alive_and_min]
  numCrashed < round → ∀ n₁ n₂ v, decision n₁ v ∧ alive n₂ → W n₂ v ∧ (∀ v', W n₂ v' → val_ord.le v v')

ghost relation crashedInThisRound (n : node) := crashed n ∧ ¬ crashedInAPreviousRound n

invariant [crashed_in_round_le_round]
  ∀ n, crashedInRound n ≤ round

invariant [crashed_this_round]
  ∀ n m v, numCrashed = round ∧ crashedInThisRound n ∧ alive m → (W n v = W m v)

invariant [crashed_this_round_synced]
  numCrashed < round → ∀ n m v, (alive n ∨ crashedInThisRound n) ∧ (alive m ∨ crashedInThisRound m) → (W n v = W m v)

-- set_option veil.smt.timeout 500

#gen_spec

#model_check compiled { node := Fin 3, value := Fin 3 } { f := 3 } (seenSet := HAMTMapShard)

-- Uncomment to check
-- #check_invariants


end FloodSet
