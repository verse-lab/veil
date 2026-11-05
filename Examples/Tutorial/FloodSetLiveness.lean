module

public import Veil
public import Veil.Liveness

/-! # FloodSet: liveness

The FloodSet protocol from `FloodSet.lean`, with temporal properties checked by Lasso.
-/

veil module FloodSetLiveness

open Lentil

type node
type value
instantiate val_ord : TotalOrder value

immutable individual f : Nat

individual round : Nat
function initialValue : node → value
relation W (n : node) (v : value) : Bool
relation decision (n : node) (v : value) : Bool
function crashed (n : node) : Bool
function crashedInRound (n : node) : Nat
individual numCrashed : Nat

ghost relation alive (n : node) := ¬crashed n
ghost relation crashedInAPreviousRound (n : node) := (crashed n ∧ crashedInRound n < round)
ghost relation decided (n : node) := ∃ v, decision n v

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

/-! ## Temporal properties -/

-- HOLDS: termination. Every run eventually reaches a point from which every node has
-- either decided or crashed, and stays there.
temporal [terminates]
  ◇ □ ⌜ ∀ n, crashed n ∨ decided n ⌝

-- HOLDS: once a node has decided, it stays decided.
temporal [decisionStable]
  ∀ n : node, □ (⌜ decided n ⌝ → □ ⌜ decided n ⌝)

-- FAILS: not every node is guaranteed to decide, because a node may crash before deciding.
temporal [everyoneDecides]
  ◇ ⌜ ∀ n, decided n ⌝

#gen_spec

/- ## Temporal model checking -/

#temporal_check [terminates] [decisionStable] { node := Fin 3, value := Fin 2 } { f := 1 }

set_option veil.violationIsError false in
#temporal_check [everyoneDecides] { node := Fin 3, value := Fin 2 } { f := 1 }

/- ## Temporal propeerty proof -/

set_option veil.smt.trust false

prove_temporal_by [decisionStable]
  -- The proof starts with the three conjuncts named, hInit : ⌜ Init ⌝,
  -- hNext : □⟨ NextStep ⟩ and hInv : □⌜ Invariants ⌝, and `decisionStable` unfolded
  tclear hInit hInv       -- stability only needs the transition relation
  tintro n                -- fix the node `n`

  -- Restate the goal over the ghost relation applied to the state directly,
  -- the form the first-order reduction in `veil_solve_temporal` recognizes
  tsuffices h :
   □ (⌜fun st => decided n th st⌝ → □ ⌜fun st => decided n th st⌝) by
    tassumption

  -- Strip the outer □: every hypothesis (only hNext) is itself under □
  ttoggle_goal_under_always
  tintro hd               -- hd : `n` has decided now

  -- Induction over the trace: □ p = p ∧ □ (p → ◯ p)
  trewrite [always_induction]
  tsplit_ands
  · tassumption           -- base case: `n` has decided now, by hd
  tclear hd               -- the inductive step holds at every position,
  ttoggle_goal_under_always  -- so strip its □ too

  -- One transition preserves `decided n`: reduce to FO VC and discharge it
  veil_solve_temporal

end FloodSetLiveness
