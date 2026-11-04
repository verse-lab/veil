module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/Moving_Cat_Puzzle/Cat.tla
-- Number_Of_Boxes = 5 (CatOddBoxes.cfg), so Boxes = 1..5 and Observed_Boxes = 2..4.

veil module MovingCatPuzzle

individual cat_box : Nat
individual observed_box : Nat
individual direction : Bool

#gen_state

-- Init == cat_box \in Boxes /\ observed_box \in Observed_Boxes /\ direction \in Directions
-- A *set* of 5 * 3 * 2 = 30 initial states, not one. `Victory` has to hold wherever the cat
-- starts and wherever the search starts in its pattern — that is the puzzle — so initialising at
-- a single (cat_box, observed_box, direction) would check a strictly weaker claim. TLC explores
-- exactly these 30 states.
after_init {
  let c ← pick (Fin 5)
  let o ← pick (Fin 3)
  let d ← pick Bool
  cat_box := c.val + 1
  observed_box := o.val + 2
  direction := d
}

-- Next == Move_Cat /\ Observe_Box, with cat_box' = cat_box - 1
action moveLeft {
  require cat_box ≥ 2
  cat_box := cat_box - 1
  let next_box := if direction then observed_box + 1 else observed_box - 1
  observed_box := if next_box ≥ 2 ∧ next_box ≤ 4 then next_box else observed_box
  direction := if next_box ≥ 2 ∧ next_box ≤ 4 then direction else !direction
}

-- Next == Move_Cat /\ Observe_Box, with cat_box' = cat_box + 1
action moveRight {
  require cat_box ≤ 4
  cat_box := cat_box + 1
  let next_box := if direction then observed_box + 1 else observed_box - 1
  observed_box := if next_box ≥ 2 ∧ next_box ≤ 4 then next_box else observed_box
  direction := if next_box ≥ 2 ∧ next_box ≤ 4 then direction else !direction
}

-- \/ UNCHANGED vars — models TLA+'s implicit stuttering steps under `[][Next]_vars`.
action stutter {
  pure ()
}

-- Victory == <>(observed_box = cat_box)
-- Not in the TLA+ source: its .cfg only ever checks Victory under the fair Spec.
-- Not checked on TLC.
temporal [victory] ◇ ⌜ observed_box = cat_box ⌝

-- Spec's `WF_cat_box(Move_Cat)`: the cat is always able to move (N >= 2), so this is
-- exactly "no infinite stuttering".
temporal [victoryFair]
  (□ ◇ ¬ T(stutter)) → ◇ ⌜ observed_box = cat_box ⌝

#gen_spec

#temporal_check [victoryFair] compiled {} {} (route := .fair)

end MovingCatPuzzle
