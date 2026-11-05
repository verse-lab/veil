module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/Moving_Cat_Puzzle/Cat.tla
-- A cat hides among N boxes in a row and moves to an adjacent box nightly; a fixed morning sweep always finds her.
-- Config `CatOddBoxes.cfg`: `Spec` at `Number_Of_Boxes = 5`, checking `TypeOK` and `Victory`.

veil module MovingCatPuzzle

param Number_Of_Boxes : Nat

-- Directions == {"left", "right"}
enum Directions = { left, right }

individual cat_box : Nat
individual observed_box : Nat
individual direction : Directions

#gen_state

assumption [enough_boxes] Number_Of_Boxes ≥ 2

-- Boxes == 1 .. Number_Of_Boxes
ghost function Boxes : List Nat := List.range' 1 Number_Of_Boxes

-- Observed_Boxes == 2 .. Number_Of_Boxes - 1
ghost function Observed_Boxes : List Nat := List.range' 2 (Number_Of_Boxes - 2)

-- Init == cat_box \in Boxes /\ observed_box \in Observed_Boxes /\ direction \in Directions
after_init {
  let c : { c // c ∈ Boxes } :| true
  cat_box := c.val
  let o : { o // o ∈ Observed_Boxes } :| true
  observed_box := o.val
  direction := *
}

-- Move_Cat == (cat_box' = cat_box + 1 \/ cat_box' = cat_box - 1) /\ cat_box' \in Boxes
procedure Move_Cat {
  let b : { b // b ∈ Boxes } :| b.val = cat_box + 1 ∨ b.val = cat_box - 1
  cat_box := b.val
}

/-
Observe_Box ==
  LET next_box == IF direction = "right" THEN observed_box + 1 ELSE observed_box - 1
  IN \/ next_box \in Observed_Boxes /\ observed_box' = next_box /\ UNCHANGED direction
     \/ next_box \notin Observed_Boxes
        /\ direction' = CHOOSE d \in Directions: d /= direction
        /\ UNCHANGED observed_box
-/
procedure Observe_Box {
  let next_box := if direction = right then observed_box + 1 else observed_box - 1
  if next_box ∈ Observed_Boxes then
    observed_box := next_box
  else
    direction := if direction = right then left else right
}

-- Next == Move_Cat /\ Observe_Box
-- Named `Step` because `#gen_spec` declares the module's next-state relation as `Next`.
action Step {
  Move_Cat
  Observe_Box
}

-- Spec == Init /\ [][Next]_vars /\ WF_cat_box(Move_Cat)
-- \/ UNCHANGED vars
action stutter { pure () }

termination false

-- TypeOK == cat_box \in Boxes /\ observed_box \in Observed_Boxes /\ direction \in Directions
invariant [TypeOK] cat_box ∈ Boxes ∧ observed_box ∈ Observed_Boxes

-- Victory == <>(observed_box = cat_box)
temporal (only := check) [Victory] WF(Step) → ◇ ⌜ observed_box = cat_box ⌝

#gen_spec

#model_check { Number_Of_Boxes := 5, Directions := Directions_IndT }

#temporal_check { Number_Of_Boxes := 5, Directions := Directions_IndT }

end MovingCatPuzzle
