module

public import Veil

veil module RiverCrossing

enum position = {near, far}
individual wolf_pos : position
individual goat_pos : position
individual cabbage_pos : position
individual farmer_pos : position

-- enum act = {Init, FarmerAndWolf, FarmerAndGoat, FarmerAndCabbage, FarmerAlone}
-- individual lastAction : act

#gen_state

/-
Puzzle Rules:
 * If goat and wolf are on the same bank p, the farmer must also be on p.
 * If goat and cabbage are on the same bank p, the farmer must also be on p.
-/
ghost relation safety_constraint :=
     (goat_pos = wolf_pos → farmer_pos = goat_pos) ∧
     (goat_pos = cabbage_pos → farmer_pos = goat_pos)

after_init {
  wolf_pos := near
  goat_pos := near
  cabbage_pos := near
  farmer_pos := near
}

action FarmerAndWolf {
  require farmer_pos = wolf_pos
  if farmer_pos = far then
    farmer_pos := near
    wolf_pos := near
    assume safety_constraint
  else
    farmer_pos := far
    wolf_pos := far
    assume safety_constraint
}

action FarmerAndGoat {
  require farmer_pos = goat_pos
  if farmer_pos = far then
    farmer_pos := near
    goat_pos := near
    assume safety_constraint
  else
    farmer_pos := far
    goat_pos := far
    assume safety_constraint
}


action FarmerAndCabbage {
  require farmer_pos = cabbage_pos
  if farmer_pos = far then
    farmer_pos := near
    cabbage_pos := near
    assume safety_constraint
  else
    farmer_pos := far
    cabbage_pos := far
    assume safety_constraint
}

action FarmerAlone {
  if farmer_pos = far then
    farmer_pos := near
    assume safety_constraint
  else
    farmer_pos := far
    assume safety_constraint
}

invariant [Safe] safety_constraint
invariant [unsolved] ¬ (goat_pos = far ∧ wolf_pos = far ∧ cabbage_pos = far ∧ farmer_pos = far)

termination false

#time #gen_spec

-- TLC checks the same puzzle with `Benchmarks/TLA/RiverCrossing.cfg`, on `RiverCrossing.tla`,
-- which extends `FarmerGooseFox.tla` (`Benchmarks/TLA/scripts/fetch_upstream.py` downloads it).
-- There the wolf, the goat and the cabbage are the fox, the goose and the beans, and the banks
-- `near` and `far` are `Here` and `There`.
-- The check below finds a violation of `unsolved`, whose trace solves the puzzle. TLC reports
-- `Unsolved` as violated in the same way.
-- `set_option veil.violationIsError false in` reports that violation without failing the build.
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s. It is
-- empty here: `position` is an `enum`, which needs no instantiation. The cfg sets no constants
-- either.
-- The theory (second argument) is left out, since this module has no `immutable` fields.
-- The other settings of the cfg:
-- * `INVARIANT Unsolved`: the `invariant [unsolved]` above.
-- * `INVARIANT TypeOK`: Lean's types ensure it.
-- * The TLA+ `Next` requires `Safe'`. Here each action assumes `safety_constraint` after its
--   move instead, and the extra `invariant [Safe]` checks it.
-- * The cfg has no `CHECK_DEADLOCK`, so TLC checks for deadlocks. With `termination false`
--   above, Veil also reports every state without successors as a deadlock.
-- Options:
-- * `interpreted` runs the search only in Lean's interpreter, without compiling a checker.
set_option veil.violationIsError false in
#model_check interpreted {  }

end RiverCrossing
