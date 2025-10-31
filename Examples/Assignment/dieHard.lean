import Veil

veil module DieHard

-- ------------------------------ MODULE DieHard -------------------------------
-- (***************************************************************************)
-- (* In the movie Die Hard 3, the heroes must obtain exactly 4 gallons of     *)
-- (* water using a 5 gallon jug, a 3 gallon jug, and a water faucet.  Our    *)
-- (* goal: to get TLC to solve the problem for us.                           *)
-- (*                                                                         *)
-- (* First, we write a spec that describes all allowable behaviors of our    *)
-- (* heroes.                                                                  *)
-- (***************************************************************************)
-- EXTENDS Naturals
--   (*************************************************************************)
--   (* This statement imports the definitions of the ordinary operators on   *)
--   (* natural numbers, such as +.                                           *)
--   (*************************************************************************)

-- (***************************************************************************)
-- (* We next declare the specification's variables.                          *)
-- (***************************************************************************)
-- VARIABLES big,   \* The number of gallons of water in the 5 gallon jug.
--           small  \* The number of gallons of water in the 3 gallon jug.

individual big : Nat
individual tmp : Nat
individual small : Nat
-- (***************************************************************************)
-- (* We now define TypeOK to be the type invariant, asserting that the value *)
-- (* of each variable is an element of the appropriate set.  A type          *)
-- (* invariant like this is not part of the specification, but it's          *)
-- (* generally a good idea to include it because it helps the reader         *)
-- (* understand the spec.  Moreover, having TLC check that it is an          *)
-- (* invariant of the spec catches errors that, in a typed language, are     *)
-- (* caught by type checking.                                                *)
-- (*                                                                         *)
-- (* Note: TLA+ uses the convention that a list of formulas bulleted by /\   *)
-- (* or \/ denotes the conjunction or disjunction of those formulas.         *)
-- (* Indentation of subitems is significant, allowing one to eliminate lots  *)
-- (* of parentheses.  This makes a large formula much easier to read.        *)
-- (* However, it does mean that you have to be careful with your indentation.*)
-- (***************************************************************************)
#gen_state

after_init {
  big := 0
  small := 0
  tmp := 0
}
-- (***************************************************************************)
-- (* Now we define the actions that our hero can perform.  There are three    *)
-- (* things they can do:                                                     *)
-- (*                                                                         *)
-- (*   - Pour water from the faucet into a jug.                              *)
-- (*                                                                         *)
-- (*   - Pour water from a jug onto the ground.                              *)
-- (*                                                                         *)
-- (*   - Pour water from one jug into another                                *)
-- (*                                                                         *)
-- (* We now consider the first two.  Since the jugs are not calibrated,       *)
-- (* partially filling or partially emptying a jug accomplishes nothing.      *)
-- (* So, the first two possibilities yield the following four possible        *)
-- (* actions.                                                                *)
-- (***************************************************************************)

-- FillSmallJug  == /\ small' = 3
--                  /\ big' = big
action FillSmallJug {
  small := 3
  big := big
}

-- FillBigJug    == /\ big' = 5
--                  /\ small' = small
action FillBigJug {
  big := 5
  small := small
}

-- EmptySmallJug == /\ small' = 0
--                  /\ big' = big
action EmptySmallJug {
  small := 0
  big := big
}

-- EmptyBigJug   == /\ big' = 0
--                  /\ small' = small
action EmptyBigJug {
  big := 0
  small := small
}

-- SmallToBig == /\ big'   = Min(big + small, 5)
--               /\ small' = small - (big' - big)
action SmallToBig {
  tmp := big
  big := if big + small < 5 then big + small else 5
  small := small - (big - tmp)
}

-- BigToSmall == /\ small' = Min(big + small, 3)
--               /\ big'   = big - (small' - small)
action BigToSmall {
  tmp := small
  small := if big + small < 3 then big + small else 3
  big := big - (small - tmp)
}


-- TypeOK == /\ small \in 0..3
--           /\ big   \in 0..5
invariant [typeOK] small≤ 3 ∧ big ≤ 5

-- NotSolved == big # 4
invariant [not_solved] big ≠ 4

#gen_spec

-- #check_invariants

end DieHard
