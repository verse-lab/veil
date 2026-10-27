module

public import Veil

/-
Veil translation/adaptation of TLA+ material from tlaplus/Examples.
Source: https://github.com/tlaplus/Examples/blob/a997ee6813b7c20951311e3658a8579270d9f306/specifications/DieHard/DieHard.tla
Copyright (c) 2016: The TLA+ project and other contributors.
Upstream MIT license: Benchmarks/TLA/TLAPlusExamples/LICENSE
-/


veil module DieHard

individual big : Nat
individual small : Nat

#gen_state

after_init {
  big := 0
  small := 0
}


action FillSmallJug {
  small := 3
  big := big
}


action FillBigJug  {
  big := 5
  small := small
}


action EmptySmallJug {
  small := 0
  big := big
}


action EmptyBigJug {
  big := 0
  small := small
}


action SmallToBig {
  let tmp := big
  big := if big + small < 5 then big + small else 5
  small := small - (big - tmp)
}



action BigToSmall {
  let tmp := small
  small := if big + small < 3 then big + small else 3
  big := big - (small - tmp)
}


invariant [typeOK] small≤ 3 ∧ big ≤ 5
invariant [not_solved] big ≠ 4

termination false

#gen_spec

-- TLC checks this spec with `Benchmarks/TLA/TLAPlusExamples/DieHard.cfg`.
-- The check below finds a violation of `not_solved`, whose trace solves the puzzle. TLC reports
-- `NotSolved` as violated with the same six steps.
-- `set_option veil.violationIsError false in` reports that violation without failing the build.

-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s. There are
-- none, hence `{}`. The cfg sets no constants either.
-- The theory (second argument) is left out, since this module has no `immutable` fields.

-- The other settings of the cfg:
-- * `INVARIANTS TypeOK NotSolved`: `#model_check` checks every `invariant` of the module, here
--   `typeOK` and `not_solved`.
-- * The cfg has no `CHECK_DEADLOCK`, so TLC checks for deadlocks. With `termination false`
--   above, Veil also reports every state without successors as a deadlock.
-- Options:
-- * `interpreted` runs the search only in Lean's interpreter, without compiling a checker.
set_option veil.violationIsError false in
#model_check interpreted {}


end DieHard
