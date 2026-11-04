module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/CoffeeCan/CoffeeCan.tla
-- MaxBeanCount = 100, matching CoffeeCan100Beans.cfg, with `Init`'s full set of initial cans
-- (every (black, white) with 1 <= black + white <= 100).

veil module CoffeeCan

-- CONSTANT MaxBeanCount; ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1
-- Fixed at the .cfg's 100 rather than left a module parameter: `Init` has to enumerate
-- `0..MaxBeanCount` twice, and `pick` needs a concrete finite type to enumerate.
abbrev MaxBeanCount : Nat := 100

individual black : Nat
individual white : Nat

#gen_state

-- Init == can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}
-- A *set* of initial states, not one: `Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]`
-- and the constraint keeps the ones holding between 1 and MaxBeanCount beans. 5150 of them at
-- MaxBeanCount = 100. `EventuallyTerminates` and `TerminationHypothesis` both have to hold from
-- every one of them, which is the whole point of the puzzle, so initialising at a single can
-- would check a strictly weaker claim.
after_init {
  let b ← pick (Fin (MaxBeanCount + 1))
  let w ← pick (Fin (MaxBeanCount + 1))
  require b.val + w.val ≥ 1 ∧ b.val + w.val ≤ MaxBeanCount
  black := b.val
  white := w.val
}

-- PickSameColorBlack == /\ BeanCount > 1 /\ can.black >= 2 /\ can' = [can EXCEPT !.black = @ - 1]
action pickSameColorBlack {
  require black + white > 1 ∧ black ≥ 2
  black := black - 1
}

-- PickSameColorWhite == /\ BeanCount > 1 /\ can.white >= 2 /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]
action pickSameColorWhite {
  require black + white > 1 ∧ white ≥ 2
  black := black + 1
  white := white - 2
}

-- PickDifferentColor == /\ BeanCount > 1 /\ can.black >= 1 /\ can.white >= 1 /\ can' = [can EXCEPT !.black = @ - 1]
action pickDifferentColor {
  require black + white > 1 ∧ black ≥ 1 ∧ white ≥ 1
  black := black - 1
}

-- Termination == /\ BeanCount = 1 /\ UNCHANGED can
action terminationAction {
  require black + white = 1
}

-- `\/ UNCHANGED vars` — models TLA+'s implicit stuttering steps under `[][Next]_can`.
action stutter {
  pure ()
}

-- Not in the TLA+ source: it only ever checks EventuallyTerminates under Spec (with WF_can(Next)).
-- Not checked on TLC.
temporal [eventuallyTerminates] ◇ ⌜ black + white = 1 ⌝

-- Spec == Init /\ [][Next]_can /\ WF_can(Next); Next excludes stutter, so `◇T(Next)` is `◇¬T(stutter)`.
temporal [eventuallyTerminatesFair]
  (□ ◇ ¬ T(stutter)) → ◇ ⌜ black + white = 1 ⌝

-- TerminationHypothesis == IF can.white % 2 = 0 THEN <>(can.black=1 ∧ can.white=0) ELSE
-- <>(can.black=0 ∧ can.white=1). No `□` needed (unlike `~>`-shaped properties): this is a
-- plain `cond → ◇Q` formula, checked once from the initial state, same shape as
-- `ChangRoberts.lean`'s `elect`. Not in the TLA+ source unconditionally: it's only ever checked
-- under Spec (with WF_can(Next)).
-- Not checked on TLC.
temporal [terminationHypothesis]
  (⌜ white % 2 = 0 ⌝ → ◇ ⌜ black = 1 ∧ white = 0 ⌝) ∧
  (⌜ white % 2 ≠ 0 ⌝ → ◇ ⌜ black = 0 ∧ white = 1 ⌝)

temporal [terminationHypothesisFair]
  (□ ◇ ¬ T(stutter)) →
  ((⌜ white % 2 = 0 ⌝ → ◇ ⌜ black = 1 ∧ white = 0 ⌝) ∧
   (⌜ white % 2 ≠ 0 ⌝ → ◇ ⌜ black = 0 ∧ white = 1 ⌝))

#gen_spec

#temporal_check [eventuallyTerminatesFair] [terminationHypothesisFair] compiled {} {} (route := .fair)

end CoffeeCan
