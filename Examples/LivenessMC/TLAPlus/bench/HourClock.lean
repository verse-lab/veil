module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/SpecifyingSystems/Liveness/LiveHourClock.tla
-- LSpec == HC /\ WF_hr(HCnxt), HC from HourClock.tla in the same directory.

veil module HourClock

individual hr : Nat

#gen_state

-- HCini == hr \in (1..12)
after_init {
  let h ← pick (Fin 12)
  hr := h.val + 1
}

-- HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1
action tick {
  hr := if hr ≠ 12 then hr + 1 else 1
}

-- \/ UNCHANGED hr — models TLA+'s implicit stuttering steps under `[][HCnxt]_hr`.
action stutter {
  pure ()
}

-- TypeInvariance == []HCini
invariant [typeInvariance] hr ≥ 1 ∧ hr ≤ 12

-- AlwaysTick == []<><<HCnxt>>_hr — `tick` is the only non-stutter action.
-- Not checked on TLC.
temporal [alwaysTick] □ ◇ T(tick)

-- AlwaysTick, checked against LSpec == HC /\ WF_hr(HCnxt).
temporal [alwaysTickFair]
  (□ ◇ T(tick)) → □ ◇ T(tick)

-- AllTimes == \A n \in 1..12 : []<>(hr = n) — literal Nat conjuncts, not a sort quantifier.
-- Not checked on TLC.
temporal [allTimes]
  □ ◇ ⌜ hr = 1 ⌝ ∧ □ ◇ ⌜ hr = 2 ⌝ ∧ □ ◇ ⌜ hr = 3 ⌝ ∧ □ ◇ ⌜ hr = 4 ⌝ ∧
  □ ◇ ⌜ hr = 5 ⌝ ∧ □ ◇ ⌜ hr = 6 ⌝ ∧ □ ◇ ⌜ hr = 7 ⌝ ∧ □ ◇ ⌜ hr = 8 ⌝ ∧
  □ ◇ ⌜ hr = 9 ⌝ ∧ □ ◇ ⌜ hr = 10 ⌝ ∧ □ ◇ ⌜ hr = 11 ⌝ ∧ □ ◇ ⌜ hr = 12 ⌝

-- AllTimes, checked against LSpec == HC /\ WF_hr(HCnxt).
temporal [allTimesFair]
  (□ ◇ T(tick)) →
  (□ ◇ ⌜ hr = 1 ⌝ ∧ □ ◇ ⌜ hr = 2 ⌝ ∧ □ ◇ ⌜ hr = 3 ⌝ ∧ □ ◇ ⌜ hr = 4 ⌝ ∧
   □ ◇ ⌜ hr = 5 ⌝ ∧ □ ◇ ⌜ hr = 6 ⌝ ∧ □ ◇ ⌜ hr = 7 ⌝ ∧ □ ◇ ⌜ hr = 8 ⌝ ∧
   □ ◇ ⌜ hr = 9 ⌝ ∧ □ ◇ ⌜ hr = 10 ⌝ ∧ □ ◇ ⌜ hr = 11 ⌝ ∧ □ ◇ ⌜ hr = 12 ⌝)

#gen_spec

#temporal_check [alwaysTickFair] [allTimesFair] compiled {} {} (route := .fair)

end HourClock
