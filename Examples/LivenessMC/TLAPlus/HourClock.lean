module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/SpecifyingSystems/Liveness/LiveHourClock.tla
-- Lamport's hour clock: `hr` cycles through 1..12 forever. Config `LiveHourClock.cfg`, `LSpec == HC /\ WF_hr(HCnxt)`.
-- HCini, HCnxt and HC come from HourClock.tla, which it EXTENDS.

veil module HourClock

individual hr : Nat

#gen_state

-- HCini == hr \in (1 .. 12)
ghost relation HCini := hr ∈ List.range' 1 12

-- HC == HCini /\ [][HCnxt]_hr
after_init {
  let h ← pick { h // h ∈ List.range' 1 12 }
  hr := h.val
}

-- HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1
action HCnxt {
  hr := if hr ≠ 12 then hr + 1 else 1
}

-- \/ UNCHANGED hr — the stuttering `[][HCnxt]_hr` admits; the `WF(HCnxt)` hypotheses below rule it out.
action stutter { pure () }

-- LiveHourClock.cfg has no CHECK_DEADLOCK FALSE, so TLC checks deadlock; this matches it.
termination false

-- TypeInvariance == []HCini
invariant [TypeInvariance] HCini

-- AlwaysTick == []<><<HCnxt>>_hr
temporal (only := check) [AlwaysTick] WF(HCnxt) → □ ◇ T(HCnxt)

-- AllTimes == \A n \in 1..12 : []<>(hr = n)
temporal (only := check) [AllTimes]
  WF(HCnxt) → ∀ n : { n // n ∈ List.range' 1 12 }, □ ◇ ⌜ hr = n.val ⌝

#gen_spec

#model_check {}

#temporal_check {}

end HourClock
