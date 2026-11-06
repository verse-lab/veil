module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/CoffeeCan/CoffeeCan.tla
-- Gries' coffee can problem: drawing two beans and returning one shrinks the can by one bean a step.
-- CoffeeCan100Beans.cfg (MaxBeanCount = 100).

veil module CoffeeCan

param MaxBeanCount : Nat

-- Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]
@[veil_decl] structure Can where
  black : Nat
  white : Nat

individual can : Can

#gen_state

-- ASSUME MaxBeanFact == MaxBeanCount \in Nat /\ MaxBeanCount >= 1 — \in Nat is the Lean type.
assumption [MaxBeanFact] MaxBeanCount ≥ 1

ghost function BeanCount := can.black + can.white

-- Init == can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}
after_init {
  let (b, w) : { b : Nat // b ∈ List.range' 0 (MaxBeanCount + 1) }
             × { w : Nat // w ∈ List.range' 0 (MaxBeanCount + 1) } :|
    b.val + w.val ∈ List.range' 1 MaxBeanCount
  can := { black := b.val, white := w.val }
}

-- MonotonicDecrease == [][BeanCount' < BeanCount]_can
-- Reads `can'`, so it is a procedure every step calls rather than a temporal formula.
procedure MonotonicDecrease (old : Can) {
  assert can.black + can.white < old.black + old.white
}

-- LoopInvariant == [][can.white % 2 = 0 <=> can'.white % 2 = 0]_can
procedure LoopInvariant (old : Can) {
  assert (old.white % 2 = 0 ↔ can.white % 2 = 0)
}

-- PickSameColorBlack == BeanCount > 1 /\ can.black >= 2 /\ can' = [can EXCEPT !.black = @ - 1]
action PickSameColorBlack {
  require BeanCount > 1
  require can.black ≥ 2
  let old := can
  can := { can with black := can.black - 1 }
  MonotonicDecrease old
  LoopInvariant old
}

-- PickSameColorWhite == BeanCount > 1 /\ can.white >= 2 /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]
action PickSameColorWhite {
  require BeanCount > 1
  require can.white ≥ 2
  let old := can
  can := { can with black := can.black + 1, white := can.white - 2 }
  MonotonicDecrease old
  LoopInvariant old
}

-- PickDifferentColor == BeanCount > 1 /\ can.black >= 1 /\ can.white >= 1 /\ can' = [can EXCEPT !.black = @ - 1]
action PickDifferentColor {
  require BeanCount > 1
  require can.black ≥ 1
  require can.white ≥ 1
  let old := can
  can := { can with black := can.black - 1 }
  MonotonicDecrease old
  LoopInvariant old
}

-- Termination == BeanCount = 1 /\ UNCHANGED can
action Termination {
  require BeanCount = 1
}

-- Next == PickSameColorWhite \/ PickSameColorBlack \/ PickDifferentColor \/ Termination
termination false

-- TypeInvariant == can \in Can
invariant [TypeInvariant] can.black ≤ MaxBeanCount ∧ can.white ≤ MaxBeanCount

-- Spec == Init /\ [][Next]_can /\ WF_can(Next)

-- EventuallyTerminates == <>(ENABLED Termination)
temporal (only := check) [EventuallyTerminates]
  (□ ◇ (T(PickSameColorWhite) ∨ T(PickSameColorBlack) ∨ T(PickDifferentColor)
        ∨ ¬ (E(PickSameColorWhite) ∨ E(PickSameColorBlack) ∨ E(PickDifferentColor))))
    → ◇ E(Termination)

-- TerminationHypothesis == IF can.white % 2 = 0 THEN <>(can.black = 1 /\ can.white = 0)
--                                               ELSE <>(can.black = 0 /\ can.white = 1)
temporal (only := check) [TerminationHypothesis]
  (□ ◇ (T(PickSameColorWhite) ∨ T(PickSameColorBlack) ∨ T(PickDifferentColor)
        ∨ ¬ (E(PickSameColorWhite) ∨ E(PickSameColorBlack) ∨ E(PickDifferentColor))))
    → ((⌜ can.white % 2 = 0 ⌝ → ◇ ⌜ can.black = 1 ∧ can.white = 0 ⌝)
       ∧ (⌜ can.white % 2 ≠ 0 ⌝ → ◇ ⌜ can.black = 0 ∧ can.white = 1 ⌝))

#gen_spec

#model_check compiled { MaxBeanCount := 100 } {}
#temporal_check compiled { MaxBeanCount := 100 } {}
