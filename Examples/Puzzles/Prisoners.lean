module

public import Veil

/-
Veil translation/adaptation of TLA+ material from tlaplus/Examples.
Copyright (c) 2016: The TLA+ project and other contributors.
Upstream MIT license: Benchmarks/TLA/TLAPlusExamples/LICENSE
-/

/- https://github.com/tlaplus/Examples/blob/c2641e69204ed241cdf548d9645ac82df55bfcd8/specifications/Prisoners/Prisoners.tla -/
-- ------------------------------ MODULE Prisoners -----------------------------
veil module Prisoners

type prisoner
-- To sum over `OtherPrisoner` in `CountInvariant`
instantiate prisonerEnum : Veil.Enumeration prisoner

immutable individual cardPrisoner : Nat

immutable individual Counter : prisoner
individual switchAUp : Bool
individual switchBUp : Bool
function timesSwitched : prisoner → Nat
individual count : Nat

#gen_state

-- ASSUME
--   /\ Counter \in Prisoner
--   /\ Cardinality(Prisoner) > 1
-- `Counter \in Prisoner` holds by the type of `Counter`.
assumption [more_than_one_prisoner] cardPrisoner > 1

-- Init ==
--   (*************************************************************************)
--   (* The initial predicate.                                                *)
--   (*************************************************************************)
--   /\ switchAUp \in BOOLEAN
--   /\ switchBUp \in BOOLEAN
--   /\ timesSwitched = [i \in OtherPrisoner |-> 0]
--   /\ count     = 0
after_init {
  switchAUp := *
  switchBUp := *
  timesSwitched P := if P ≠ Counter then 0 else timesSwitched P
  count := 0
}

-- Done == count = 2 * (Cardinality(Prisoner) - 1)
ghost relation Done := count = 2 * (cardPrisoner - 1)


-- NonCounterStep(i) ==
--   (*************************************************************************)
--   (* A prisoner other than the counter moves switch A up if it is down and *)
--   (* if (s)he has not already moved it up two times.  Otherwise, (s)he     *)
--   (* flips switch B.                                                       *)
--   (*************************************************************************)
--   /\ IF (~switchAUp) /\ (timesSwitched[i] < 2)
--        THEN /\ switchAUp' = TRUE
--             /\ timesSwitched' = [timesSwitched EXCEPT ![i] = @+1]
--             /\ UNCHANGED switchBUp
--        ELSE /\ switchBUp' = ~switchBUp
--             /\ UNCHANGED <<switchAUp, timesSwitched>>
--   /\ UNCHANGED count
action NonCounterStep (i : prisoner) {
  require i ≠ Counter
  if  (!switchAUp) ∧ (timesSwitched i < 2) then
    switchAUp := true;
    timesSwitched i := timesSwitched i + 1
  else
    switchBUp := !switchBUp
}


-- CounterStep ==
--   (*************************************************************************)
--   (* If switch A is up, the counter moves it down and increments his (or   *)
--   (* her) count.  Otherwise, (s)he flips switch B.                         *)
--   (*************************************************************************)
--   /\ IF switchAUp
--        THEN /\ switchAUp' = FALSE
--             /\ UNCHANGED switchBUp
--             /\ count' =  count + 1
--        ELSE /\ switchBUp' = ~switchBUp
--             /\ UNCHANGED <<switchAUp, count>>
--   /\ UNCHANGED timesSwitched
action CounterStep {
  if switchAUp then
    switchAUp := false;
    count := count + 1
  else
    switchBUp := !switchBUp
}

invariant [timesSwitchedlessEqual2] ∀p, p ≠ Counter → timesSwitched p ≤ 2
invariant [countBounded] count ≤ 2 * cardPrisoner - 1

-- CountInvariant ==
--   LET totalSwitched ==
--         LET sum[S \in SUBSET OtherPrisoner] ==
--               IF S = {} THEN 0
--                         ELSE LET p == CHOOSE pr \in S : TRUE
--                              IN  timesSwitched[p] + sum[S \ {p}]
--         IN  sum[OtherPrisoner]
--       oneIfUp == IF switchAUp THEN 1 ELSE 0
--   IN  count \in {totalSwitched - oneIfUp, totalSwitched - oneIfUp + 1}
-- The arithmetic is on `Int`, as in TLA+: `totalSwitched - oneIfUp` can be `-1`.
invariant [CountInvariant]
  let totalSwitched : Int :=
    (prisonerEnum.allValues.eraseDups.filter (· ≠ Counter)).foldl
      (fun total p => total + timesSwitched p) 0
  let oneIfUp : Int := if switchAUp then 1 else 0
  (count : Int) ∈ [totalSwitched - oneIfUp, totalSwitched - oneIfUp + 1]

safety [Safety] Done → (∀P, P ≠ Counter → timesSwitched P > 0)

-- Report every state without successors as a deadlock, as TLC does by default.
termination false

#time #gen_spec

-- TLC checks this spec with `Benchmarks/TLA/TLAPlusExamples/Prisoners.cfg`.
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s:
-- * `prisoner := Fin 4`: the prisoners are `0..3` (cfg: `Prisoner = {p1, p2, p3, p4}`).
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields:
-- * `Counter := 0`: prisoner `0` is the counter (cfg: `Counter = p1`).
-- * `cardPrisoner := 4`: the number of prisoners, TLA+'s `Cardinality(Prisoner)`. It must agree
--   with `prisoner` above. The cfg has no counterpart.
--
-- Before searching, `#model_check` checks these values against the `assumption` above, which
-- translates the spec's `ASSUME`.
--
-- The other settings of the cfg:
-- * `INVARIANT TypeOK`: `timesSwitchedlessEqual2` and `countBounded` above keep its bounds on
--   `timesSwitched` and `count`; Lean's types ensure the rest.
-- * `INVARIANT CountInvariant`: the `invariant [CountInvariant]` above.
-- * `PROPERTIES Safety`: `Safety == [](Done => ...)` holds when every reachable state satisfies
--   `Done => ...`, which the `safety [Safety]` clause above checks.
-- * `PROPERTIES Liveness`: the temporal property `<>Done`, which Veil does not check.
-- * The cfg has no `CHECK_DEADLOCK`, so TLC checks for deadlocks. With `termination false`
--   above, Veil also reports every state without successors as a deadlock.
-- Options:
-- * The check names no mode, so its search starts in Lean's interpreter and moves to a compiled
--   checker once that is built.
#model_check
{ prisoner := Fin 4 }
{ Counter := 0,
  cardPrisoner := 4 }


end Prisoners
