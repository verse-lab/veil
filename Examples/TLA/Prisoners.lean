import Veil

/- https://github.com/tlaplus/Examples/blob/c2641e69204ed241cdf548d9645ac82df55bfcd8/specifications/Prisoners/Prisoners.tla -/
-- ------------------------------ MODULE Prisoners -----------------------------
veil module Prisoners

type prisoner

immutable individual cardPrisoner : Nat

immutable individual Counter : prisoner
individual switchAUp : Bool
individual switchBUp : Bool
function timesSwitched : prisoner → Nat
individual count : Nat

#gen_state

after_init {
  switchAUp := *
  switchBUp := *
  timesSwitched P := if P ≠ Counter then 0 else timesSwitched P
  count := 0
}

ghost relation Done := count = 2 * cardPrisoner - 1

action NonCounterStep (i : prisoner) {
  require i ≠ Counter
  if  (!switchAUp) ∧ (timesSwitched i < 2) then
    switchAUp := true;
    timesSwitched i := timesSwitched i + 1
  else
    switchBUp := !switchBUp
}

action CounterStep {
  if switchAUp then
    switchAUp := false;
    count := count + 1
  else
    switchBUp := !switchBUp
}

invariant [timesSwitchedlessEqual2] ∀p, p ≠ Counter → timesSwitched p ≤ 2
invariant [countBounded] count ≤ 2 * cardPrisoner - 1

safety [Safety] Done → (∀P, P ≠ Counter → timesSwitched P > 0)
#time #gen_spec

#model_check { prisoner := Fin 4 } { Counter := 1, cardPrisoner := 4 }


end Prisoners
