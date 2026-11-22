module

public import Veil

open Lentil

/-! Under `veil.deferVCGeneration`, `#gen_spec` leaves `Init`, `NextStep` and the
other verification definitions to the first verification command. The model checker
gets its temporal formula at finalization, and proof preparation builds the shallow predicate. -/

set_option veil.deferVCGeneration true

veil module TemporalDeferVCGeneration

individual counter : Nat

#gen_state

after_init {
  counter := 0
}

action tick {
  counter := counter + 1
}

invariant [nonneg] counter ≥ 0

ghost relation positive := counter > 0

temporal [eventuallyPositive] ◇ ⌜ positive ⌝

#gen_spec

run_meta do
  let env ← Lean.getEnv
  unless env.contains `TemporalDeferVCGeneration.eventuallyPositive.ast &&
      !env.contains `TemporalDeferVCGeneration.eventuallyPositive do
    throwError "expected only the model-checking formula before proof preparation"

set_option veil.deferVCGeneration false in
#gen_spec

run_meta do
  unless (← Lean.getEnv).contains `TemporalDeferVCGeneration.eventuallyPositive do
    throwError "verification preparation did not generate the shallow predicate"

end TemporalDeferVCGeneration
