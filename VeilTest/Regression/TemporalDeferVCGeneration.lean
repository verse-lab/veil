module

public import Veil
public import Veil.Liveness

open Lentil

/-! Under `veil.deferVCGeneration`, `#gen_spec` leaves `Init`, `NextStep` and the
other verification definitions to the first verification command. A `temporal`
declaration needs them, so it must trigger their generation itself. -/

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

#gen_spec

temporal [eventuallyPositive] ◇ ⌜ positive ⌝

end TemporalDeferVCGeneration
