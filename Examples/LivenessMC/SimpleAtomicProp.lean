module

public import Veil

veil module Live

individual chosen : Nat

#gen_state

after_init {
  chosen := 0
}

action noChoose {
  chosen := 0
}

action choose {
  chosen := 1
}

action stutter {
  require chosen = 1

  chosen := 1
}

safety [myexample]
  chosen = 0 ∨ chosen = 1

-- Fails: the run that only ever takes `noChoose` never sets `chosen`.
temporal [chosenEqOne] □ ◇ ⌜ chosen = 1 ⌝

#gen_spec

set_option veil.violationIsError false in
#temporal_check {}

end Live
