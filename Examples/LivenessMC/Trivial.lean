module

public import Veil

veil module Live

individual chosen : Nat

#gen_state

after_init {
  chosen := 0
}

action choose {
  chosen := 1
}

safety [myexample]
  chosen = 0 ∨ chosen = 1

-- Checked in declaration order: `alwaysTrue` holds, and `eventuallyFalse` is then reported
-- together with a counterexample lasso.
temporal [alwaysTrue] □ ⊤
temporal [eventuallyFalse] ◇ ⊥

#gen_spec

set_option veil.violationIsError false in
#temporal_check {}

end Live
