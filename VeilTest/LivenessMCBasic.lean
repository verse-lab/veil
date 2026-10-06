module

public import Veil

/-!
# Basic liveness model checking

`#liveness_check` accepts `□ ⊤` and finds a counterexample to `◇ ⊥`. Properties are checked in
declaration order and the first counterexample is reported, so a wrong verdict on either property
changes the message below.
-/

veil module Live

individual chosen : Nat

#gen_state

after_init {
  chosen := 0
}

action choose {
  chosen := 1
}

liveness [alwaysTrue] □ ⊤
liveness [eventuallyFalse] ◇ ⊥

#gen_spec

/--
error: ❌ Violation: liveness_failure (violates: eventuallyFalse)
  Stem:
    State 0:
      chosen = 0
    State 1:
      chosen = 1
  Loop (repeats):
    State 0:
      chosen = 1
    State 1:
      chosen = 1
-/
#guard_msgs in
#liveness_check interpreted {}

end Live
