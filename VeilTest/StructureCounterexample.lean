import Veil

set_option veil.smt.trust false

namespace StructureCounterexampleTypes

@[veil_decl]
structure Payload where
  value : Int
  accepted : Bool

@[veil_decl]
structure Message where
  payload : Payload
  term : Int

end StructureCounterexampleTypes

open StructureCounterexampleTypes

veil module StructureCounterexampleProbe

individual message : Message

after_init {
  message := { payload := { value := 5, accepted := true }, term := 2 }
}

action change {
  message := { payload := { value := 4, accepted := false }, term := 3 }
}

invariant message = { payload := { value := 5, accepted := true }, term := 2 }

#gen_spec

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  inv_0 ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  change
    doesNotThrow ... ✅
    inv_0 ... ❌
      Counterexample (WP):
        Theory:

        Pre-state:
          message = {payload: {accepted: true, value: 5}, term: 2}
        Action: change
      Counterexample (TR):
        Theory:

        Pre-state:
          message = {payload: {accepted: true, value: 5}, term: 2}
        Action: change
        Post-state:
          message = {payload: {accepted: false, value: 4}, term: 3}
-/
#guard_msgs in
#check_invariants

end StructureCounterexampleProbe
