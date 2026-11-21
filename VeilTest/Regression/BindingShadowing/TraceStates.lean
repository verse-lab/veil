module

public import Veil

veil module TraceStateIndex

type st0
relation seen : st0 → Bool
individual flag : Bool

-- Fix the carrier so the displayed relation has one deterministic row.
assumption ∀ (x y : st0), x = y

after_init {
  flag := true
  seen X := true
}

action keep { pure () }
action clear (b : Bool) {
  require b
  flag := false
}

safety [falseInitially] ¬ flag
#gen_spec

/--
info: ✅ Satisfying trace found
  Instantiation:
    st0 = Fin 1
  State 0 (via init):
    seen = {0}
    flag = true
  State 1 (via clear(b=true)):
    seen = {0}
    flag = false
-/
#guard_msgs in
sat trace {
  any action
  assert (¬ flag)
}

#guard_msgs(drop info) in
#updr (expect := unsafe) certify

#gen_theorems

/-- info: 'TraceStateIndex.ic3_unsafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TraceStateIndex.ic3_unsafe

end TraceStateIndex
