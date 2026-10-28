module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! An action named like an enum constructor (`Cycle`). The bare constructor
name would resolve to the action, so the strengthening clause names the
constructor through the enum's class, in the solver queries and in the
printed clause. -/

veil module EnumClash

enum phase = {Cycle, Drive, Done}

individual pc : phase
individual armed : Bool
individual fired : Bool

#gen_state

after_init {
  pc := phase_EnumClass.Cycle
  armed := false
  fired := false
}

action Cycle {
  require pc = phase_EnumClass.Cycle
  pc := Drive
  armed := false
}

action drive {
  require pc = Drive
  pc := Done
}

action arm {
  require pc = phase_EnumClass.Cycle
  armed := true
}

action fire {
  require pc = Done ∧ armed
  fired := true
}

safety [never_fired] ¬ fired

#gen_spec

/-- invariant [ic3_0] pc = phase_EnumClass.Cycle ∨ ¬ armed -/
#guard_msgs(info, substring := true) in
#updr (fuel := 200) (expect := invariant) certify

#gen_theorems

/-- info: 'EnumClash.ic3_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EnumClash.ic3_safe

end EnumClash
