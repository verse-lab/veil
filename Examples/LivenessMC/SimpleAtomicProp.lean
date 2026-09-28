import Veil

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

liveness [chosenEqOne] □ ◇ ⌜ chosen = 1 ⌝

#gen_spec

#gen_executable

#eval Veil.LivenessMC.printCheckResult "Live" "□◇(chosen = 1)"
  (Veil.LivenessMC.check (enumerableTransitionSystem {})
    (chosenEqOne Theory (State FieldConcreteType) FieldConcreteType)
    (by native_decide) (by native_decide))

end Live
