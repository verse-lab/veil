import Veil

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

liveness [alwaysTrue] □ ⊤
liveness [eventuallyFalse] ◇ ⊥

#gen_spec

#model_check {}

#eval Veil.LivenessMC.checkResultToString "Live" "□⊤"
  (Veil.LivenessMC.check (enumerableTransitionSystem {})
    (alwaysTrue Theory (State FieldConcreteType) FieldConcreteType)
    (by native_decide) (by native_decide))

#eval Veil.LivenessMC.checkResultToString "Live" "◇⊥"
  (Veil.LivenessMC.check (enumerableTransitionSystem {})
    (eventuallyFalse Theory (State FieldConcreteType) FieldConcreteType)
    (by native_decide) (by native_decide))

end Live
