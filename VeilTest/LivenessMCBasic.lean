import Veil
import LTLLib

/-!
# Basic liveness model checking

Verifies that `Veil.LivenessMC.check` accepts `□ ⊤` and finds a counterexample to `◇ ⊥`.
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

#gen_executable

#eval show IO Unit from do
  match Veil.LivenessMC.check (enumerableTransitionSystem {})
      (alwaysTrue Theory (State FieldConcreteType) FieldConcreteType)
      (by native_decide) (by native_decide) with
  | .empty _ => pure ()
  | .nonEmpty .. => throw (IO.userError "expected `alwaysTrue` to hold")

#eval show IO Unit from do
  match Veil.LivenessMC.check (enumerableTransitionSystem {})
      (eventuallyFalse Theory (State FieldConcreteType) FieldConcreteType)
      (by native_decide) (by native_decide) with
  | .nonEmpty .. => pure ()
  | .empty _ => throw (IO.userError "expected `eventuallyFalse` to be violated")

end Live
