import Veil
import LTLLib

/-!
# `#gen_executable`

Verifies that `#gen_executable` generates `enumerableTransitionSystem` (and therefore
makes `Veil.LivenessMC.check` usable) without needing to run `#model_check` first, that
it is idempotent, and that a subsequent `#model_check` still works.
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

safety [myexample]
  chosen = 0 ∨ chosen = 1

liveness [alwaysTrue] □ ⊤
liveness [eventuallyFalse] ◇ ⊥

#gen_spec

-- Generates `enumerableTransitionSystem`, without running the model checker.
#gen_executable
-- Idempotent: calling it again is a no-op.
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

-- `#model_check` after `#gen_executable` still works (idempotent generation).
#model_check {}

end Live
