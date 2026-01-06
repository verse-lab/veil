import Veil

veil module MiniProtocol

-- set_option trace.veil.desugar true
-- set_option trace.veil.debug true

type node
relation rel : Nat → Bool
-- relation rel3 : node → node → node → Bool
function f : Nat → Option Nat
immutable function nodeToNat : node → Nat

#gen_state

after_init {
  -- rel N := false
  pure ()
}

action trivial (a : node) {
  let n := nodeToNat a
  -- rel n := true
  f n := some (n + 100)
}

invariant [inv_11] ∃ i < 10, (f i).isSome = false
termination true = true

-- run_cmd do
--   let a ← Lean.MonadLog.getFileName
--   Lean.logInfo m!"Logging to {a}"
set_option trace.veil.desugar true
#gen_spec
#print Instantiation
#print Theory
-- set_option trace.veil.desugar true
#time #model_check interpreted { node := Fin 9 } { nodeToNat := fun n => n.val }

-- def res :=
--   let __veil_inst : Instantiation := { node := Fin 3 }
--     let __veil_th : Theory __veil_inst.node := { }
--     Veil.ModelChecker.Concrete.findReachable (enumerableTransitionSystem __veil_inst.node __veil_th)
--       { invariants :=
--           [Veil.ModelChecker.SafetyProperty.mk (name := `inv_11) (property := fun th st => inv_11 th st)]
--         terminating :=
--           Veil.ModelChecker.SafetyProperty.mk (name := `termination_0) (property := fun th st =>
--             termination_0 th st)
--         earlyTerminationConditions := [Veil.ModelChecker.EarlyTerminationCondition.foundViolatingState] }

end MiniProtocol

-- export Ring (res)
