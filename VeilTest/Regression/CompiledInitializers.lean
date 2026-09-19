import Veil
import VeilTest.Regression.CompiledInitializersHelper

-- These effects are not reachable from the checker entry point. Both anonymous
-- initialization and a named initializer whose result is unused must still run,
-- exactly once and in source order, before the model's configuration is read.
initialize initializationOrder : IO.Ref (Array Nat) ← do
  unless (← CompiledInitializersHelper.order.get) == #[0, 1] do
    throw <| IO.userError "imported initialization was omitted or reordered"
  IO.mkRef #[]
initialize initializationOrder.modify (·.push 1)
initialize unusedInitializationResult : Nat ← do
  initializationOrder.modify (·.push 2)
  return 42
initialize configuredLimit : Nat ← do
  unless (← initializationOrder.get) == #[1, 2] do
    throw <| IO.userError "model initialization was omitted or reordered"
  return 2

veil module CompiledInitializers
immutable individual limit : Nat
individual flag : Bool
after_init { flag := false }
action toggle { flag := !flag }
invariant limit = 2
#gen_spec

/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check compiled {} { limit := configuredLimit } (sequential := true)

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate compiled {} { limit := configuredLimit }
  (seed := 1) (numTraces := 1) (maxSteps := 1)

end CompiledInitializers
