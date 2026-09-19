module

public import Veil

veil module CompiledCheckWithVerification

type node
individual flag : Bool
relation seen : node → Bool

#gen_state

after_init {
  flag := false
  seen N := false
}

action mark (n : node) {
  seen n := true
  flag := true
}

invariant [flag_set] (∃ N, seen N) → flag

#gen_spec

-- Compile a checker before the solver has ever run in this file.
/-- info: ✅ No violation (explored 4 states) -/
#guard_msgs in
#model_check compiled { node := Fin 2 } {} (sequential := true)

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  flag_set ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  mark
    doesNotThrow ... ✅
    flag_set ... ✅
-/
#guard_msgs(info, drop warning) in
#check_invariants

-- Compile again after the solver has run, at a different instantiation and
-- without `sequential`, so the parallel entry point is compiled too.
/-- info: ✅ No violation (explored 8 states) -/
#guard_msgs in
#model_check compiled { node := Fin 3 } {}

-- Compiled simulation shares the emitted-C path with `#model_check compiled` but
-- builds a different entry point. `simulateLoopM` walks the traces sequentially
-- from `seed`, so the output is reproducible; `mark` is always enabled, so every
-- trace runs out of steps rather than stopping early and the depth histogram is
-- pinned by `maxSteps` and `numTraces` rather than by the draws.
/--
info: ✅ No violation in 2 traces
Trace depths: 3x2
Seed: 1
-/
#guard_msgs in
#simulate compiled { node := Fin 3 } {} (seed := 1) (numTraces := 2) (maxSteps := 3)

-- The interpreted path must still work in a file that has compiled binaries.
/--
info: ✅ No violation in 3 traces
Trace depths: 4x3
Seed: 7
-/
#guard_msgs in
#simulate { node := Fin 2 } {} (seed := 7) (numTraces := 3) (maxSteps := 4)

end CompiledCheckWithVerification

-- The native dependency graph must stay free of verification-only imports even
-- after the solver has run in this file, and on platforms whose CVC5 libraries
-- would happen to link successfully.
run_cmd do
  let imports ← Lean.Elab.Command.liftCoreM <|
    Veil.ModelChecker.Compilation.executionImports (← Lean.getEnv)
  for name in imports do
    if [`Smt, `Auto, `cvc5].any (·.isPrefixOf name) then
      throwError "verification dependency in native imports: {name}"
