module

public import Veil

-- Lean's specialization cache can reuse list/pair formatting helpers from
-- Smt.Config's derived Repr instance. Compiled execution must generate its own
-- helper instead of pulling the SMT frontend and CVC5 into the native imports.
-- The native dependency graph must exclude all verification-only imports,
-- even on platforms whose CVC5 libraries would happen to link successfully.
run_cmd do
  let imports ← Lean.Elab.Command.liftCoreM <|
    Veil.ModelChecker.Compilation.executionImports (← Lean.getEnv)
  for name in imports do
    if [`Smt, `Auto, `cvc5].any (·.isPrefixOf name) then
      throwError "verification dependency in native imports: {name}"

set_option compiler.postponeCompile false in
def renderPairs (xs : List (String × String)) : String := reprStr xs

veil module CompiledFormatting
immutable individual rendered : String
individual flag : Bool
after_init { flag := false }
action toggle { flag := !flag }
invariant rendered = "[(\"a\", \"b\"), (\"c\", \"d\")]"
#gen_spec

/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check compiled {} { rendered := renderPairs [("a", "b"), ("c", "d")] } (sequential := true)

/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check {} { rendered := renderPairs [("a", "b"), ("c", "d")] } (sequential := true)

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate compiled {} { rendered := renderPairs [("a", "b"), ("c", "d")] }
  (seed := 1) (numTraces := 1) (maxSteps := 1)
end CompiledFormatting
