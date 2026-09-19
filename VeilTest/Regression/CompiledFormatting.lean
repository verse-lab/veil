import Veil

-- Lean's specialization cache can reuse list/pair formatting helpers from
-- Smt.Config's derived Repr instance. Compiled execution must generate its own
-- helper instead of pulling the SMT frontend and CVC5 into the native imports.
veil module CompiledFormatting
immutable individual rendered : String
individual flag : Bool
after_init { flag := false }
action toggle { flag := !flag }
invariant rendered = "[(\"a\", \"b\"), (\"c\", \"d\")]"
#gen_spec

/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check compiled {} { rendered := reprStr [("a", "b"), ("c", "d")] } (sequential := true)

/--
info: ✅ No violation in 1 traces
Seed: 1
-/
#guard_msgs in
#simulate compiled {} { rendered := reprStr [("a", "b"), ("c", "d")] }
  (seed := 1) (numTraces := 1) (maxSteps := 1)
end CompiledFormatting
