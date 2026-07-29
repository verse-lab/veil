import Lean
open Lean

/-- Lean introduces a "synthetic" `sorry` when elaboration fails for a terms.
This differs from the `sorry` our SMT interaction introduces, which is the same
as user-typed `sorry`, i.e. non-synthetic. We use this to check that a
definition was correctly elaborated. -/
def isElaboratedCorrectly (n : Name) : MetaM Bool :=
  return !Expr.hasSyntheticSorry (← Meta.reduceAll $ ← Meta.mkConstWithFreshMVarLevels n)
