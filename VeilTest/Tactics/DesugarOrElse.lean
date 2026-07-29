import Veil

/-! ## Test: `DesugarTacticM.orElse` properly backtracks accumulated tactics

The default `<|>` for `StateRefT` does not restore the mutable ref cell on
failure, so tactics recorded by the first branch would leak. Our custom
`DesugarTacticM.orElse` fixes this by saving/restoring the ref cell. -/

open Lean Elab Tactic in
open Veil in
/-- A test tactic that uses `DesugarTacticM.orElse`:
- First branch: records `skip`, then fails
- Second branch: records `trivial` and succeeds
Without proper backtracking, the output would show both `skip` and `trivial`. -/
elab "test_orElse_backtrack" : tactic => do
  let res : DesugarTacticM Unit := DesugarTacticM.orElse
    (do veilEvalTactic (← `(tactic| skip))
        throwError "intentional failure")
    (fun _ => do veilEvalTactic (← `(tactic| trivial)))
  res.runByOption (← getRef)

set_option veil.desugarTactic true

/--
info: After desugaring:
  [apply] trivial
-/
#guard_msgs (whitespace := lax) in
example : True := by test_orElse_backtrack

open Lean Elab Tactic in
open Veil in
/-- A test tactic that uses the default `<|>` (no backtracking of accumulated tactics):
- First branch: records `skip`, then fails
- Second branch: records `trivial` and succeeds
The output will show both `skip` and `trivial` because the ref cell leaks. -/
elab "test_default_orelse" : tactic => do
  let res : DesugarTacticM Unit :=
    (do veilEvalTactic (← `(tactic| skip))
        throwError "intentional failure") <|>
    (do veilEvalTactic (← `(tactic| trivial)))
  res.runByOption (← getRef)

/--
info: After desugaring:
  [apply] skip ; trivial
-/
#guard_msgs (whitespace := lax) in
example : True := by test_default_orelse
