import Smt

/- Prepared diagnostic, not executed. This isolates loss of universe levels
   in dependency bookkeeping, not the model-specific precursor that exposes
   DecidableEq. It does not ask the solver to encode DecidableEq. -/

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let original := mkConst ``DecidableEq [Level.succ Level.zero]
  let _ ← inferType original
  let ((_, dependencies, _), _) ← (Smt.Translator.translateExpr original).run {}
  unless dependencies.contains ``DecidableEq do
    throwError "expected the generic translator to record DecidableEq"
  let rebuilt := mkConst ``DecidableEq -- Query.lean:64's reconstruction
  let failure ← try
    let _ ← inferType rebuilt
    pure none
  catch ex => pure (some (← ex.toMessageData.toString))
  let some failure := failure
    | throwError "expected missing universe arguments to be rejected"
  logInfo m!"Valid input constant lost its universe levels through NameSet dependencies: {failure}"
