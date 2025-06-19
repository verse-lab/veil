import Veil.SMT.Solver
namespace Veil.SMT

-- /-- Our own version of the `smt` & `auto` tactics. -/
syntax (name := sauto) "sauto" Smt.Tactic.smtHints : tactic

open Lean Elab Tactic

/-- Converts `smtHints` into those understood by `lean-auto`. -/
def parseAutoHints : TSyntax `smtHints → TacticM (TSyntax `Auto.hints)
  | `(Smt.Tactic.smtHints| [ $[$hs:term],* ]) => `(Auto.hints| [$[$hs:term],*])
  | `(Smt.Tactic.smtHints| ) => `(Auto.hints| [])
  | _ => do throwError s!"Failure in parseAutoHints on {← getRef}"

private def solverStr (solver : Option SmtSolver := none) : String :=
  match solver with
  | some solver => s!"{solver}: "
  | none => ""

/-- A string to print when the solver returns `sat`. Factored out here
because it's used by `checkTheorems` in `Check.lean` to distinguish
between failures and `sat` from the solver .-/
def satGoalStr (solver : Option SmtSolver := none) : String := s!"{solverStr solver}the goal is false"
def unknownGoalStr (solver : Option SmtSolver := none) : String := s!"{solverStr solver}the goal is unknown"
def failureGoalStr (solver : Option SmtSolver := none) : String := s!"{solverStr solver}solver invocation failed"

@[tactic sauto] def elabSauto : Tactic := fun stx => withMainContext do
  let hints : TSyntax `smtHints := ⟨stx[1]⟩
  let mv ← Tactic.getMainGoal
  let withTimeout := veil.smt.timeout.get (← getOptions)
  -- If the user wants proof reconstruction, we simply call the `smt`
  -- tactic provided by `lean-smt`.
  let opts ← getOptions
  if veil.smt.reconstructProofs.get opts then
    let chosenTranslator := veil.smt.translator.get opts
    -- if chosenTranslator != .leanSmt then
      -- logInfo s!"Proof reconstruction is only supported with `lean-smt`, but `veil.smt.translator = {chosenTranslator}`. Falling back to `lean-smt`."
    let hints : TSyntax ``Smt.Tactic.smtHints := ⟨stx[1]⟩
    let smtSyntax ← `(tactic| smt $(hints):smtHints)
    trace[veil.smt] s!"proof reconstruction is on, so evaluating {smtSyntax}"
    Smt.Tactic.evalSmt smtSyntax
  else
    let cmdString := fun (translator : SmtTranslator) => do
      match translator with
      | .leanAuto => Veil.SMT.prepareLeanAutoQuery mv (← Veil.SMT.parseAutoHints hints)
      | .leanSmt => Veil.SMT.prepareLeanSmtQuery mv (← Smt.Tactic.elabHints hints)
    -- Due to [ufmg-smite#126](https://github.com/ufmg-smite/lean-smt/issues/126),
    -- we first use `lean-auto` to generate the query, and call `lean-smt` only
    -- if the query is satisfiable and we want to print a model,
    -- UNLESS the `veil.smt.translator` option overrides this behaviour.
    let translatorToUse := veil.smt.translator.get opts
    let originalCmdString ← cmdString translatorToUse
    let (res, solverUsed) ← Veil.SMT.querySolver originalCmdString withTimeout (retryOnUnknown := veil.smt.retryOnUnknown.get opts)
    match res with
    -- this shouldn't happen
    | .Sat none => throwError s!"{satGoalStr solverUsed}"
    | .Sat (some modelString) =>
      -- try to generate a readable model, using `lean-smt`
      let leanSmtQueryString ← if translatorToUse == .leanSmt then pure originalCmdString else cmdString .leanSmt
      -- FIXME: we are doing some crazy string manipulation in `getModelStr` to print counterexamples in `#check_invariants`,
      -- so please don't change the string format in the next two lines.
      let tryToMinimize := veil.smt.model.minimize.get opts
      let .some fostruct ← SMT.getReadableModel leanSmtQueryString withTimeout (minimize := tryToMinimize)
        | throwError s!"{satGoalStr solverUsed} (could not get readable model; {modelGenerationFailureDiagnostic}):\n{modelString}"
      -- Print that the model is not minimized if that we failed to
      -- minimize it and the user requested minimization.
      let mismatchedExpectation := tryToMinimize && !fostruct.isMinimized
      let minimizationWarning := if mismatchedExpectation then
        s!"\n(we could not minimize this model; {modelGenerationFailureDiagnostic})"
      else ""
      let modelString := minimizationWarning ++ fostruct.mkString
      throwError s!"{satGoalStr solverUsed}:{modelString}"
    | .Unknown reason => throwError "{unknownGoalStr solverUsed}{if reason.isSome then s!": {reason.get!}" else ""}"
    | .Failure reason => throwError "{failureGoalStr solverUsed}{if reason.isSome then s!": {reason.get!}" else ""}"
    | .Unsat => mv.admit (synthetic := false)

end Veil.SMT
