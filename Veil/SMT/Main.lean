import Lean
import Auto
import Smt

import Veil.SMT.Base
import Veil.SMT.Translation
import Veil.SMT.Solver
import Veil.Util.Meta

/- Not actually used here, but re-exported. -/
import Veil.SMT.Preparation
import Veil.SMT.Quantifiers.Elimination
import Veil.SMT.Model

namespace Veil.SMT

-- /-- Our own version of the `smt` & `auto` tactics. -/
syntax (name := sauto) "sauto" Smt.Tactic.smtHints Smt.Tactic.smtTimeout : tactic

open Lean Elab Tactic

/-- Converts `smtHints` into those understood by `lean-auto`. -/
def parseAutoHints : TSyntax `smtHints → TacticM (TSyntax `Auto.hints)
  | `(Smt.Tactic.smtHints| [ $[$hs],* ]) => `(Auto.hints| [$[$hs:term],*])
  | `(Smt.Tactic.smtHints| ) => `(Auto.hints| [])
  | _ => throwUnsupportedSyntax

/- We use our own `parseTimeout` because the one in `lean-smt` has a
  hard-coded `5` as default if no timeout is specified. -/
def parseTimeout : TSyntax `smtTimeout → CoreM Nat
  | `(Smt.Tactic.smtTimeout| (timeout := $n)) => return n.getNat
  | `(Smt.Tactic.smtTimeout| ) => return (auto.smt.timeout.get (← getOptions))
  | _ => throwUnsupportedSyntax

/-- A string to print when the solver returns `sat`. Factored out here
because it's used by `checkTheorems` in `Check.lean` to distinguish
between failures and `sat` from the solver .-/
def satGoalStr : String := "the goal is false"
def unknownGoalStr : String := "the solver returned unknown"
def failureGoalStr : String := "solver invocation failed"

@[tactic sauto] def elabSauto : Tactic := fun stx => withMainContext do
  let mv ← Tactic.getMainGoal
  let withTimeout ← parseTimeout ⟨stx[2]⟩
  -- If the user wants proof reconstruction, we simply call the `smt`
  -- tactic provided by `lean-smt`.
  let opts ← getOptions
  if veil.smt.reconstructProofs.get opts then
    let chosenTranslator := veil.smt.translator.get opts
    if chosenTranslator != .leanSmt then
      logInfo s!"Proof reconstruction is only supported with `lean-smt`, but `veil.smt.translator = {chosenTranslator}`. Falling back to `lean-smt`."
    Smt.Tactic.evalSmt stx
  else
    -- Due to [ufmg-smite#126](https://github.com/ufmg-smite/lean-smt/issues/126),
    -- we first use `lean-auto` to generate the query, and call `lean-smt` only
    -- if the query is satisfiable and we want to print a model,
    -- UNLESS the `veil.smt.translator` option overrides this behaviour.
    let translatorToUse := veil.smt.translator.get opts
    let cmdString ←
      match translatorToUse with
      | .leanAuto => Veil.SMT.prepareLeanAutoQuery mv (← Veil.SMT.parseAutoHints ⟨stx[1]⟩)
      | .leanSmt => Veil.SMT.prepareLeanSmtQuery mv (← Smt.Tactic.parseHints ⟨stx[1]⟩)
    let getModel? := translatorToUse == .leanSmt
    let res ← Veil.SMT.querySolver cmdString withTimeout (getModel? := getModel?) (retryOnUnknown := true)
    match res with
    -- if we have a user-readable model, we can print it
    | .Sat _ (.some fostruct) => throwError s!"{satGoalStr}: {fostruct}"
    | .Sat (.some model) none => throwError s!"{satGoalStr}\n{model}"
    | .Sat none none => throwError s!"{satGoalStr}"
    | .Unknown reason => throwError "{unknownGoalStr}: {reason}"
    | .Failure reason => throwError "{failureGoalStr}: {reason}"
    | .Unsat => mv.admit (synthetic := false)


open Lean.Meta in
/-- UNSAFE: Switches the goal with its negation!
    This is unsound unless we use `admit_if_satisfiable` on the resulting goal! -/
elab "negate_goal" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← getMainTarget
  let negatedGoalType ← mkAppM `Not #[goalType]
  let negatedGoal ← mkFreshExprMVar $ negatedGoalType
  goal.admit (synthetic := false)
  setGoals [negatedGoal.mvarId!]

syntax (name := admit_if_satisfiable) "admit_if_satisfiable" Smt.Tactic.smtHints Smt.Tactic.smtTimeout : tactic

open Lean.Meta in
/-- UNSAFE: admits the goal if it is satisfiable.
    This is unsound unless we use `negate_goal` on the goal first!
    MOREOVER, we need to pass in all the hypotheses in the context.
-/
@[tactic admit_if_satisfiable] def evalAdmitIfSat : Tactic := fun stx => withMainContext do
  let mv ← Tactic.getMainGoal
  let hs ← Smt.Tactic.parseHints ⟨stx[1]⟩
  let withTimeout ← parseTimeout ⟨stx[2]⟩
  let cmdString ← Veil.SMT.prepareLeanSmtQuery mv hs
  let res ← Veil.SMT.querySolver cmdString withTimeout (retryOnUnknown := true)
  match res with
  | .Sat _ _ =>
    trace[veil.smt.result] "The negation of the goal is satisfiable, hence the goal is valid."
    mv.admit (synthetic := false)
  | .Unsat => throwError "the goal is false"
  | .Unknown reason => throwError "the solver returned unknown: {reason}"
  | .Failure reason => throwError "solver invocation failed: {reason}"

end Veil.SMT
