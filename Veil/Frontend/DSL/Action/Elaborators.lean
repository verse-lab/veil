import Lean
import Veil.Frontend.DSL.Action.Syntax
import Veil.Frontend.DSL.Action.DoNotation
import Veil.Frontend.DSL.Util
import Veil.Util.Meta

open Lean Elab Command Term

/-! # Elaborators for Veil actions

  This file contains the elaborators for Veil actions. Every `action`
  declaration in a Veil `module` elaborates into a plethora of
  inter-related Lean definitions. For an action named `act`:

  1. First of all, we have to elaborate the `veil_do` notation of the
  `action` in _both_ the `internal` and `external` modes (see
  `Semantics/Definitions.lean`), i.e. with different treatment of
  `require` statements. This gives us two definitions:
    - `act` — the `internal` mode of the action, which is what gets
    called by other actions; this has a return value
    - `act.ext` - the `external` mode of the action; always returning
    `Unit` (the environment does not care about the return value)

  2. Then, from `act.ext`, we derive `act.succeedsWhenIgnoring` which
  is parameterised by a set of exceptions IDs `ExId → Prop` which we
  DON'T care about (assertion failures are treated as exceptions, and
  each assertion has its unique ID).
-/

namespace Veil

def elabProcedureDoNotation (vs : Array Expr) (act : Ident) (br : Option (TSyntax ``Lean.explicitBinders)) (mode : Mode) (l : doSeq) : TermElabM Name := do
  let name := toActName act.getId mode
  let brs ← Option.stxArrMapM br toFunBinderArray
  let stx ← `(fun $brs* => veil_do $act in $(← mode.stx) in $environmentTheory, $environmentState in $l)
  try
    /- We want to throw an error if anything fails or is missing during elaboration. -/
    withoutErrToSorry $ do
    let (mvars, e) ← elabTermDecidable stx
    let e ← Meta.mkLambdaFVarsImplicit (vs ++ mvars) e (binderInfoForMVars := BinderInfo.instImplicit) >>= instantiateMVars
    match mode with
    | Mode.internal => addVeilDefinition name e
    | _ => throwError "Cannot add a definition for an external action"
  catch ex =>
    throwError "Error in action {name}: {← ex.toMessageData.toString}"
  return name

def elabAction (act : Ident) (br : Option (TSyntax ``Lean.explicitBinders)) (spec : Option doSeq) (l : doSeq) : CommandElabM Unit := do
  let mod ← getCurrentModule (errMsg := "You cannot elaborate an action outside of a Veil module!")
  let _ ← liftTermElabMWithBinders (← mod.actionBinders act.getId) $ fun vs => elabProcedureDoNotation vs act br Mode.internal l
  return ()


end Veil
