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
  `action`. We elaborate it generic in the mode as `act.do` (see
  `Semantics/Definitions.lean`), and then, based on `act.do`, define:
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

def elabProcedureDoNotation (vs : Array Expr) (act : Ident) (br : Option (TSyntax ``Lean.explicitBinders)) (l : doSeq) : TermElabM (Name × Array Parameter × Expr) := do
  let originalName := act.getId
  let name := toDoName originalName
  let brs ← Option.stxArrMapM br toFunBinderArray
  let stx ← `(fun $brs* => veil_do $act in $environmentTheory, $environmentState in $l)
  try
    Meta.withLocalDecl veilModeVar.getId BinderInfo.default (mkConst ``Mode) fun mode => do
    /- We want to throw an error if anything fails or is missing during elaboration. -/
    withoutErrToSorry $ do
    let (mvars, e) ← elabTermDecidable stx
    let e ← Meta.mkLambdaFVarsImplicit (#[mode] ++ vs ++ mvars) e (binderInfoForMVars := BinderInfo.instImplicit) >>= instantiateMVars
    return (name, ← mvars.mapM (mvarToParam originalName), e)
  catch ex =>
    throwError "Error in action {name}: {← ex.toMessageData.toString}"
where
  mvarToParam (inAction : Name) (mvar : Expr) : TermElabM Parameter := do
    let mvarTypeStx ← delabVeilExpr (← Meta.inferType mvar)
    return { kind := .definitionTypeclass inAction, name := Name.anonymous, «type» := mvarTypeStx, userSyntax := .missing }

def elabProcedureInMode (act : Ident) (mode : Mode) : TermElabM (Name × Expr) := do
  let originalName := act.getId
  let toDoName := toDoName originalName
  let name := toActName originalName mode
  let mut body := mkAppN (mkConst toDoName) #[mode.expr]
  if mode == Mode.external then
    body ← Meta.forallTelescope (← Meta.inferType body) fun ks _ => do
      Meta.mkLambdaFVars ks $ ← Meta.mkAppM' (mkConst ``VeilM.returnUnit) #[(mkAppN body ks)]
  body ← body.unfold #[toDoName]
  body ← body.dsimp #[`doSimp]
  return (name, body)

def Module.registerProcedureSpecification [Monad m] [MonadError m] (mod : Module) (ps : ProcedureSpecification) : m Module := do
  mod.throwIfAlreadyDeclared ps.name
  return { mod with procedures := mod.procedures.push ps }

/- The implementation of this method _could_ be split into two distinct
parts (i.e. registering the action, then elaboration the definitions),
but that would eliminate opportunities for async elaboration. -/
def elabAction (mod : Module) (act : Ident) (br : Option (TSyntax ``Lean.explicitBinders)) (spec : Option doSeq) (l : doSeq) : CommandElabM Module := do
  let mut mod := mod
  -- Obtain `extraParams` so we can register the action
  let (nmDo, extraParams, e) ← liftTermElabMWithBinders (← mod.actionBinders act.getId) $ fun vs => elabProcedureDoNotation vs act br l
  let ps := ProcedureSpecification.mk (ProcedureInfo.action act.getId) br extraParams spec l
  mod ← mod.registerProcedureSpecification ps
  -- Elaborate the definition in the Lean environment
  liftTermElabM $ do
    addVeilDefinition nmDo e (attr := #[{name := `reducible}])
    let (nmExt, eExt) ← elabProcedureInMode act Mode.external
    let (nmInt, eInt) ← elabProcedureInMode act Mode.internal
    addVeilDefinitionAsync nmInt eInt
    addVeilDefinitionAsync nmExt eExt
   -- Make the definitions realizable / available for use
    let mut definitions := #[nmExt, nmInt]
    for d in definitions do
      enableRealizationsForConst d
  return mod


end Veil
