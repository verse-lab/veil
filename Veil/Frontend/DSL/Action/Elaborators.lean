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

def elabProcedureDoNotation (vs : Array Expr) (act : Name) (br : Option (TSyntax ``Lean.explicitBinders)) (l : doSeq) : TermElabM (Name × Array Parameter × Expr) := do
  let originalName := act
  let name := toDoName originalName
  let brs ← Option.stxArrMapM br toFunBinderArray
  let stx ← `(fun $brs* => veil_do $(mkIdent act) in $environmentTheory, $environmentState in $l)
  try
    Meta.withLocalDecl veilModeVar.getId BinderInfo.default (mkConst ``Mode) fun mode => do
    /- We want to throw an error if anything fails or is missing during elaboration. -/
    withoutErrToSorry $ do
    let (mvars, e) ← elabTermDecidable stx
    let e ← Meta.mkLambdaFVarsImplicit (#[mode] ++ vs ++ mvars) e (binderInfoForMVars := BinderInfo.instImplicit) >>= instantiateMVars
    return (name, ← mvars.mapIdxM (fun i mvar => mvarToParam originalName mvar i), e)
  catch ex =>
    throwError "Error in action {name}: {← ex.toMessageData.toString}"
where
  mvarToParam (inAction : Name) (mvar : Expr) (i : Nat) : TermElabM Parameter := do
    let mvarTypeStx ← delabVeilExpr (← Meta.inferType mvar)
    return { kind := .definitionTypeclass inAction, name := Name.mkSimple s!"{inAction}_dec_{i}", «type» := mvarTypeStx, userSyntax := .missing }

def elabProcedureInMode (act : Name) (mode : Mode) : TermElabM (Name × Expr) := do
  let originalName := act
  let toDoName ← resolveGlobalConstNoOverload $ mkIdent $ toDoName originalName
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
  return { mod with procedures := mod.procedures.push ps, _declarations := mod._declarations.insert ps.name (.procedure ps.info) }

/- The implementation of this method _could_ be split into two distinct
parts (i.e. registering the action, then elaboration the definitions),
but that would eliminate opportunities for async elaboration. -/
def Module.defineProcedure (mod : Module) (pi : ProcedureInfo) (br : Option (TSyntax ``Lean.explicitBinders)) (spec : Option doSeq) (l : doSeq) (stx : Syntax) : CommandElabM Module := do
  let mut mod := mod
  -- Obtain `extraParams` so we can register the action
  let (nmDo, extraParams, e) ← liftTermElabMWithBinders (← mod.actionBinders pi.name) $ fun vs => elabProcedureDoNotation vs pi.name br l
  let ps := ProcedureSpecification.mk pi br extraParams spec l stx
  mod ← mod.registerProcedureSpecification ps
  -- Elaborate the definition in the Lean environment
  liftTermElabM $ do
    _ ← addVeilDefinition nmDo e (attr := #[{name := `reducible}])
    let mut (nmExt, eExt) ← elabProcedureInMode pi.name Mode.external
    let mut (nmInt, eInt) ← elabProcedureInMode pi.name Mode.internal
    nmInt ← addVeilDefinitionAsync nmInt eInt
    nmExt ← addVeilDefinitionAsync nmExt eExt
   -- Make the definitions realizable / available for use
    let mut definitions := #[nmExt, nmInt]
    for d in definitions do
      enableRealizationsForConst d
  return mod

end Veil
