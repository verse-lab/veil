import Lean
import Veil.Frontend.DSL.Action.Syntax
import Veil.Frontend.DSL.Action.DoNotation
import Veil.Frontend.DSL.Module.Util
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

abbrev FullyQualifiedName := Name
/-- Get the fully qualified name of an _existing_ definition. -/
def getFullyQualifiedName [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] (name : Name) : m FullyQualifiedName := do
  resolveGlobalConstNoOverload (mkIdent name)

/-- If `mode?` is `none`, the name is the `.do`-definition of the action, i.e.
the one that is parametric in `mode`. -/
def ProcedureInfo.nameInMode (pi : ProcedureInfo) (mode? : Option Mode) : Name :=
  match mode? with
  | .none => toDoName pi.name
  | .some mode => toActName pi.name mode


/-! ## Auxiliary definitions-/
namespace AuxiliaryDefinitions
open Veil Veil.Simp

def Argument := Term
def SyntaxTemplate := Array Argument → TermElabM Term

/-- Template for defining the WP of an action. -/
private def wpTemplate (sourceAction : Name) : SyntaxTemplate :=
  let (handler, post) := (mkVeilImplementationDetailIdent `handler, mkVeilImplementationDetailIdent `post)
  (fun args : Array Term =>
    `(fun $handler $post => [IgnoreEx $handler| $(mkIdent ``wp) (@$(mkIdent sourceAction) $args*) $post]))

/-- This defines `act.do.wp`. Our aim is to reduce all `wp` goals related to
`act` to applications of this definition. The rationale is that we can apply
heavy-duty simplification to this definition _only_ and benefit from it in all
contexts. -/
private def defineWp (mod : Module) (nm : Name) (dk : DeclarationKind) : TermElabM Unit := do
  let fqn ← getFullyQualifiedName nm
  let (allBinders, allArgs) ← mod.declarationAllBindersArgs nm dk
  let defterm ← (wpTemplate fqn) allArgs
  trace[veil.debug] "{nm}\n{defterm}"
  let res ← elabBinders allBinders $ fun _vs => (do
    let e ← withoutErrToSorry <| elabTermAndSynthesize defterm none
    trace[veil.debug] "{nm}\n{e}"
    -- FIXME: `quantifierSimp` will not push quantifiers all the way here. Making
    -- `quantifierSimp` work over the `.do` definition would be great, but it likely
    -- requires writing a simproc to push over `require` and `ensure`
    -- FIXME: why aren't the state lemmas applying correctly?
    -- it's probably due to us not setting up typeclass instances properly
    let cfg := { unfoldPartialApp := true }
    let simp := (Simp.unfold #[fqn]) |>.andThen (Simp.simp #[`wpSimp] cfg) |>.andThen (Simp.simp #[`quantifierSimp])
    let res ← simp e
    trace[veil.debug] "{nm}\n{e}\n~>\n{res.expr}"
    let e' ← Meta.mkLambdaFVars _vs res.expr
    trace[veil.debug] "{← delabVeilExpr e'}"
    pure res)
  return

private def define (mod : Module) (nmDo : Name) (dk : DeclarationKind) : TermElabM Unit := do
  defineWp mod nmDo dk

end AuxiliaryDefinitions

/-! ## Procedure elaboration -/

def elabProcedureDoNotation (vs : Array Expr) (pi : ProcedureInfo) (br : Option (TSyntax ``Lean.explicitBinders)) (l : doSeq) : TermElabM (Name × Array Parameter × Expr) := do
  let brs ← Option.stxArrMapM br toFunBinderArray
  let stx ← `(fun $brs* => veil_do $(mkIdent pi.name) in $environmentTheory, $environmentState in $l)
  try
    Meta.withLocalDecl veilModeVar.getId BinderInfo.default (mkConst ``Mode) fun mode => do
    /- We want to throw an error if anything fails or is missing during elaboration. -/
    withoutErrToSorry $ do
    let (mvars, e) ← elabTermDecidable stx
    let e ← Meta.mkLambdaFVarsImplicit (#[mode] ++ vs ++ mvars) e (binderInfoForMVars := BinderInfo.instImplicit) >>= instantiateMVars
    let res ← (Simp.dsimp #[]) e
    return ((pi.nameInMode .none), ← mvars.mapIdxM (fun i mvar => mvarToParam pi.name mvar i), res.expr)
  catch ex =>
    throwError "Error in action {pi.name}: {← ex.toMessageData.toString}"
where
  mvarToParam (inAction : Name) (mvar : Expr) (i : Nat) : TermElabM Parameter := do
    let mvarTypeStx ← delabVeilExpr (← Meta.inferType mvar)
    return { kind := .definitionTypeclass inAction, name := Name.mkSimple s!"{inAction}_dec_{i}", «type» := mvarTypeStx, userSyntax := .missing }

def elabProcedureInMode (pi : ProcedureInfo) (mode : Mode) : TermElabM (Name × Expr) := do
  let doNm_fullyQualified ← getFullyQualifiedName $ (pi.nameInMode .none)
  let mut body := mkAppN (mkConst doNm_fullyQualified) #[mode.expr]
  /- The external mode of an action always returns `Unit`. -/
  if mode == Mode.external then
    body ← Meta.forallTelescope (← Meta.inferType body) fun ks _ => do
      Meta.mkLambdaFVars ks $ ← Meta.mkAppM' (mkConst ``VeilM.returnUnit) #[(mkAppN body ks)]
  let res ← (Simp.unfold #[doNm_fullyQualified]).andThen (Simp.dsimp #[]) body
  return (pi.nameInMode mode, res.expr)

def Module.registerProcedureSpecification [Monad m] [MonadError m] (mod : Module) (ps : ProcedureSpecification) : m Module := do
  mod.throwIfAlreadyDeclared ps.name
  return { mod with procedures := mod.procedures.push ps, _declarations := mod._declarations.insert ps.name (.procedure ps.info) }

private def Module.registerDerivedActionDefinition [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (base : ProcedureSpecification) (mode? : Option Mode) : m (Module × DeclarationKind) := do
  let derivedName := base.info.nameInMode mode?
  mod.throwIfAlreadyDeclared derivedName
  let derivedDefKind := match mode? with | .none => .actionDoLike | .some _ => .actionLike
  let declKind := .derivedDefinition derivedDefKind {base.name}
  let derivedDef : DerivedDefinition := { name := derivedName, kind := derivedDefKind, params := base.params, extraParams := base.extraParams, derivedFrom := {base.name}, stx := .none }
  let mod := { mod with _declarations := mod._declarations.insert derivedName declKind, _derivedDefinitions := mod._derivedDefinitions.insert derivedName derivedDef }
  return (mod, declKind)

/- The implementation of this method _could_ be split into two distinct
parts (i.e. registering the action, then elaboration the definitions),
but that would eliminate opportunities for async elaboration. -/
def Module.defineProcedure (mod : Module) (pi : ProcedureInfo) (br : Option (TSyntax ``Lean.explicitBinders)) (spec : Option doSeq) (l : doSeq) (stx : Syntax) : CommandElabM Module := do
  let mod := mod
  -- Obtain `extraParams` so we can register the action
  let actionBinders ← (← mod.declarationBaseParams (.procedure pi)).mapM (·.binder)
  let (nmDo, extraParams, e) ← liftTermElabMWithBinders actionBinders $ fun vs => elabProcedureDoNotation vs pi br l
  let ps := ProcedureSpecification.mk pi br extraParams spec l stx
  -- We register the `internal` view of the action as the "real" one
  let mod ← mod.registerProcedureSpecification ps
  -- The `.do` and `.ext` views are marked as derived definitions
  let (mod, doKind) ← mod.registerDerivedActionDefinition ps .none
  let intKind := ps.declarationKind
  let (mod, extKind) ← mod.registerDerivedActionDefinition ps Mode.external
  -- Elaborate the definitions in the Lean environment
  liftTermElabM $ do
    let _ ← addVeilDefinition nmDo e (attr := #[{name := `reducible}])
    -- defineAuxiliaryDeclarations pi Option.none br nmDo nmDoFull
    let (nmExt, eExt) ← elabProcedureInMode pi Mode.external
    let (nmInt, eInt) ← elabProcedureInMode pi Mode.internal
    let nmInt_fullyQualified ← addVeilDefinitionAsync nmInt eInt
    let nmExt_fullyQualified ← addVeilDefinitionAsync nmExt eExt
   -- Make the definitions realizable / available for use
    let mut definitions := #[nmExt_fullyQualified, nmInt_fullyQualified]
    for d in definitions do
      enableRealizationsForConst d
      Elab.Term.applyAttributes d #[{name := `actSimp}]
    -- TODO: do this asynchronously
    -- AuxiliaryDefinitions.define mod nmDo doKind
    AuxiliaryDefinitions.define mod nmExt extKind
    -- defineAuxiliaryDeclarations pi (Option.some .internal) br nmInt nmIntFull
    -- defineAuxiliaryDeclarations pi (Option.some .external) br nmExt nmExtFull
  return mod

end Veil
