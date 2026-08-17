import Veil.Frontend.DSL.Action.DoElab.Context
import Veil.Frontend.DSL.Action.Syntax
import Lean.Elab.Idbg

open Lean Elab Term Meta Lean.Parser
open Lean.Elab.Do
open Lean.Parser.Term

/-! ## Veil-specific statements -/

namespace Veil
namespace Action.DoElab

/- The existential `if x :| p` is a pure macro over `doIf` and `let x :| p`
(see `Action/Syntax.lean`); it needs no handler here. -/

@[doElem_control_info requireDo, doElem_control_info assertDo]
def assertionControlInfo : ControlInfoHandler := fun _ =>
  return ControlInfo.pure

private def elabAssertionStatement (operation : Name) (stx : DoElem)
    (proposition : Term) (dec : DoElemCont) : DoElabM Expr := do
  let ctx ← requireVeilDoBlock
  openStateAround ctx.mod do
    let assertionId ← mkNewAssertion ctx.proc stx
    let term ← `($(mkIdent operation) $proposition $(Syntax.mkNatLit assertionId.toNat))
    let elem ← `(doElem| $term:term)
    Lean.Elab.Do.elabDoExpr elem (← dec.ensureUnitAt stx)

@[doElem_elab requireDo, doElem_elab assertDo]
def elabAssertion : DoElab := fun stx dec => do
  match stx with
  | `(doElem| require $p:term) =>
    elabAssertionStatement ``VeilM.require stx p dec
  | `(doElem| assert $p:term) =>
    elabAssertionStatement ``VeilM.assert stx p dec
  | _ => throwUnsupportedSyntax


/-! ## Ordinary Lean statements: delegation and rejection -/


private def warnComponentShadow (ctx : Context) (id : Ident) : DoElabM Unit := do
  if ← isUserShadowed id.getId then return
  let some field := ctx.mod.signature.find? (·.name == id.getId) | return
  let kind := if field.isMutable then "mutable state" else "immutable theory"
  logWarningAt id m!"local `{id.getId}` shadows {kind} component `{id.getId}`; references to this name resolve to the local"

/-- The identifiers a binding statement introduces.  Statement shapes without
binders (e.g. a non-dependent `if`) bind nothing; unrecognized shapes of the
binding kinds make the Veil handler fall through to Lean's. -/
private def boundIdents (stx : DoElem) : DoElabM (Array Ident) := do
  match stx with
  | `(doElem| let%$_ $[mut%$_]? $_:letConfig $decl:letDecl)
  | `(doElem| have%$_ $_:letConfig $decl:letDecl) =>
    getLetDeclVars decl
  | `(doLetArrow| let%$_ $[mut%$_]? $_:letConfig $decl) =>
    match decl with
    | `(doIdDecl| $id:ident $[: $_]? ← $_) => return #[id]
    | `(doPatDecl| _%$_ $pattern:term $[: $_]? ← $_)
    | `(doPatDecl| $pattern:term $[: $_]? ← $_ $[| $_ $[$_]?]?) =>
      getPatternVarsEx pattern
    | _ => throwUnsupportedSyntax
  | `(doLetElse| let $[mut%$_]? $_:letConfig $pattern:term := $_ | $_ $(_)? ) =>
    getPatternVarsEx pattern
  | `(doIf| if $h:ident : $_ then $_ else $_) => return #[h]
  | `(doMatch| match $[(dependent := $_)]? $[(generalizing := $_)]? $(_)?
      $_,* with $alts:matchAlt*) =>
    Lean.Elab.Do.getAltsPatternVars alts
  | _ =>
    if stx.raw.isOfKind ``Lean.Parser.Term.doIf then return #[]
    throwUnsupportedSyntax

private def warnShadowingBinders (ctx : Context) (stx : DoElem) : DoElabM Unit := do
  (← boundIdents stx).forM (warnComponentShadow ctx)

private def delegate (builtin : DoElab)
    (before : Context → DoElem → DoElabM Unit := fun _ _ => pure ())
    (after : Context → Expr → DoElabM Expr := fun _ e => pure e) : DoElab := fun stx dec => do
  let ctx ← requireVeilDoBlock
  before ctx stx
  openStateAround ctx.mod do after ctx (← builtin stx dec)

private def doExprHeadName? (stx : DoElem) : Option Name :=
  match stx with
  | `(doExpr| $term:term) =>
    if term.raw.isIdent then
      some term.raw.getId
    else
      term.isApp?.map (fun (head, _) => head.getId)
  | _ => none

private def rejectDirectRecursion (ctx : Context) (stx : DoElem) : DoElabM Unit := do
  if doExprHeadName? stx == some ctx.proc &&
      (← findUserLocal? ctx.proc).isNone then
    throwErrorAt stx
      "recursive Veil action calls are not supported; action bodies must terminate structurally"

@[doElem_elab Lean.Parser.Term.doExpr]
def elabVeilExpr : DoElab :=
  delegate Lean.Elab.Do.elabDoExpr (before := rejectDirectRecursion)

@[doElem_elab Lean.Parser.Term.doNested]
def elabVeilNested : DoElab := delegate Lean.Elab.Do.elabDoNested

@[doElem_elab Lean.Parser.Term.doLet]
def elabVeilLet : DoElab :=
  delegate Lean.Elab.Do.elabDoLet (before := warnShadowingBinders)

@[doElem_elab Lean.Parser.Term.doHave]
def elabVeilHave : DoElab :=
  delegate Lean.Elab.Do.elabDoHave (before := warnShadowingBinders)

@[doElem_elab Lean.Parser.Term.doLetArrow]
def elabVeilLetArrow : DoElab :=
  delegate Lean.Elab.Do.elabDoLetArrow (before := warnShadowingBinders)

@[doElem_elab Lean.Parser.Term.doLetElse]
def elabVeilLetElse : DoElab :=
  delegate Lean.Elab.Do.elabDoLetElse (before := warnShadowingBinders)

@[doElem_elab Lean.Parser.Term.doIf]
def elabVeilIf : DoElab :=
  delegate Lean.Elab.Do.elabDoIf (before := warnShadowingBinders)

@[doElem_elab Lean.Parser.Term.doMatch]
def elabVeilMatch : DoElab := delegate Lean.Elab.Do.elabDoMatch
    (before := warnShadowingBinders)
    (after := fun ctx result => zetaFieldDerivedLets ctx.mod result)

@[doElem_elab Lean.Parser.Term.doReturn]
def elabVeilReturn : DoElab := delegate Lean.Elab.Do.elabDoReturn

@[doElem_elab Lean.Parser.Term.doDbgTrace]
def elabVeilDbgTrace : DoElab := delegate Lean.Elab.Do.elabDoDbgTrace

private def unsupportedMessage : SyntaxNodeKind → MessageData
  | ``Lean.Parser.Term.doLetRec => "recursive local declarations are not supported in Veil actions"
  | ``Lean.Parser.Term.doFor => "`for` loops are not supported in Veil actions"
  | ``Lean.Parser.Term.doWhile => "`while` loops are not supported in Veil actions"
  | ``Lean.Parser.Term.doRepeat => "`repeat` loops are not supported in Veil actions"
  | ``Lean.Parser.Term.doTry => "exceptions (`try`/`catch`/`finally`) are not supported in Veil actions"
  | ``Lean.Parser.Term.doBreak => "`break` is not supported in Veil actions"
  | ``Lean.Parser.Term.doContinue => "`continue` is not supported in Veil actions"
  | ``Lean.Parser.Term.doMatchExpr => "`match_expr` is not supported in Veil actions"
  | ``Lean.Parser.Term.doAssert => "Lean `assert!` is not supported in Veil actions; use Veil `assert`"
  | ``Lean.Parser.Term.doDebugAssert => "Lean `debug_assert!` is not supported in Veil actions; use Veil `assert`"
  | ``Lean.Parser.Term.doIdbg => "`idbg` is not supported in Veil actions"
  | kind => m!"`{kind}` is not supported in Veil actions"

@[doElem_elab Lean.Parser.Term.doLetRec, doElem_elab Lean.Parser.Term.doFor,
  doElem_elab Lean.Parser.Term.doWhile, doElem_elab Lean.Parser.Term.doRepeat,
  doElem_elab Lean.Parser.Term.doTry, doElem_elab Lean.Parser.Term.doBreak,
  doElem_elab Lean.Parser.Term.doContinue, doElem_elab Lean.Parser.Term.doMatchExpr,
  doElem_elab Lean.Parser.Term.doAssert, doElem_elab Lean.Parser.Term.doDebugAssert,
  doElem_elab Lean.Parser.Term.doIdbg]
def rejectUnsupported : DoElab := fun stx _ => do
  discard <| requireVeilDoBlock
  throwError (unsupportedMessage stx.raw.getKind)

end Action.DoElab
end Veil
