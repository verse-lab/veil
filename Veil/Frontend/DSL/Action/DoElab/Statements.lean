module

public meta import Veil.Frontend.DSL.Action.DoElab.Context
public meta import Veil.Frontend.DSL.Action.Syntax
public meta import Lean.Elab.Idbg

public meta section

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

private def warnComponentShadow (ctx : Context) (id : Ident) : DoElabM Unit := do
  if ← isUserShadowed id.getId then return
  let some field := ctx.mod.signature.find? (·.name == id.getId) | return
  let kind := if field.isMutable then "mutable state" else "immutable theory"
  logWarningAt id m!"local `{id.getId}` shadows {kind} component `{id.getId}`; references to this name resolve to the local"

/- NOTE: `dec.ensureUnitAt stx` checks that the rest of the block expects no value from this
statement, and reports a type mismatch otherwise. Few handlers call it. Inside a block, the
continuation of every statement but the last already expects `PUnit`, so the check can fail only
for the last statement of a block or branch. Lean's handlers for statements (`let`, `have`,
`let x ← e`, `for`, …) make the check themselves, so the Veil handlers that delegate to them need
not. An expression statement **must not make it**, since its value may be the result of the block;
`elabDoExpr` elaborates it against the type the rest of the block expects instead.

A statement that binds a variable produces no value either: `do let x ← e; rest` elaborates to
`e >>= fun x => rest`, so the value of `e` goes to `x` and nothing is left for the statement.
Lean's handler for `let x ← e` (`elabDoArrow` in `Lean/Elab/BuiltinDo/Let.lean`)
accordingly has two continuations: the one `elabDoIdDecl` builds, whose result is `x`, and the
statement's own `dec`, which it checks with `ensureUnitAt` and then continues with
`continueWithUnit`, that is, with `()`.

A `require` or `assert` produces no value, and both branches below elaborate the statement
themselves. The first hands the generated `VeilM.require p 0` to `elabDoExpr` as an expression
statement, and there the check is for the error message: without it, a `require` ending a branch
that returns a value would still be rejected, but as a type mismatch of that generated term rather
than of the statement. The second is a binding statement like `let x ← e`, with the proof bound to
`h`, and is elaborated the same way. `continueWithUnit` makes the check as well, so there the
explicit check only comes before the right-hand side is elaborated. -/

private def elabAssertionStatement (operation : Name) (stx : DoElem) (proof? : Option Ident)
    (proposition : Term) (dec : DoElemCont) : DoElabM Expr := do
  let ctx ← requireVeilDoBlock
  proof?.forM (warnComponentShadow ctx)
  openStateAround ctx.mod do
    let assertionId ← mkNewAssertion ctx.proc stx
    let term ← `($(mkIdent operation) $proposition $(Syntax.mkNatLit assertionId.toNat))
    match proof? with
    | none =>
      let elem ← `(doElem| $term:term)
      Lean.Elab.Do.elabDoExpr elem (← dec.ensureUnitAt stx)
    | some h =>
      /- NOTE: `require h : p` or `assert h : p` cannot be a macro like `assume h : p`, since the assertion ID needs to be
      allocated here. Also, this statement's state opening is already in place, so the result is
      bound directly and `h` is added as a `have`; a pattern `let ⟨_, h⟩ ← …` would pass its
      destructuring `let` to Veil's `let` handler, which would open the state a second time. -/
      let dec ← dec.ensureUnitAt stx
      bindInternalResult stx `holds term fun holds => do
        let proof ← Term.elabTerm (← `($(mkIdent holds).property)) none
        let prop := (← instantiateMVars (← inferType proof)).headBeta
        mapLetDecl h.getId prop proof (nondep := true) fun hFVar => do
          Term.addLocalVarInfo h hFVar
          dec.continueWithUnit

@[doElem_elab requireDo, doElem_elab assertDo]
def elabAssertion : DoElab := fun stx dec => do
  match stx with
  | `(doElem| require $[$h?:ident :]? $p:term) =>
    let operation := if h?.isSome then ``VeilM.requireSubtype else ``VeilM.require
    elabAssertionStatement operation stx h? p dec
  | `(doElem| assert $[$h?:ident :]? $p:term) =>
    let operation := if h?.isSome then ``VeilM.assertSubtype else ``VeilM.assert
    elabAssertionStatement operation stx h? p dec
  | _ => throwUnsupportedSyntax


/-! ## Ordinary Lean statements: delegation and rejection -/

/-- The identifiers a binding statement introduces. Unrecognized shapes
return `#[]` rather than throwing: an exception here would drop the whole
Veil handler — including the state opening — not just the shadow warning. -/
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
    | _ => return #[]
  | `(doLetElse| let $[mut%$_]? $_:letConfig $pattern:term := $_ | $_ $(_)? ) =>
    getPatternVarsEx pattern
  | `(doIf| if $h:ident : $_ then $_ $[else $_]?) => return #[h]
  | `(doMatch| match $[(dependent := $_)]? $[(generalizing := $_)]? $(_)?
      $_,* with $alts:matchAlt*) =>
    Lean.Elab.Do.getAltsPatternVars alts
  | _ => return #[]

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

/-- In `let x ← rhs`, Lean elaborates the type of `x` under this statement's
state opening but elaborates `rhs` as a `do` element of its own. A plain
expression `rhs` would then go through `elabVeilExpr`, whose second opening
binds fresh field views that are out of scope of `x`'s type, so a type
mentioning mutable state (e.g. `let i ← pick { i // i ∈ s }`) could not be
assigned to `x`. Since Lean lifts nested actions `(← …)` out of the whole
statement before any handler runs, the statement's own opening is already
current for `rhs`: mark `rhs` internal so it is elaborated under that opening. -/
private def rhsUnderStatementOpening (ctx : Context) (stx : DoElem) : DoElabM DoElem := do
  let internal? (rhs : DoElem) : DoElabM (Option DoElem) := do
    let `(doElem| $e:term) := rhs | return none
    rejectDirectRecursion ctx rhs
    some <$> withRef rhs `(doElem| veil_do_internal_expr% $e)
  -- NOTE: It would also be possible to write the following through
  -- indices of `stx` and `decl` (e.g., let `decl` being `stx[3]`),
  -- but using the concrete syntax matching should be more readable and maintainable.
  let `(doLetArrow| let%$tk $[mut%$mutTk?]? $cfg:letConfig $decl) := stx | return stx
  match decl with
  | `(doIdDecl| $x:ident $[: $ty?]? ← $rhs) =>
    let some rhs ← internal? rhs | return stx
    let decl ← `(doIdDecl| $x:ident $[: $ty?]? ← $rhs)
    `(doElem| let%$tk $[mut%$mutTk?]? $cfg:letConfig $decl:doIdDecl)
  | `(doPatDecl| $pat:term $[: $ty?]? ← $rhs $[| $otherwise? $(rest?)?]?) =>
    let some rhs ← internal? rhs | return stx
    let decl ← `(doPatDecl| $pat:term $[: $ty?]? ← $rhs $[| $otherwise? $(rest?)?]?)
    `(doElem| let%$tk $[mut%$mutTk?]? $cfg:letConfig $decl:doPatDecl)
  | _ => return stx

@[doElem_elab Lean.Parser.Term.doLetArrow]
def elabVeilLetArrow : DoElab := fun stx dec => do
  -- This looks like `delegate`, but needs processing of `stx`
  let ctx ← requireVeilDoBlock
  warnShadowingBinders ctx stx
  let stx ← rhsUnderStatementOpening ctx stx
  openStateAround ctx.mod <| Lean.Elab.Do.elabDoLetArrow stx dec

@[doElem_elab Lean.Parser.Term.doLetElse]
def elabVeilLetElse : DoElab :=
  delegate Lean.Elab.Do.elabDoLetElse (before := warnShadowingBinders)

/-- The pre-port existential `if` was spelled `if x : p`, which now parses
as Lean's dependent `if`. The hypothesis binder is not in scope in its own
condition, so when the same name occurs there it refers to an outer binding
— either the legacy spelling (meaning changed silently) or a dependent `if`
whose hypothesis shadows a variable it constrains. Lint both. -/
private def warnLegacyExistentialIf (_ctx : Context) (stx : DoElem) : DoElabM Unit := do
  let `(doIf| if $h:ident : $c then $_ $[else $_]?) := stx | return
  let some occurrence := Action.findOutsideQuotations? c.raw fun s =>
      if s.isIdent && s.getId == h.getId then some s else none
    | return
  logWarningAt occurrence
    m!"Veil's existential `if` is now spelled `if {h.getId} :| p`; this `if {h.getId} : p` parses as Lean's dependent `if`, so the condition tests the existing binding of `{h.getId}` instead of introducing a witness; if the dependent `if` is intended, name the hypothesis differently from the variables in its condition"

@[doElem_elab Lean.Parser.Term.doIf]
def elabVeilIf : DoElab :=
  delegate Lean.Elab.Do.elabDoIf (before := fun ctx stx => do
    warnLegacyExistentialIf ctx stx
    warnShadowingBinders ctx stx)

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
