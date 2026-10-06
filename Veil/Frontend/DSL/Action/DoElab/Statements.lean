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

/-- Keep a plain-expression RHS of `let x ← rhs` under the enclosing
statement's state opening.

For example, suppose `bound` is a mutable state field and the statement is
`let i ← pick { n : Nat // n < bound }`. Without the internal RHS wrapper:

1. `elabVeilLetArrow` opens the state, introducing `state₁ ← get` and field
   bindings. Call the logical view of `state₁`'s `bound` field `bound₁`; the
   source name `bound` resolves to this binding.
2. Lean's `elabDoIdDecl` creates a type metavariable `?T` for `i` before
   elaborating the RHS. Its creation context contains `state₁` and `bound₁`,
   but does not contain the `state₂` and `bound₂` introduced next.
3. The RHS is elaborated as a separate `doExpr`, entering `elabVeilExpr`.
   This opens the state again, introducing `state₂ ← get` and a new field
   view `bound₂` that shadows the source name `bound`.
4. The RHS now picks a value of type `{ n : Nat // n < bound₂ }`. Inferring
   `i`'s type requires `?T := { n : Nat // n < bound₂ }`, but `bound₂` is
   absent from `?T`'s creation context, so this assignment is invalid.
   Unfolding the field aliases still leaves a reference to `state₂`, which
   is absent too. Renaming the shadowing bindings cannot fix this scope escape.

Wrapping the RHS in `veil_do_internal_expr%` sends it directly to Lean's
`elabDoExpr`, skipping step 3's second opening. The subtype then uses `bound₁`,
so `?T := { n : Nat // n < bound₁ }` only refers to locals already present
when `?T` was created. Other RHS forms retain their normal handlers.
Nested actions `(← …)` that Lean lifts out of the statement run before its
handler's state opening, so that opening already reflects their effects. -/
private def rhsUnderStatementOpening (ctx : Context) (stx : DoElem) : DoElabM DoElem := do
  -- NOTE: It would also be possible to write the following through
  -- indices of `stx` and `decl` (e.g., let `decl` being `stx[3]`),
  -- but using the concrete syntax matching should be more readable and maintainable.
  let `(doLetArrow| let%$tk $[mut%$mutTk?]? $cfg:letConfig $decl) := stx | return stx
  match decl with
  | `(doIdDecl| $x:ident $[: $ty?]? ← $rhs) =>
    let some rhs ← internalIfPlainTerm? ctx rhs | return stx
    let decl ← `(doIdDecl| $x:ident $[: $ty?]? ← $rhs)
    `(doElem| let%$tk $[mut%$mutTk?]? $cfg:letConfig $decl:doIdDecl)
  | `(doPatDecl| $pat:term $[: $ty?]? ← $rhs $[| $otherwise? $(rest?)?]?) =>
    let some rhs ← internalIfPlainTerm? ctx rhs | return stx
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
