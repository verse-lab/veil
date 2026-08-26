import Veil.Frontend.DSL.Action.DoElab.Assign
import Veil.Frontend.DSL.Action.DoElab.Statements

open Lean Elab Term Meta Lean.Parser
open Lean.Elab.Do

/-! ## Pre-elaboration validation -/

namespace Veil
namespace Action.DoElab

open Lean.Parser.Term

private def nestedActionInAssignmentTarget? (stx : Syntax) : Option Syntax := do
  let target ← assignmentLhs? ⟨stx⟩
  findOutsideQuotations? target.raw fun targetPart =>
    if targetPart.isOfKind ``Lean.Parser.Term.nestedAction then
      some targetPart
    else
      none

/-- Find an assignment whose target tries to execute a nested action, and
return that nested action so the diagnostic points at the effect itself. -/
private def findEffectfulAssignmentTarget? (stx : Syntax) : Option Syntax :=
  findOutsideQuotations? stx nestedActionInAssignmentTarget?

private def findKindOutsideQuotations? (stx : Syntax) (kind : SyntaxNodeKind) : Option Syntax :=
  findOutsideQuotations? stx fun candidate =>
    if candidate.isOfKind kind then some candidate else none

/-- Every `doElem` kind the Veil action elaborator classifies: kinds with
Veil `@[doElem_elab]` handlers (including the targeted rejections in
`Statements.lean`), Veil's own statement syntax (whether elaborated or
macro-expanded), and Lean kinds that re-dispatch into classified ones
(`doUnless` elaborates through `doIf`). `validateStatementKinds` errors on
anything else, so a new statement kind must be classified here before it can
appear in an action. -/
private def classifiedDoElemKinds : NameSet := .ofList [
  -- Lean statements with Veil handlers
  ``Lean.Parser.Term.doReassign, ``Lean.Parser.Term.doReassignArrow,
  ``Lean.Parser.Term.doLet, ``Lean.Parser.Term.doHave,
  ``Lean.Parser.Term.doLetArrow, ``Lean.Parser.Term.doLetElse,
  ``Lean.Parser.Term.doIf, ``Lean.Parser.Term.doUnless,
  ``Lean.Parser.Term.doMatch, ``Lean.Parser.Term.doExpr,
  ``Lean.Parser.Term.doNested, ``Lean.Parser.Term.doReturn,
  ``Lean.Parser.Term.doDbgTrace,
  -- inserted by Lean's own doElem macro expansion (e.g. `if` without `else`)
  ``Lean.Parser.Term.InternalSyntax.doSkip,
  -- Veil's own statements
  ``requireDo, ``assertDo, ``ifSomeDo, ``letPick, ``havocAssignment,
  ``veilLetDo, ``veilVarDo, ``stateAssignWrapper, ``internalExpr,
  ``theoryOpen,
  -- rejected with targeted diagnostics
  ``Lean.Parser.Term.doLetRec, ``Lean.Parser.Term.doFor,
  ``Lean.Parser.Term.doWhile, ``Lean.Parser.Term.doRepeat,
  ``Lean.Parser.Term.doTry, ``Lean.Parser.Term.doBreak,
  ``Lean.Parser.Term.doContinue, ``Lean.Parser.Term.doMatchExpr,
  ``Lean.Parser.Term.doAssert, ``Lean.Parser.Term.doDebugAssert,
  ``Lean.Parser.Term.doIdbg, ``Lean.Parser.Term.doForward]

/-- Completeness guard, run on the post-macro-expansion action body: every
statement (including those in nested branch sequences) must be a `doElem`
kind Veil classifies. An unclassified kind — new upstream syntax, or a
library-registered `doElem` — would elaborate through Lean's builtin
handlers *without* the per-statement state opening, a silent stale-state
hazard; make it a loud error instead. Boundaries whose contents Lean
elaborates in another monad (`by` blocks), or treats as data (quotations),
are skipped; term-level `do` is rejected separately by `validateVeilDo`. -/
private partial def validateStatementKinds (stx : Syntax)
    (inQuotation := false) : TermElabM Unit := do
  if stx.isOfKind ``Lean.Parser.Term.byTactic ||
      stx.isOfKind ``Lean.Parser.Term.do then
    return
  if !inQuotation && stx.isOfKind ``Lean.Parser.Term.doSeqItem then
    let elem := stx[0]
    unless classifiedDoElemKinds.contains elem.getKind do
      throwErrorAt elem
        m!"statements of kind `{elem.getKind}` are not supported in Veil actions"
  let childQuoted := Action.childrenAreQuoted stx inQuotation
  for child in stx.getArgs do
    validateStatementKinds child childQuoted

/-- Structural checks which must run before Lean lifts nested actions. This is
applied both to the user's surface syntax and to the syntax obtained after
`prepareStateAssignments` expands `doElem` macros. -/
def validateVeilDo (body : ActionSyntax) : TermElabM Unit := do
  if let some termDo := findKindOutsideQuotations? body.raw ``Lean.Parser.Term.do then
    throwErrorAt termDo
      "term-level `do` blocks cannot be stored, passed, or otherwise deferred inside Veil actions; execute the block directly as a statement or bind its result"

  /- `while` macro-expands to `repeat` before the statement handlers run, so
  the `rejectUnsupported` handler would report a misleading `repeat`
  diagnostic; catch it here, before macro expansion. -/
  if let some stx := findKindOutsideQuotations? body.raw ``Lean.Parser.Term.doWhile then
    throwErrorAt stx "`while` loops are not supported in Veil actions"

  if let some stx := findKindOutsideQuotations? body.raw ``Lean.Parser.Term.doForward then
    throwErrorAt stx "effect forwarding (`do←`) is not supported in Veil actions"

  if let some nestedAction := findEffectfulAssignmentTarget? body.raw then
    throwErrorAt nestedAction "effects are not supported in state-update target indices"


/-! ## The `veil_do` entry point -/

/-- The user-visible bindings in scope at the `veil_do` entry point: the
action's declared parameters (e.g. `x` and `y` in
`action foo (x : Nat) (y : Bool)`), plus any surrounding module-level
binders. Only names that collide with a signature component matter — they
trigger the shadow warning below and refine assignment diagnostics. -/
private structure Parameters where
  ids : FVarIdSet := {}
  names : NameSet := {}

private def currentParameters : TermElabM Parameters :=
  foldUserLocals {} fun result decl =>
    { ids := result.ids.insert decl.fvarId, names := result.names.insert decl.userName }

/-- Warn if parameters shadow state components. -/
private def warnParameterShadows (mod : Module) (body : ActionSyntax)
    (parameters : Parameters) : TermElabM Unit :=
  mod.signature.filter (parameters.names.contains ·.name) |>.forM fun field => do
    let kind := if field.isMutable then "mutable state" else "immutable theory"
    logWarningAt body m!"parameter `{field.name}` shadows {kind} component `{field.name}`; references to this name resolve to the parameter"

def elabVeilDo (procName : Name) (readerType stateType : Term)
    (body : ActionSyntax) : TermElabM Expr := do
  let mod ← getCurrentModule
    (errMsg := "You cannot use Veil action notation outside a Veil module")
  validateVeilDo body
  let parameters ← currentParameters
  warnParameterShadows mod body parameters
  let body : ActionSyntax := ⟨← prepareStateAssignments body.raw⟩
  /- `prepareStateAssignments` recursively expands `doElem` macros.  Validate
  the syntax that will actually reach Lean's nested-action lifting as well as
  the original surface syntax above, so a macro cannot introduce a forbidden
  term-level `do`, `do←`, or effectful assignment target. -/
  validateVeilDo body
  validateStatementKinds body.raw
  let expectedTypeStx ←
    `(term| $(mkIdent ``VeilM) $veilModeVar $readerType $stateType _)
  let expectedType ← Term.elabType expectedTypeStx
  let .app monad _ := expectedType.consumeMData
    | throwErrorAt body "internal error: Veil action type is not a monad application"
  let some body ← prependDoSeqItem? (← `(Term.doSeqItem| veil_do_open_theory%)) body
    | throwErrorAt body "unexpected Veil action body"
  withVeilDoContext { mod := mod, proc := procName, monad, parameters := parameters.ids } do
    withOptions (fun opts => opts.setBool `backward.do.legacy false) do
      Lean.Elab.Do.elabDoWith .default body (some expectedType)

end Action.DoElab

elab (name := VeilDo) "veil_do" name:ident "in" readerType:term ","
    stateType:term "in" body:doSeq : term =>
  Action.DoElab.elabVeilDo name.getId readerType stateType body

end Veil
