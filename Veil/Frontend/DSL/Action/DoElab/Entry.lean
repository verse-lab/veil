import Veil.Frontend.DSL.Action.DoElab.Assign
import Veil.Frontend.DSL.Action.DoElab.Statements

open Lean Elab Term Meta Lean.Parser
open Lean.Elab.Do

/-! ## Pre-elaboration validation -/

namespace Veil
namespace Action.DoElab

open Lean.Parser.Term

private def assignmentTarget? (stx : Syntax) : Option Term :=
  let elem : DoElem := ⟨stx⟩
  match elem with
  | `(doElem| $target:term $[: $_]? := $_) => some target
  | `(doReassignArrow| $target:term $[: $_]? ← $_ $[| $_ $[$_]?]?) => some target
  | `(doElem| $target:term := *) => some target
  | _ => none

private def nestedActionInAssignmentTarget? (stx : Syntax) : Option Syntax := do
  let target ← assignmentTarget? stx
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
  let expectedTypeStx ←
    `(term| $(mkIdent ``VeilM) $veilModeVar $readerType $stateType _)
  let expectedType ← Term.elabType expectedTypeStx
  let .app monad _ := expectedType.consumeMData
    | throwErrorAt body "internal error: Veil action type is not a monad application"
  let body ← prependDoItem (← `(Term.doSeqItem| veil_do_open_theory%)) body
  withVeilDoContext { mod := mod, proc := procName, monad, parameters := parameters.ids } do
    withOptions (fun opts => opts.setBool `backward.do.legacy false) do
      Lean.Elab.Do.elabDoWith .default body (some expectedType)

end Action.DoElab

elab (name := VeilDo) "veil_do" name:ident "in" readerType:term ","
    stateType:term "in" body:doSeq : term =>
  Action.DoElab.elabVeilDo name.getId readerType stateType body

end Veil
