
import Lean
import Lean.Parser

open Lean Lean.Parser

namespace Veil

namespace Action

/-- Whether children of `stx` are quoted, accounting for antiquotations. -/
def childrenAreQuoted (stx : Syntax) (currentlyQuoted : Bool) : Bool :=
  (currentlyQuoted && !(stx.isAntiquot && !stx.isEscapedAntiquot)) || stx.isQuot

end Action

section VeilActionKeywords

declare_syntax_cat veilActionKeyword

scoped syntax (name := kw_require) "require" : veilActionKeyword
scoped syntax (name := kw_assume) "assume" : veilActionKeyword
scoped syntax (name := kw_assert) "assert" : veilActionKeyword
scoped syntax (name := kw_pick) "pick" : veilActionKeyword
scoped syntax (name := kw_veil_var) "veil_var" : veilActionKeyword
scoped syntax (name := kw_veil_let) "veil_let" : veilActionKeyword


/-- Precondition -/
scoped syntax (name := kw_requires) "requires" : veilActionKeyword

/-- Postcondition -/
scoped syntax (name := kw_ensures) "ensures" : veilActionKeyword

scoped syntax (name := kw_with) "with" : veilActionKeyword
scoped syntax (name := kw_unchanged) "unchanged" : veilActionKeyword
scoped syntax (name := kw_unchanged_fields) "unchanged_fields" : veilActionKeyword

end VeilActionKeywords

/-- `assume P` ignores executions that do not satisfy `P`. BE CAREFUL
when making assumptions, as inconsistent assumptions will eliminate ALL
executions, making your specification vacuous. -/
syntax (name := assumeStatement) kw_assume term : term

/-- `pick` creates a non-deterministic, arbitrary value of the given
type `ty`, which is optional. If no type is provided, it is inferred.

We recommend giving type annotations when possible, e.g. `pick Nat`,
as type inference failures might lead to confusing error messages. -/
syntax (name := pickExpression) kw_pick (lineEq term) ? : term

/-- Binds a variable to a value that satisfies a predicate. -/
scoped syntax (name := letPick) "let" term (":" term)? ":|" term : doElem

/-- `require P` means that execution can only proceed if `P` holds. It
is used to express pre-conditions.

When an action including `require` is called by the environment, this
behaves like an `assume`. When it is called by another action, this
behaves like an `assert`: the caller must ensure that `P` holds.

If you have inconsistent `require` statements, your action will not
admit any executions. -/
scoped syntax (name := requireDo) kw_require term : doElem

/-- `assert P` means that `P` must hold on every execution that reaches
this statement. If `P` does not hold, this execution fails. -/
scoped syntax (name := assertDo) (priority := high) kw_assert term : doElem

/--
`if x :| p then … else …` is the conditional twin of `let x :| p`: if a
witness satisfying `p` exists, bind it and run the then-branch; otherwise run
the else-branch (defaulting to `pure ()`). The witness may be an identifier or
a flat tuple of identifiers, e.g. `if (x, y) :| r x y then …`.
-/
scoped syntax (name := ifSomeDo)
  withPosition(ppRealGroup(
    ppRealFill(ppIndent("if " term:max " :| " term " then") ppSpace doSeq)
    (colGe ppDedent(ppSpace "else " doSeq))?
  )) : doElem

/-- Witness identifiers of an existential `if`. -/
private def ifSomeBinderIdents? (pat : Term) : Option (Array Ident) :=
  match pat with
  | `(term| $x:ident) => some #[x]
  | `(($_:hygieneInfo $x:ident, $xs:ident,*)) => some (#[x] ++ xs.getElems)
  | _ => none

/-- Prepend `item` to a `do` sequence, preserving its braced/unbraced shape. -/
private def prependDoSeqItem (item : TSyntax ``Lean.Parser.Term.doSeqItem)
    (seq : TSyntax ``Lean.Parser.Term.doSeq) : MacroM (TSyntax ``Lean.Parser.Term.doSeq) := do
  match seq with
  | `(Lean.Parser.Term.doSeq| $items:doSeqItem*) =>
    `(Lean.Parser.Term.doSeq| $item $items*)
  | `(Lean.Parser.Term.doSeq| { $items:doSeqItem* }) =>
    `(Lean.Parser.Term.doSeq| { $item $items* })
  | _ => Macro.throwUnsupported

macro_rules
  | `(doElem| if $witness:term :| $predicate:term then $thenSeq:doSeq $[else $elseSeq?:doSeq]?) => do
    let some ids := ifSomeBinderIdents? witness
      | Macro.throwErrorAt witness
          "unsupported witness pattern for Veil existential `if`; expected an identifier or flat tuple of identifiers"
    let existsGuard ← `(term| ∃ $[$ids:ident]*, $predicate)
    let pickItem ← `(Lean.Parser.Term.doSeqItem| let $witness:term :| $predicate)
    let thenSeq ← prependDoSeqItem pickItem thenSeq
    let elseSeq ← elseSeq?.getDM `(Lean.Parser.Term.doSeq| pure PUnit.unit)
    `(doElem| if $existsGuard then $thenSeq else $elseSeq)

/-- `veil_let` is a `let` that the verification pipeline will not eagerly
inline. The right-hand side must be a pure computation. -/
scoped syntax (name := veilLetDo) (priority := high)
  kw_veil_let Lean.Parser.Term.letDecl : doElem

/-- `veil_let` is a `let` that the verification pipeline will not eagerly
inline. The right-hand side must be a pure computation. -/
scoped syntax:lead (name := veilLetTerm)
  withPosition(kw_veil_let Lean.Parser.Term.letDecl) "; " term : term

def parseVeilLet? (decl : TSyntax ``Lean.Parser.Term.letDecl) :
    Option (Term × Option Term × Term) :=
  let this : Term := ⟨mkIdent `this⟩
  match decl with
  | `(letDecl| $x:ident $[: $ty:term]? := $value:term) => some (⟨x.raw⟩, ty, value)
  | `(letDecl| $pattern:term $[: $ty:term]? := $value:term) => some (pattern, ty, value)
  | `(letDecl| := $value:term) => some (this, none, value)
  | `(letDecl| : $ty:term := $value:term) => some (this, some ty, value)
  | _ => none

macro_rules
  | `(veil_let $decl:letDecl; $body:term) => do
    let some (pattern, type?, value) := parseVeilLet? decl | Macro.throwUnsupported
    let ty ← type?.getDM `(_)
    `($(mkIdent `Veil.letEq) ($value : $ty) (fun ($pattern : $ty) => $body))

macro_rules
  | `(assume $t) => `($(mkIdent `VeilM.assume) $t)
  | `(pick $(t)?) => do
    `($(mkIdent `MonadNonDet.pick) $(← t.getDM `(_)))
  | `(doElem| let $x:term $[: $ty:term]? :| $p) => do
    `(doElem| let $x:term ← $(mkIdent `VeilM.pickSuchThat):ident $(← ty.getDM `(_)) (fun $x => $p))

private def veilVarType := withForbidden "veil_var" termParser

/--
`veil_var x : τ` declares an Ivy-style uninitialized mutable local by picking
an arbitrary initial value of type `τ`.
It expands like:

```
let x ← pick τ
let mut x := x
```
-/
scoped syntax (name := veilVarDo) kw_veil_var ident " : " veilVarType : doElem

macro_rules
  | `(doElem| veil_var $x:ident : $ty:term) =>
    `(doElem| do let $x:ident ← pick ($ty:term); let mut $x:ident := $x:ident)
  | `(doElem| veil_let $decl:letDecl) => do
    if decl.raw.find? (·.isOfKind ``Lean.Parser.Term.nestedAction) |>.isSome then
      Macro.throwErrorAt decl "the right-hand side of `veil_let` must be pure; move the computation to a preceding bind"
    let some (pattern, tyAsc, value) := parseVeilLet? decl
      | Macro.throwErrorAt decl "unsupported `veil_let` declaration"
    let value ← match tyAsc with
      | some ty => `(($value : $ty))
      | none => pure value
    `(doElem| let $pattern $[: $tyAsc]? :| $(mkIdent `Veil.eqWithoutSubst):ident $pattern $value)

/-- Nondeterministic assignment. The leading-token guard mirrors Lean's own
term-leading `do` elements (`doReassign`): without it, this parser's `term`
swallows a preceding statement-keyword statement (e.g. a plain `let`, whose
term form spans lines) and wins the longest-match against `doLet`. -/
@[scoped doElem_parser high] def havocAssignment := leading_parser
  Lean.Parser.Term.notFollowedByRedefinedTermToken >>
  atomic (termParser >> " := " >> " * ")

declare_syntax_cat unchanged_decl
declare_syntax_cat spec

/-- A precondition and postcondition specification, where the
postcondition depends on the return value. -/
scoped syntax (name := prePostSpecWithRetValInPost) kw_requires term colGe kw_ensures rcasesPat  "," term : spec

/-- A precondition and postcondition specification, where the
postcondition does not depend on the return value. -/
scoped syntax (name := prePostSpec) (priority := high) kw_requires term colGe kw_ensures term : spec

scoped syntax atomic(kw_with kw_unchanged) "[" ident,* "]" : unchanged_decl
scoped syntax spec (colGe unchanged_decl)? : term
scoped syntax atomic("[" kw_unchanged "|") str "|" ident* "]" : term
scoped syntax atomic("[" kw_unchanged_fields "|") str "|" ident* "]" : term

end Veil
