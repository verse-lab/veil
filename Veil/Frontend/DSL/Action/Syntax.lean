
import Lean
import Lean.Parser

open Lean Lean.Parser

namespace Veil

section VeilActionKeywords

declare_syntax_cat veilActionKeyword

scoped syntax (name := kw_require) "require" : veilActionKeyword
scoped syntax (name := kw_assume) "assume" : veilActionKeyword
scoped syntax (name := kw_assert) "assert" : veilActionKeyword
scoped syntax (name := kw_pick) "pick" : veilActionKeyword
scoped syntax (name := kw_veil_var) "veil_var" : veilActionKeyword

/-- Precondition -/
scoped syntax (name := kw_requires) "requires" : veilActionKeyword

/-- Postcondition -/
scoped syntax (name := kw_ensures) "ensures" : veilActionKeyword

scoped syntax (name := kw_with) "with" : veilActionKeyword
scoped syntax (name := kw_unchanged) "unchanged" : veilActionKeyword
scoped syntax (name := kw_unchanged_fields) "unchanged_fields" : veilActionKeyword

end VeilActionKeywords

/-- `require P` means that execution can only proceed if `P` holds. It
is used to express pre-conditions.

When an action including `require` is called by the environment, this
behaves like an `assume`. When it is called by another action, this
behaves like an `assert`: the caller must ensure that `P` holds.

If you have inconsistent `require` statements, your action will not
admit any executions. -/
syntax (name := requireStatement) kw_require term : term

/-- `assert P` means that `P` must hold on every execution that reaches
this statement. If `P` does not hold, this execution fails. -/
syntax (name := assertStatement) (priority := high) kw_assert term : term

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
scoped syntax (name := letPick) "let" term ":|" term : doElem

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

scoped syntax (name := havocAssignment) (priority := high) atomic(term ":=" "*") : doElem

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
