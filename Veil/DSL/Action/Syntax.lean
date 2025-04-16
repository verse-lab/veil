
import Lean
import Lean.Parser

open Lean Lean.Parser

namespace Veil

section VeilActionKeywords

declare_syntax_cat veilActionKeyword

syntax (name := kw_require) "require" : veilActionKeyword
syntax (name := kw_assume) "assume" : veilActionKeyword
syntax (name := kw_assert) "assert" : veilActionKeyword
syntax (name := kw_fresh) "fresh" : veilActionKeyword

/-- Precondition -/
syntax (name := kw_requires) "requires" : veilActionKeyword

/-- Postcondition -/
syntax (name := kw_ensures) "ensures" : veilActionKeyword

syntax (name := kw_with) "with" : veilActionKeyword
syntax (name := kw_unchanged) "unchanged" : veilActionKeyword

end VeilActionKeywords

/-- `require P` means that execution can only proceed if `P` holds. It
is used to express pre-conditions.

When an action including `require` is called by the environment, this
behaves like an `assume`. When it is called by another action, this
behaves like an `assert`: the caller must ensure that `P` holds.

In particular, if you do `let x ← fresh` and want to constrain the
value obtained, you should use `assume`, not `require`, e.g.:

```lean
let x ← fresh Nat
assume (x < 10)
```

If you have inconsistent `require` statements, your action will not
admit any executions. -/
syntax (name := requireStatement) kw_require term : term

/-- `assert P` means that `P` must hold on every execution that reaches
this statement. If `P` does not hold, this execution fails. -/
syntax (name := assertStatement) kw_assert term : term

/-- `assume P` ignores executions that do not satisfy `P`. BE CAREFUL
when making assumptions, as inconsistent assumptions will eliminate ALL
executions, making your specification vacuous. -/
syntax (name := assumeStatement) kw_assume term : term

/-- `fresh` creates a non-deterministic, arbitrary value of the given
type `ty`, which is optional. If no type is provided, it is inferred.

We recommend giving type annotations when possible, e.g. `fresh Nat`,
as type inference failures might lead to confusing error messages. -/
syntax (name := freshExpression) kw_fresh (lineEq term) ? : term

syntax (name := havocAssignment) (priority := high) atomic(term ":=" "*") : doElem

declare_syntax_cat unchanged_decl
declare_syntax_cat spec

/-- A precondition and postcondition specification, where the
postcondition depends on the return value. -/
syntax (name := prePostSpecWithRetValInPost) kw_requires term colGe kw_ensures rcasesPat  "," term : spec

/-- A precondition and postcondition specification, where the
postcondition does not depend on the return value. -/
syntax (name := prePostSpec) (priority := high) kw_requires term colGe kw_ensures term : spec

syntax atomic(kw_with kw_unchanged) "[" ident,* "]" : unchanged_decl
syntax spec (colGe unchanged_decl)? : term
syntax atomic("[" kw_unchanged "|") str "|" ident* "]" : term

end Veil
