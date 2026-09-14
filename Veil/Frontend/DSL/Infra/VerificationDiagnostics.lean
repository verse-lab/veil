import Veil.Frontend.DSL.Module.Syntax
import Veil.Frontend.DSL.Infra.TraceSyntax
import Veil.Frontend.DSL.Infra.VerificationSupport
import Veil.Frontend.DSL.Tactic.Core

open Lean Elab Command Tactic
namespace Veil

elab_rules : command
  | `(#check_invariants) => do
    if ← hasVerificationSupport then throwUnsupportedSyntax
    throwError "Verification requires `import Veil`; `Veil.Core` supports explicit-state model checking."
  | `(#check_action $a:ident) => do
    if ← hasVerificationSupport then throwUnsupportedSyntax
    throwErrorAt a "Verification requires `import Veil`; `Veil.Core` supports explicit-state model checking."
  | `(#gen_theorems) => do
    if ← hasVerificationSupport then throwUnsupportedSyntax
    throwError "Verification requires `import Veil`; `Veil.Core` supports explicit-state model checking."
  | `($r:expected_smt_result trace $[[$_name:ident]]? { $_spec:traceSpec } $[$_pf:term]?) => do
    if ← hasVerificationSupport then throwUnsupportedSyntax
    throwErrorAt r "Symbolic traces require `import Veil`; use `#model_check` with `Veil.Core`."

elab_rules : tactic
  | `(tactic| veil_smt) => do
    if ← hasVerificationSupport then throwUnsupportedSyntax
    throwError "SMT verification requires `import Veil`."
  | `(tactic| veil_smt?) => do
    if ← hasVerificationSupport then throwUnsupportedSyntax
    throwError "SMT verification requires `import Veil`."

end Veil
