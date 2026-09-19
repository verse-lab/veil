module

public meta import Veil.Frontend.DSL.Module.Syntax
public meta import Veil.Frontend.DSL.Infra.TraceSyntax
public meta import Veil.Frontend.DSL.Infra.VerificationSupport
public meta import Veil.Frontend.DSL.Tactic.Core

public meta section

/-! Fallback diagnostics for verification syntax exposed by `Veil.Core`.
When full `Veil` is imported, decline with `throwUnsupportedSyntax` so the real
elaborators run regardless of import order. -/

open Lean Elab Command Tactic
namespace Veil

@[command_elab Veil.checkInvariants, command_elab Veil.checkAction, command_elab Veil.genTheorems]
def elabVerificationUnavailable : CommandElab := fun stx => do
  if ← hasVerificationSupport then throwUnsupportedSyntax
  let ref := match stx with
    | `(#check_action $a:ident) => a.raw
    | _ => stx
  throwErrorAt ref "Verification requires `import Veil`; `Veil.Core` supports explicit-state model checking."

elab_rules : command
  | `($r:expected_smt_result trace $[[$_name:ident]]? { $_spec:traceSpec } $[$_pf:term]?) => do
    if ← hasVerificationSupport then throwUnsupportedSyntax
    throwErrorAt r "Symbolic traces require `import Veil`; use `#model_check` with `Veil.Core`."

@[tactic veil_smt, tactic veil_smt_trace]
def elabSmtUnavailable : Tactic := fun _ => do
  if ← hasVerificationSupport then throwUnsupportedSyntax
  throwError "SMT verification requires `import Veil`."

end Veil
