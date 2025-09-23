import Lean
import Veil.Frontend.DSL.Module.Representation
import Smt
open Lean

namespace Veil

inductive VCKind where
  /-- Primary VCs are those that are _needed_ to derive other VCs. We
  try to prove these by SMT, if possible. -/
  | primary
  /-- Derived VCs typically do not require proof by SMT — they rely on
  applications of primary VCs (and potentially other derived VCs). -/
  | derived
deriving Inhabited, BEq, Hashable

instance : ToString VCKind where
  toString kind :=
    match kind with
    | .primary => "primary"
    | .derived => "derived"

structure VCMetadata where
  /-- The kind of this VC. -/
  kind : VCKind
  baseParams : Array Parameter
  extraParams : Array Parameter
  /-- The declarations that this VC's _statement_ depends on. The proof
  might need additional dependencies. -/
  stmtDerivedFrom : Std.HashSet Name
deriving Inhabited

instance : ToString VCMetadata where
  toString metadata :=
    s!"(kind: {metadata.kind})"

abbrev SmtOutput := (Name × Nat) × Smt.AsyncOutput
-- abbrev VeilResult := Array SmtOutput

abbrev SmtModel := Array (Expr × Expr)
abbrev SmtUnsatCore := Array Expr

/-- The order in which results "saturate" (from "strongest" — eats everything —
to "weakest" — gets eaten by everything else):
  - `error` (if a list of result has an `error`, the overall VeilResult becomes `error`)
  - `sat` (if a list of result has a `sat`, but no `error`, the overall VeilResult becomes `sat`)
  - `unknown` (if a list of result has an `unknown`, but no `error` or `sat`, the overall VeilResult becomes `unknown`)
  - `unsat` (if a list of result has only `unsat` results, the overall VeilResult becomes `unsat`)
-/
inductive SmtResult where
  /-- The SMT solver threw an exception. We can have multiple exceptions, since
  a single term might contain multiple calls to `smt`. If an exception is
  thrown in _any_ of the calls, the entire `VeilResult` becomes `error`. -/
  | error (exs : Array Exception)
  /-- We can have multiple counter-examples, since a single term might contain
  multiple calls to `smt`. If there is at least one `sat` result in a term, the
  entire `VeilResult` becomes `sat` (unless there are any `error` results). -/
  | sat (counterexamples : Array (Option SmtModel))
  /-- The SMT solver returned `unknown`. We can have multiple unknown results, since
  a single term might contain multiple calls to `smt`.  -/
  | unknown (reasons : Array String)
  /-- The SMT solver returned `unsat`. We can have multiple unsat results, since
  a single term might contain multiple calls to `smt`. -/
  | unsat (counterexamples : Array SmtUnsatCore)

instance : ToString Smt.cvc5Result where
  toString result :=
    match result with
    | .sat _ => "sat"
    | .unsat _ _ => "unsat"
    | .unknown _ => "unknown"

instance : ToString Smt.Result where
  toString result :=
    match result with
    | .sat _ => "sat"
    | .unsat _ _ => "unsat"
    | .unknown _ => "unknown"

instance : ToString (Except cvc5.Error Smt.cvc5Result) where
  toString raw :=
    match raw with
    | .ok result => s!"{result}"
    | .error error => s!"{error}"

instance : ToMessageData Smt.AsyncOutput where
  toMessageData output :=
    match output with
    | .queryString query => m!"{query}"
    | .rawResult raw => m!"{raw}"
    | .result result => m!"{result}"
    | .exception ex => m!"exception {ex.toMessageData}"

instance : ToMessageData SmtOutput where
  toMessageData result :=
    match result with
    | ((name, index), f) => m!"{name}.{index}: {f}"

instance : ToMessageData SmtResult where
  toMessageData result :=
    match result with
    | .error exs => m!"error {exs.map (·.toMessageData)}"
    | .sat counterexamples => m!"sat {counterexamples.map (·.map (·.map (toMessageData ·)))}"
    | .unknown reasons => m!"unknown {reasons}"
    | .unsat counterexamples => m!"unsat {counterexamples.map (·.map (toMessageData ·))}"

end Veil
