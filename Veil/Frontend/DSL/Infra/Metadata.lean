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

inductive SolverResult where
  | cvc5 (result : Option Smt.cvc5Result)
deriving Inhabited

abbrev VeilResult := Option SolverResult

instance : ToMessageData SolverResult where
  toMessageData result :=
    match result with
    | .cvc5 (.some _) => m!"cvc5 result"
    | .cvc5 (.none) => m!"none"

end Veil
