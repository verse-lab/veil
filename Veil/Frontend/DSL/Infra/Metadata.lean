import Lean
import Veil.Frontend.DSL.Module.Representation
import ProofWidgets
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

instance : ToJson VCKind where
  toJson kind :=
    match kind with
    | .primary => "primary"
    | .derived => "derived"

instance : FromJson VCKind where
  fromJson? json := do
    let s ← fromJson? json
    match s with
    | "primary" => pure .primary
    | "derived" => pure .derived
    | _ => .error s!"Invalid VCKind: {s}"

structure VCMetadata where
  /-- The kind of this VC. -/
  kind : VCKind
  /-- The action that this VC is about. -/
  action: Name
  /-- The property that this VC is about. -/
  property: Name
  baseParams : Array Parameter
  extraParams : Array Parameter
  /-- The declarations that this VC's _statement_ depends on. The proof
  might need additional dependencies. -/
  stmtDerivedFrom : Std.HashSet Name
deriving Inhabited

instance : ToString VCMetadata where
  toString metadata :=
    s!"(kind: {metadata.kind})"

instance : ToJson VCMetadata where
  toJson metadata :=
    Json.mkObj [
      ("kind", toJson metadata.kind),
      ("action", toJson metadata.action),
      ("property", toJson metadata.property),
    ]

instance : FromJson VCMetadata where
  fromJson? json := do
    let kind ← json.getObjValAs? VCKind "kind"
    let action ← json.getObjValAs? Name "action"
    let property ← json.getObjValAs? Name "property"
    pure {
      kind := kind
      action := action
      property := property
      baseParams := #[]
      extraParams := #[]
      stmtDerivedFrom := ∅
    }

abbrev SmtOutput := (Name × Nat) × Smt.AsyncOutput
-- abbrev VeilResult := Array SmtOutput

-- instance : ToJson Smt.Model where
--   toJson model :=
--     Json.mkObj [
--       ("sorts", toJson (model.sorts.map (fun (expr, value) => Json.mkObj [("expr", toJson s!"{expr}"), ("value", toJson s!"{value}")]))),
--       ("values", toJson (model.values.map (fun (expr, value) => Json.mkObj [("expr", toJson s!"{expr}"), ("value", toJson s!"{value}")])))
--     ]


instance : ToJson Smt.Model where
  toJson model :=
    Json.mkObj [
      ("sorts", toJson model.sorts.size),
      ("values", toJson model.values.size)
    ]

instance : ToMessageData Smt.Model where
  toMessageData model :=
    let toMD := fun (mv, value) => m!"{mv}: {value}"
    m!"sorts: {model.sorts.map toMD}\nconstants: {model.values.map toMD}"

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
  | error (exs : Array (Exception × Json))
  /-- We can have multiple counter-examples, since a single term might contain
  multiple calls to `smt`. If there is at least one `sat` result in a term, the
  entire `VeilResult` becomes `sat` (unless there are any `error` results). -/
  | sat (counterexamples : Array (Option (Smt.Model × ProofWidgets.Html)))
  /-- The SMT solver returned `unknown`. We can have multiple unknown results, since
  a single term might contain multiple calls to `smt`.  -/
  | unknown (reasons : Array String)
  /-- The SMT solver returned `unsat`. We can have multiple unsat results, since
  a single term might contain multiple calls to `smt`. -/
  | unsat (counterexamples : Array SmtUnsatCore)
deriving Inhabited

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

instance : ToJson SmtResult where
  toJson
  | .error exs =>
      Json.mkObj [("kind", Json.str "error"),
                  ("exceptions", toJson (exs.map (fun (_, code) => toJson code)))]
  | .sat counterexamples =>
      Json.mkObj [("kind", Json.str "sat"),
                  ("counterexamples", toJson (counterexamples.map <| fun ce? =>
                    match ce? with
                    | some (ce, _html) => Json.mkObj [("model", toJson ce), ("html", Json.str "<p>Counter-example HTML</p>")]
                    | none => Json.null
                  ))]
  | .unknown reasons =>
      Json.mkObj [("kind", Json.str "unknown"),
                  ("reasons", toJson reasons)]
  | .unsat unsatCores =>
      Json.mkObj [("kind", Json.str "unsat"),
                  ("unsatCores", toJson (unsatCores.map (fun core =>
                    toJson (core.map (fun e => s!"{e}"))
                  )))]

instance : Server.RpcEncodable SmtResult where
  rpcEncode r := do match r with
  | .error exs => do
    return .mkObj [("kind", Json.str "error"),
                  ("exceptions", toJson (exs.map (fun (_, code) => toJson code)))]
  | .sat counterexamples => do
    return .mkObj [("kind", Json.str "sat"),
                  ("counterexamples", toJson (← counterexamples.mapM <| fun ce? => do
                    match ce? with
                    | some (ce, html) => do
                    let html ← Server.rpcEncode html
                    return Json.mkObj [("model", toJson ce), ("html", html)]
                    | none => pure <| Json.null))]
  | .unsat unsatCores => do
    return .mkObj [("kind", Json.str "unsat"),
                  ("unsatCores", toJson (unsatCores.map (fun core =>
                    toJson (core.map (fun e => s!"{e}"))
                  )))]
  | .unknown reasons => do
    return .mkObj [("kind", Json.str "unknown"),
                  ("reasons", toJson reasons)]

  rpcDecode _ := do return default

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
    | .error exs => m!"error {exs.map (·.1.toMessageData)}"
    | .sat counterexamples => m!"sat {counterexamples.map (·.map (fun (ce, _html) => toMessageData ce))}"
    | .unknown reasons => m!"unknown {reasons}"
    | .unsat counterexamples => m!"unsat {counterexamples.map (·.map (toMessageData ·))}"

end Veil
