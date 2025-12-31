import Lean
import ProofWidgets
import Smt

/-!
# SMT Result Types

This module contains types for representing SMT solver results, including
models, counterexamples, and result categorization.
-/

open Lean

namespace Veil

abbrev SmtOutput := (Name × Nat) × Smt.AsyncOutput

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

structure AnnotatedSmtModel where
  /-- The model data structured returned by Lean SMT. -/
  raw : Smt.Model
  /-- A widget view of the raw model. -/
  rawHtml : ProofWidgets.Html
  /-- JSON representation of the structured counterexample. Pre-computed using
  `VeilCTI.toJson` or `VeilTrace.toJson` at construction time. -/
  structuredJson : Json

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
  | sat (counterexamples : Array (Option AnnotatedSmtModel))
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
                    | some ce => Json.mkObj [("raw", toJson ce.raw), ("html", Json.str "<p>Counter-example HTML</p>"), ("structuredJson", ce.structuredJson)]
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
                    | some ce => do
                      let html ← Server.rpcEncode ce.rawHtml
                      return Json.mkObj [
                        ("raw", toJson ce.raw),
                        ("html", html),
                        ("structuredJson", ce.structuredJson),
                      ]
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
    | .sat counterexamples => m!"sat {counterexamples.map (·.map (fun ce => toMessageData ce.raw))}"
    | .unknown reasons => m!"unknown {reasons}"
    | .unsat counterexamples => m!"unsat {counterexamples.map (·.map (toMessageData ·))}"

end Veil
