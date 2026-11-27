module

public meta import Lean
public meta import Veil.Frontend.DSL.Infra.EnvExtensions

public meta section

open Lean Elab Command

namespace Veil

/-- Enrich JSON with assertion source info for any assertion failures.
Looks for "exception_id" fields in the JSON and adds corresponding source info. -/
partial def enrichJsonWithAssertions (json : Json) (sources : Std.HashMap AssertionId AssertionSourceInfo)
    : Json :=
  match json with
  | .obj fields =>
    -- Check if this object has an exception_id field and add assertion_info if found
    let fieldsWithInfo : List (String × Json) := fields.toList
    let hasExceptionId := fieldsWithInfo.find? (·.1 == "exception_id")
    let newFields := match hasExceptionId with
      | some (_, exIdJson) =>
        match exIdJson.getInt? with
        | .ok exId =>
          match sources.get? exId with
          | some info => fieldsWithInfo ++ [("assertion_info", toJson info)]
          | none => fieldsWithInfo
        | .error _ => fieldsWithInfo
      | none => fieldsWithInfo
    -- Recursively process all values
    Json.mkObj (newFields.map fun (k, v) => (k, enrichJsonWithAssertions v sources))
  | .arr items => .arr (items.map (enrichJsonWithAssertions · sources))
  | other => other

end Veil
