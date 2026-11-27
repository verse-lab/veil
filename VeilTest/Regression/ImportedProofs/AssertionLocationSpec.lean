module

public import Veil

veil module ImportedAssertionLocation
individual flag : Bool
after_init { flag := false }
action boom { assert flag }
invariant [off] ¬ flag

/-- warning: This assertion can fail even if the module's invariants hold when `boom` starts. -/
#guard_msgs in
#gen_spec

open Lean Elab Command Veil.ModelChecker.Concrete in
public meta def checkAssertionLocation : CommandElabM Unit := do
  let nextId ← nextInstanceId.get
  let some result ← getResultJson (nextId - 1)
    | throwError "expected a model-check result"
  let violation ← IO.ofExcept <| result.getObjVal? "violation"
  unless violation.getObjValAs? String "kind" == .ok "assertion_failure" do
    throwError "expected an assertion failure, got {violation}"
  let .ok location := violation.getObjVal? "assertion_info"
    | throwError "assertion failure is missing its source location"
  -- The assertion is on line 8 of the spec, at column 14.
  unless location.getObjValAs? String "moduleName" == .ok "ImportedAssertionLocation" &&
      location.getObjValAs? String "procedureName" == .ok "boom" &&
      location.getObjValAs? Nat "line" == .ok 8 &&
      location.getObjValAs? Nat "column" == .ok 14 do
    throwError "unexpected assertion location {location}"

set_option veil.violationIsError false
#guard_msgs (drop info) in
#model_check interpreted {}
run_cmd checkAssertionLocation
end ImportedAssertionLocation
