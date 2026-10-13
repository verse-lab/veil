module

public import Veil
public import VeilTest.Regression.LivenessHandoffHelper
public meta import VeilTest.Regression.LivenessHandoffHelper
import all Veil.Core.Tools.ModelChecker.CompiledRuntime

open Veil Veil.LivenessMC Veil.ModelChecker Veil.ModelChecker.Concrete Lean

private instance : ToJson Unit where
  toJson _ := .null

private def loopingSystem :
    EnumerableTransitionSystem Unit (List Unit) Nat (List Nat) Int Unit (Transitions Unit Int Nat) () := {
  initStates := [0]
  tr := fun _ n => { successes := [((), n)], failures := [] }
}

/-- `j` without its `timing` field. -/
private def withoutTiming (j : Json) : Json :=
  match j with
  | .obj kvs => .obj (kvs.erase "timing")
  | _ => j

private def timingOf (j : Json) : Json := j.getObjValD "timing"

private def immediatelyTrue : LivenessProperty Unit Nat Unit := {
  name := `immediatelyTrue
  atoms := [.state { name := `always, property := fun _ _ => True }]
  φ := .eventually (.atom 0)
}

-- Liveness retains its completed prefix and property budget across a handoff.
#eval show IO Unit from do
  let (id, _) ← allocProgressInstance (.liveness { numProperties := 3 })
  updateLivenessProgress id {
    numProperties := 3, propertiesChecked := 1,
    currentProperty := "progress" }
  let _ ← resetProgressForHandoff id
  let after ← getProgress id
  unless (match after.details with
      | .liveness m => m.numProperties == 3 && m.propertiesChecked == 1 &&
          m.currentProperty.isEmpty
      | _ => false) do
    throw <| IO.userError "handoff must preserve liveness metrics"

-- Cancellation is honoured between properties: the property being checked runs to
-- completion and is recorded in the checkpoint, then the run stops without a verdict.
-- A run cancelled before it starts reports no verdict either.
#eval show IO Unit from do
  let params : SearchParameters Unit Nat := { invariants := [], earlyTerminationConditions := [] }
  let (id, tk) ← allocProgressInstance (.liveness { numProperties := 1 })
  tk.set
  let result ← checkAllWithProgress loopingSystem params [immediatelyTrue] id tk
  unless result.getObjValD "result" == "cancelled" do
    throw <| IO.userError "pre-cancelled search reported a verdict"
  let (id, tk) ← allocProgressInstance (.liveness { numProperties := 2 })
  -- The first property's atom blocks until the token is set, so the run is cancelled
  -- while that property is being checked and stops right after it.
  VeilTest.LivenessHandoff.armProbe tk
  let waitingProperty := VeilTest.LivenessHandoff.blockingProperty
  let task ← IO.asTask (prio := .dedicated) <|
    checkAllWithProgress loopingSystem params [waitingProperty, immediatelyTrue] id tk
  for _ in [:500] do
    if let .liveness m := (← getProgress id).details then
      if m.currentProperty == waitingProperty.name.toString then break
    IO.sleep 10
  requestCancellation id
  for _ in [:500] do
    if ← IO.hasFinished task then break
    IO.sleep 10
  unless ← IO.hasFinished task do
    throw <| IO.userError "liveness run did not stop at the property boundary"
  let result ← IO.ofExcept (← IO.wait task)
  unless result.getObjValD "result" == "cancelled" do
    throw <| IO.userError "a run cancelled between properties reported a verdict"
  let some checkpoint ← getHandoffState id
    | throw <| IO.userError "cancellation lost the completed prefix"
  unless checkpoint.getObjValAs? Nat "propertiesChecked" == .ok 1 do
    throw <| IO.userError "the property being checked was not completed and recorded"
  let progress ← getProgress id
  unless (match progress.details with | .liveness m => m.propertiesChecked == 1 | _ => false) do
    throw <| IO.userError "cancellation lost completed-property progress"

-- Resume from a real completed prefix and preserve both final totals. A fresh
-- instance has no inherited checkpoint, and a fully completed prefix does no more work.
#eval show IO Unit from do
  let params : SearchParameters Unit Nat := { invariants := [], earlyTerminationConditions := [] }
  let alwaysTrue := { immediatelyTrue with φ := .always (.atom 0) }
  let (fullId, fullTk) ← allocProgressInstance (.liveness { numProperties := 2 })
  let full ← checkAllWithProgress loopingSystem params [alwaysTrue, alwaysTrue] fullId fullTk
  unless (full.getObjValAs? Nat "explored_states").toOption.getD 0 > 0 do
    throw <| IO.userError "the totals test must explore a nonempty graph"
  let (prefixId, prefixTk) ← allocProgressInstance (.liveness { numProperties := 1 })
  discard <| checkAllWithProgress loopingSystem params [alwaysTrue] prefixId prefixTk
  let some checkpoint ← getHandoffState prefixId | throw <| IO.userError "missing checkpoint"
  let (id, tk) ← allocProgressInstance (.liveness { numProperties := 2 })
  unless (← getHandoffState id).isNone do throw <| IO.userError "checkpoint leaked between runs"
  saveHandoffState id checkpoint
  let resumed ← checkAllWithProgress loopingSystem params [alwaysTrue, alwaysTrue] id tk
  unless withoutTiming resumed == withoutTiming full do
    throw <| IO.userError "resumed totals differ from uninterrupted checking"
  unless ((timingOf resumed).getObjValD "properties").getArr?.toOption.map (·.size) == some 1 do
    throw <| IO.userError "the resumed run reported the prefix's searches as its own"
  let complete ← checkAllWithProgress loopingSystem params [alwaysTrue, alwaysTrue] id tk
  unless withoutTiming complete == withoutTiming full do
    throw <| IO.userError "completed prefix was counted twice"
  unless (timingOf complete).getObjValD "properties" == .arr #[] do
    throw <| IO.userError "a fully completed prefix reported a search"
  unless (timingOf complete).getObjValD "search_ns" == (timingOf resumed).getObjValD "search_ns" do
    throw <| IO.userError "a fully completed prefix lost the carried search time"
  unless (match (← getProgress id).details with
      | .liveness m => m.propertiesChecked == 2 && m.currentProperty.isEmpty
      | _ => false) do
    throw <| IO.userError "a fully completed prefix was searched again"
  let invalid ← (checkAllWithProgress loopingSystem params [alwaysTrue] id tk).toBaseIO
  unless invalid matches .error _ do throw <| IO.userError "invalid checkpoint was accepted"

-- Handoff arguments coexist with the safety checker's parallel settings.
#eval show IO Unit from do
  let checkpoint := Json.mkObj [("propertiesChecked", toJson (1 : Nat)), ("exploredStates", toJson (7 : Nat))]
  for args in [[], ["4", "20", "1"]] do
    let parsed ← IO.ofExcept <| Compilation.parseLaunchArgs (args ++ ["--handoff-state", checkpoint.compress])
    unless (parsed.positional, parsed.handoffState) == (args, some checkpoint) do throw <| IO.userError "handoff arguments changed parallel settings"
    let plain ← IO.ofExcept <| Compilation.parseLaunchArgs args
    unless (plain.positional, plain.handoffState) == (args, none) do throw <| IO.userError "standalone run acquired a checkpoint"
  for args in [["--handoff-state"], ["--handoff-state", "not JSON"]] do
    unless Compilation.parseLaunchArgs args matches .error _ do
      throw <| IO.userError "malformed handoff arguments were accepted"

open Lean Elab Command in
elab "#test_liveness_handoff" fail:term : command => do
  let mod ← getCurrentModule
  let call ← `(VeilTest.LivenessHandoff.handoffProbe $fail)
  ExecutionWorkflow.run { name := "liveness_handoff_test" } .liveness mod (← getRef) .default call

veil module Handoff
individual flag : Bool
after_init { flag := false }
action idle { flag := flag }
liveness [trivial] □ ⊤
liveness [another] □ ⊤
invariant true
#gen_spec

/-- info: ✅ No liveness violation (checked 2 properties, explored 2 product states) -/
#guard_msgs in
#test_liveness_handoff false

/--
error: ❌ Violation: liveness_failure (violates: pending)
  Stem:
    State 0:
0
  Loop (repeats):
    State 0:
0
    State 1:
0
-/
#guard_msgs in
#test_liveness_handoff true

end Handoff
