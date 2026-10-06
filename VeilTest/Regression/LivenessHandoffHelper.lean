module

public import Veil

public section

namespace VeilTest.LivenessHandoff
open Veil Veil.LivenessMC Veil.ModelChecker Veil.ModelChecker.Concrete Lean

private instance : ToJson Unit where
  toJson _ := .null

private def loopingSystem :
    EnumerableTransitionSystem Unit (List Unit) Nat (List Nat) Int Unit (Transitions Unit Int Nat) () := {
  initStates := [0]
  tr := fun _ n => { successes := [((), n)], failures := [] }
}

private initialize probeCancelToken : IO.Ref (Option IO.CancelToken) ← IO.mkRef none

-- Test-only atom. Interpreted, the first property blocks until the armed token is set and
-- then passes, so the run stops at the property boundary right after it, and the second
-- property is never reached. Compiled, the first property would fail if it were rerun, and
-- the second has the chosen verdict.
@[noinline] private unsafe def probeAtomImpl (first fail : Bool) (st : Nat) : Bool := unsafeBaseIO do
  if st != 0 then return false
  if ← compiledModeEnabled.get then return !first && !fail
  if !first then return false
  let some tk ← probeCancelToken.get | return false
  for _ in [:30000] do
    if ← tk.isSet then return true
    IO.sleep 10
  return false

@[implemented_by probeAtomImpl] private opaque probeAtom (first fail : Bool) (st : Nat) : Bool

private def probeProperty (first fail : Bool) : LivenessProperty Unit Nat Unit := {
  name := if first then `passed else `pending
  atoms := [.state { name := `probe, property := fun _ st => probeAtom first fail st = true }]
  φ := if first then .always (.atom 0) else .eventually (.atom 0)
}

/-- Arm the probe atoms with the token they wait for. -/
def armProbe (tk : IO.CancelToken) : IO Unit := probeCancelToken.set (some tk)

/-- Interpreted, this property passes only once the armed token is set: its atom blocks until
then, so a test can cancel a run deterministically while the property is being checked. -/
def blockingProperty : LivenessProperty Unit Nat Unit := probeProperty true false

-- Exercise the real runner through the shared scheduler and a separate binary.
def handoffProbe {α : Type} (fail : Bool) (_ : Option ParallelConfig) (id : Nat) (tk : IO.CancelToken)
    (finish : Json → IO α) : IO α := do
  let native ← compiledModeEnabled.get
  if native then
    let some checkpoint ← getHandoffState id | throw <| IO.userError "native worker received no checkpoint"
    unless checkpoint.getObjValAs? Nat "propertiesChecked" == .ok 1 do
      throw <| IO.userError "native worker received the wrong completed prefix"
  armProbe tk
  let params : SearchParameters Unit Nat := { invariants := [], earlyTerminationConditions := [] }
  let result ← checkAllWithProgress loopingSystem params [probeProperty true fail, probeProperty false fail] id tk
  if !native then
    unless (← tk.isSet) && result.getObjValD "result" == "cancelled" do
      throw <| IO.userError "interpreted probe did not stop at the handoff"
  else if fail then
    unless result.getObjValD "result" == "found_violation" &&
        (result.getObjValD "violation").getObjValD "violates" == toJson ([`pending] : List Name) do
      throw <| IO.userError "compiled run repeated the passed property or skipped the pending property"
  else
    unless result.getObjValD "result" == "no_violation_found" &&
        result.getObjValAs? Nat "properties_checked" == .ok 2 do
      throw <| IO.userError "compiled run failed to reuse the completed prefix"
    let some checkpoint ← getHandoffState id | throw <| IO.userError "missing native checkpoint"
    let carried ← IO.ofExcept <| checkpoint.getObjValAs? Nat "exploredStates"
    let .empty remaining := checkFair loopingSystem (probeProperty false fail)
      | throw <| IO.userError "pending property unexpectedly failed"
    unless carried > 0 && result.getObjValAs? Nat "explored_states" == .ok (carried + remaining) do
      throw <| IO.userError "handoff lost the completed prefix's explored-state count"
  finish result

end VeilTest.LivenessHandoff
