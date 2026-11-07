module

public import Veil.Core.Tools.LivenessMC.LivenessMC
public import Veil.Core.Tools.ModelChecker.Concrete.Progress

public section

namespace Veil.LivenessMC
open Lean ModelChecker Concrete

/-- Completed prefix of this command's property list, transferred only between executions of the same elaborated snapshot. -/
private structure HandoffCheckpoint where
  propertiesChecked : Nat := 0
  exploredStates : Nat := 0
  searchNs : Nat := 0
  deriving ToJson, FromJson

variable {ρ σ l : Type} [beqσ : BEq σ] [hashσ : Hashable σ] [lawfulσ : LawfulBEq σ] [inhabσ : Inhabited σ]
  [beql : BEq l] [hashl : Hashable l] {th : ρ}

/-- The route and the search time, in total and per property. -/
private def timingJson (route : Route) (searchNs : Nat) (perProperty : Array Json) : Json :=
  Json.mkObj [("route", route.name), ("search_ns", toJson searchNs),
    ("properties", Json.arr perProperty)]

/-- Check declared properties in order with `checkRoute route`, stopping at the first counterexample. Assumptions and state
constraints match the safety checker, and a dead end stutters. Assertion failures and safety invariants are checked
separately by `#model_check`.

Cancellation and progress are honoured between properties only. Explored counts are product states summed over passed
properties, including the prefix carried over at handoff. -/
-- Specialize on `route` so that `checkRoute` receives it as a constant; otherwise every route is specialized
@[specialize route]
def checkAllWithProgress [ToJson ρ] [ToJson σ]
    (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l (Transitions l Int σ) th)
    (params : SearchParameters ρ σ) (properties : List (LivenessProperty ρ σ l))
    (instanceId : Nat) (cancelToken : IO.CancelToken) (route : Route := .fair)
    [cert : RouteCertificate route (restrictSystemByStateConstraints sys params th)] :
    IO Json := do
  let properties ← match ← getPropertySelection with
    | none => pure properties
    | some wanted =>
      match properties.filter (fun p => p.name.toString == wanted) with
      | [] => throw <| IO.userError s!"--property {wanted}: no such liveness property. \
          Available: {", ".intercalate (properties.map (·.name.toString))}"
      | selected => pure selected
  let cancelled := Json.mkObj [("result", "cancelled")]
  match params.violatedAssumptions th with
  | violates@(_ :: _) =>
      setViolationFound instanceId
      return Json.mkObj [("result", "found_violation"),
        ("violation", Json.mkObj [("kind", "assumption_failure"), ("violates", toJson violates)])]
  | [] => pure ()
  let checkpoint : HandoffCheckpoint ← do
    match ← getHandoffState instanceId with
    | none => pure {}
    | some state => IO.ofExcept (fromJson? state)
  if checkpoint.propertiesChecked > properties.length then
    throw <| IO.userError "liveness handoff checkpoint exceeds the number of properties"
  let rsys := restrictSystemByStateConstraints sys params th
  let mut progress : LivenessProgress := {
    numProperties := properties.length
    propertiesChecked := checkpoint.propertiesChecked
  }
  let mut explored := checkpoint.exploredStates
  let mut searchNs := checkpoint.searchNs
  let mut perProperty : Array Json := #[]
  for p in properties.drop progress.propertiesChecked do
    if ← cancelToken.isSet then return cancelled
    progress := { progress with currentProperty := p.name.toString }
    updateLivenessProgress instanceId progress
    let t0 ← IO.monoNanosNow
    match checkRoute route rsys p (cert := cert) with
    | .empty n =>
        let elapsed := (← IO.monoNanosNow) - t0
        searchNs := searchNs + elapsed
        explored := explored + n
        perProperty := perProperty.push <| Json.mkObj
          [("property", toJson p.name), ("search_ns", toJson elapsed),
           ("explored_states", toJson n), ("verdict", "holds")]
        progress := { progress with propertiesChecked := progress.propertiesChecked + 1 }
        saveHandoffState instanceId (toJson ({
          propertiesChecked := progress.propertiesChecked
          exploredStates := explored
          searchNs := searchNs
        } : HandoffCheckpoint))
        updateLivenessProgress instanceId progress
    | .nonEmpty stem loop =>
        let elapsed := (← IO.monoNanosNow) - t0
        searchNs := searchNs + elapsed
        perProperty := perProperty.push <| Json.mkObj
          [("property", toJson p.name), ("search_ns", toJson elapsed), ("verdict", "fails")]
        setViolationFound instanceId
        updateLivenessProgress instanceId progress
        return Json.mkObj [("result", "found_violation"),
          ("violation", Json.mkObj [("kind", "liveness_failure"), ("violates", toJson [p.name])]),
          ("theory", toJson th),
          ("lasso", Json.mkObj [("stem", toJson stem), ("loop", toJson loop)]),
          ("timing", timingJson route searchNs perProperty)]
  updateLivenessProgress instanceId progress
  return Json.mkObj [("result", "no_violation_found"),
    ("properties_checked", toJson progress.propertiesChecked), ("explored_states", toJson explored),
    ("timing", timingJson route searchNs perProperty)]

end Veil.LivenessMC
