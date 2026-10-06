module

public import Veil.Core.Tools.LivenessMC.LivenessMC
public import Veil.Core.Tools.ModelChecker.Concrete.Progress

public section

namespace Veil.LivenessMC
open Lean ModelChecker Concrete

/-- Completed prefix of this command's property list. The workflow transfers it only
between executions of the same elaborated snapshot; it is not a reusable certificate. -/
private structure HandoffCheckpoint where
  propertiesChecked : Nat := 0
  exploredStates : Nat := 0
  deriving ToJson, FromJson

variable {ρ σ l : Type} [beqσ : BEq σ] [hashσ : Hashable σ] [lawfulσ : LawfulBEq σ] [inhabσ : Inhabited σ]
  [beql : BEq l] [hashl : Hashable l] {th : ρ}

/-- Check declared properties in order with `checkFair`, stopping at the first
counterexample. Assumptions and state constraints match the safety checker.
A dead end stutters: LTLLib gives it a self-loop, so a run may end there. Assertion
failures and safety invariants are checked separately by `#model_check`.

Cancellation is honoured between properties only. LTLLib's search is pure, so the
property being checked always runs to completion; it is recorded in the checkpoint
before the token is consulted again, and a handoff redoes none of its work. Progress
is likewise reported between properties. Compiled runs are cancelled by killing the
process instead.

The counterexample preserves LTLLib's state projections of the stem and loop.
It does not invent action labels: parallel labelled edges need not be determined
by their endpoints. Explored counts are product states summed over passed properties,
including the completed prefix carried over from interpreted execution at handoff.
Only the first unfinished property restarts its search. -/
def checkAllWithProgress [ToJson ρ] [ToJson σ]
    (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l (Transitions l Int σ) th)
    (params : SearchParameters ρ σ) (properties : List (LivenessProperty ρ σ l))
    (instanceId : Nat) (cancelToken : IO.CancelToken) : IO Json := do
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
  let sys := restrictSystemByStateConstraints sys params th
  let mut progress : LivenessProgress := {
    numProperties := properties.length
    propertiesChecked := checkpoint.propertiesChecked
  }
  let mut explored := checkpoint.exploredStates
  for p in properties.drop progress.propertiesChecked do
    if ← cancelToken.isSet then return cancelled
    progress := { progress with currentProperty := p.name.toString }
    updateLivenessProgress instanceId progress
    match checkFair sys p with
    | .empty n =>
        explored := explored + n
        progress := { progress with propertiesChecked := progress.propertiesChecked + 1 }
        saveHandoffState instanceId (toJson ({
          propertiesChecked := progress.propertiesChecked
          exploredStates := explored
        } : HandoffCheckpoint))
        updateLivenessProgress instanceId progress
    | .nonEmpty stem loop =>
        setViolationFound instanceId
        updateLivenessProgress instanceId progress
        return Json.mkObj [("result", "found_violation"),
          ("violation", Json.mkObj [("kind", "liveness_failure"), ("violates", toJson [p.name])]),
          ("theory", toJson th),
          ("lasso", Json.mkObj [("stem", toJson (stem.map Prod.fst)),
            ("loop", toJson (loop.map Prod.fst))])]
  updateLivenessProgress instanceId progress
  return Json.mkObj [("result", "no_violation_found"),
    ("properties_checked", toJson progress.propertiesChecked), ("explored_states", toJson explored)]

end Veil.LivenessMC
