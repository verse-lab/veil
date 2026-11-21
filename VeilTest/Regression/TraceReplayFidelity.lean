module

public import Veil

open Lean Meta Elab Command Veil

set_option veil.violationIsError false

veil module TraceReplayFidelity
individual count : Nat
after_init { count := 0 }
action choose {
  let k ← pick Nat
  count := k
}
action disabled (_impossible : Fin 0) { pure () }
invariant [ok] True
#gen_spec

-- A second elaboration under a replay label would silently change the checkpoint to True.
macro "contextualAssertion" : term => `(by
  first
  | exact (fun (_ : $(mkIdent `Label):ident) => True) (by assumption)
  | exact $(mkIdent `count):ident = 1)

#guard_msgs (drop info) in
sat trace [found] {
  choose
  assert contextualAssertion
}

run_cmd do
  let mod ← getCurrentModule
  let results ← Verifier.waitFilteredSync VCMetadata.isTrace
  let some model := results.vcs.findSome? (fun vc => vc.timing.dischargers.findSome? (fun d => match d.result with
    | some (.proven _ (some (.sat models)) _) => models.findSome? id | _ => none)) | throwError "missing model"
  liftTermElabM do
    let (_, replay) ← mkTraceQuery mod (← `(traceSpec|
      $(mkIdent `choose):ident
      assert contextualAssertion))
    let findKey (name : Name) := do
      let some (k, _) ← model.raw.values.findM? (fun (k, _) => do
        return (← getExprName model.raw.ctx k).bind modelBinderKey? == some name)
        | throwError "missing model assignment {name}"
      return k
    let preKey ← findKey `st0.count
    let postKey ← findKey `st1.count
    let mutate (pre post : Int) := { model.raw with values := model.raw.values.map fun (k, v) =>
      (k, if k == preKey then toExpr pre else if k == postKey then toExpr post else v) }
    for pre in [:4] do
      for post in [:4] do
        let witness ← buildTraceFromModel (mutate pre post) mod 1
        let actual ← replay.check witness
        let expected := if pre == 0 && post == 1 then WitnessCheck.checked else .invalid
        unless actual == expected do throwError "{pre} → {post}: expected {repr expected}, got {repr actual}"
    -- These paths are both legal and visit the same three states in different orders.
    let (_, checkpoint) ← mkTraceQuery mod (← `(traceSpec|
      any action
      assert contextualAssertion
      any action))
    for (mid, last, expected) in [(1, 2, WitnessCheck.checked), (2, 1, .invalid)] do
      let w ← buildTraceFromModel (mutate 0 mid) mod 1
      let finalStep := (← buildTraceFromModel (mutate mid last) mod 1).steps[0]!
      let actual ← checkpoint.check { w with steps := w.steps.push finalStep }
      unless actual == expected do throwError "checkpoint at {mid}: expected {repr expected}, got {repr actual}"
    let negative := mutate (-1) 1
    if (← observing? (buildTraceFromModel negative mod 1)).isSome then
      throwError "decoded a negative Nat as a valid initial state"
    let tag ← findKey (traceTagName 1)
    let values := model.raw.values.filter (·.1 != tag)
    if (← observing? (buildTraceFromModel { model.raw with values } mod 1)).isSome then
      throwError "decoded an action without its tag"

-- An action with no possible arguments cannot prevent another action from firing.
#guard_msgs (drop info) in
sat trace [anyEnabled] { any action }
run_cmd do
  let results ← Verifier.waitFilteredSync VCMetadata.isTrace
  let some vc := results.vcs.find? (fun vc => match vc.metadata with
    | .trace md => md.traceName == some `anyEnabled | _ => false) | throwError "missing any-action query"
  unless vc.status == some .proven do throwError "an inactive branch blocked the enabled action"
end TraceReplayFidelity
