module

public import Veil
public import Veil.Core.Tools.Synthesizer

open Lean Elab Command Veil.Synthesizer

/-! Progress belongs to one run and cannot resurrect after cancellation. Hiding the panel must
not freeze the state used when it is reopened. -/

run_cmd do
  let first ← Progress.create `First 10
  let second ← Progress.create `Second 20
  Progress.beginQuery (some first)
  let now ← IO.monoMsNow
  first.modify fun s => { s with queryStartedAt := some (now - 500) }
  Progress.finish (some first) .cancelled "Cancelled during a query"
  let finished ← first.get
  unless finished.queryMs ≥ 500 do throwError "cancellation lost in-flight query time"
  Progress.endQuery (some first)
  Progress.finish (some first) .finished "Late success"
  Progress.activity (some first) "Late update"
  let after ← first.get
  unless after.status == .cancelled && after.queryMs == finished.queryMs &&
      after.result == finished.result do
    throwError "a late update overwrote the cancelled result"
  unless (← second.get).queriesStarted == 0 do throwError "progress leaked between runs"

private meta partial def htmlText : ProofWidgets.Html → String
  | .text text => text
  | .element _ _ children | .component _ _ _ children =>
    String.intercalate " " (children.toList.map htmlText)

private meta def awaitDisplay (token : ProofWidgets.RefreshToken)
    (text : String) : IO Unit := do
  let started ← IO.monoMsNow
  repeat
    let html := (← token.state.get).curr.get
    if ((htmlText html).splitOn text).length > 1 then return
    if (← IO.monoMsNow) - started > 3000 then
      throw <| IO.userError s!"display did not update to {text}"
    IO.sleep 10

run_cmd do
  let ref ← Progress.create `Remount 10
  let (_, token) ← ProofWidgets.mkRefreshComponent
  let cancel ← IO.CancelToken.new
  let task ← BaseIO.asTask (prio := .dedicated) (Progress.refresh ref (some cancel) token)
  try
    awaitDisplay token "Preparing"
    -- ProofWidgets sets this token when a panel unmounts. Its state must keep updating
    -- so a subsequent mount, which starts at version zero, sees current progress.
    token.cancelTk.set
    Progress.activity (some ref) "Still searching after remount"
    awaitDisplay token "Still searching after remount"
    cancel.set
    awaitDisplay token "Cancelled"
    unless (← ref.get).status == .cancelled do throwError "command cancellation was not observed"
  finally
    Progress.finish (some ref) .finished "Display test completed"
    discard <| IO.wait task

veil module SynthesisProgressTest

individual ready : Bool
#gen_state
after_init { ready := true }
action stay { ready := true }
safety [is_ready] ready
#gen_spec

run_cmd do
  let mod ← Veil.getCurrentModule
  let progress ← Progress.create mod.name 100
  let cfg : Config := { fuel := 100, progress? := some progress }
  let result ← liftTermElabM do
    synthesize mod cfg (← Signature.ofModule mod)
  let .foundInvariant _ clauses _ := result.outcome | throwError "expected an invariant"
  let snapshot ← progress.get
  unless snapshot.queriesFinished == result.stats.solverCalls &&
      snapshot.queriesStarted == snapshot.queriesFinished && snapshot.queryStartedAt.isNone &&
      !snapshot.frameSizes.isEmpty do
    throwError "search progress disagrees with the actual run"
  let cert ← certify mod (← liftCoreM <| checkedProperty mod cfg) (clauses.map (·.clause))
    (some progress)
  let snapshot ← progress.get
  unless snapshot.obligationsTotal > 0 &&
      snapshot.obligationsDone == snapshot.obligationsTotal && cert.kernelChecked do
    throwError "certificate progress did not finish its obligations"

-- The preceding synchronous command must have installed the theorem in this environment.
example := SynthesisProgressTest.ic3_safe

/-- info: 'SynthesisProgressTest.ic3_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SynthesisProgressTest.ic3_safe

end SynthesisProgressTest
