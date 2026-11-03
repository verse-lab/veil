module

public meta import Veil.Core.Tools.Verifier.Server

public meta section
namespace VeilTest.VerifierObserver
open Lean Elab Command Veil Veil.Verifier

abbrev Mgr := VCManager VCMetadata SmtResult

private def diagnostic (name : String) : BaseIO Language.Snapshot.Diagnostics :=
  Language.Snapshot.Diagnostics.ofMessageLog <| MessageLog.empty.add {
    fileName := "observer-test", pos := ⟨1, 0⟩, data := m!"{name} diagnostic"
  }

def tree (name : String) (children : Array (Language.SnapshotTask Language.SnapshotTree) := #[])
    : BaseIO Language.SnapshotTree := do
  let trace : TraceElem := {
    ref := .missing
    msg := .trace { cls := `veil.observerTest, startTime := 1, stopTime := 2 }
      m!"{name} profile" #[] }
  return {
    element := {
      desc := name
      diagnostics := ← diagnostic name
      traces := { tid := 41, traces := ({} : PersistentArray TraceElem).push trace }
    }
    children
  }

def worker (mgr : Mgr) (vcId dischargerId : Nat) (name : Name)
    (task : SnapshotTreeTask) : BaseIO (Discharger SmtResult) := do
  let cancelTk ← IO.CancelToken.new
  let startTimePromise ← IO.Promise.new
  startTimePromise.resolve 0
  let resultPromise ← IO.Promise.new
  resultPromise.resolve (.unknown none 0)
  return {
    id := { managerId := mgr._managerId, vcId, dischargerId, name }
    cancelTk, task := some task, startTimePromise, resultPromise, mkTask := pure task
  }

def data (name : Name) : CommandElabM (VCData VCMetadata) := do
  return { name, params := #[], statement := ← `(True), metadata := .induction { (default : InductionVCMetadata) with property := name } }

def matching (name : Name) (metadata : VCMetadata) : Bool := metadata.propertyName? == some name

def awaitTask (name : String) (task : Task α) (timeout : Nat := 10000) : IO (Option α) := do
  let deadline := (← IO.monoMsNow) + timeout
  while !(← IO.hasFinished task) do
    if (← IO.monoMsNow) > deadline then
      IO.println s!"bounded guard: {name} did not terminate"
      return none
    IO.sleep 1
  return some (← IO.wait task)

end VeilTest.VerifierObserver
