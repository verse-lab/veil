module

public meta import Lean

/-! Run-local, observational progress for invariant synthesis. No search decision or proof
depends on this state. A missing reference makes reporting a no-op (the command-line default). -/

public meta section

namespace Veil.Synthesizer.Progress

inductive Status where
  | running | finished | stopped | failed | cancelled
deriving BEq, Inhabited, Repr

structure Snapshot where
  moduleName : Lean.Name
  status : Status := .running
  phase : String := "Preparing"
  activity : String := "Reading the module vocabulary"
  lastEvent : String := ""
  result : String := ""
  startedAt : Nat
  finishedAt : Option Nat := none
  queryStartedAt : Option Nat := none
  queriesStarted : Nat := 0
  queriesFinished : Nat := 0
  queryMs : Nat := 0
  fuel : Nat
  frameSizes : Array Nat := #[]
  candidates : Nat := 0
  admitted : Nat := 0
  obligationsDone : Nat := 0
  obligationsTotal : Nat := 0
deriving Inhabited

abbrev Ref := IO.Ref Snapshot

def create (moduleName : Lean.Name) (fuel : Nat) : BaseIO Ref := do
  IO.mkRef { moduleName, fuel, startedAt := ← IO.monoMsNow }

/-- Terminal states cannot be overwritten by a late update from an abandoned run. -/
def update (ref? : Option Ref) (f : Snapshot → Snapshot) : BaseIO Unit :=
  ref?.forM fun ref => ref.modify fun s => if s.status == .running then f s else s

def activity (ref? : Option Ref) (text : String) : BaseIO Unit :=
  update ref? fun s => { s with activity := text }

def beginQuery (ref? : Option Ref) : BaseIO Unit := do
  let now ← IO.monoMsNow
  update ref? fun s => { s with
    queryStartedAt := some now
    queriesStarted := s.queriesStarted + 1 }

def endQuery (ref? : Option Ref) : BaseIO Unit := do
  let now ← IO.monoMsNow
  update ref? fun s => { s with
    queryStartedAt := none
    queriesFinished := s.queriesFinished + 1
    queryMs := s.queryMs + (s.queryStartedAt.map (now - ·)).getD 0 }

def beginCertificate (ref? : Option Ref) (total : Nat) : BaseIO Unit :=
  update ref? fun s => { s with
    phase := "Certifying", activity := "Preparing certificate"
    obligationsDone := 0, obligationsTotal := total }

def completeObligation (ref? : Option Ref) : BaseIO Unit :=
  update ref? fun s => { s with obligationsDone := s.obligationsDone + 1 }

def finish (ref? : Option Ref) (status : Status) (result : String) : BaseIO Unit := do
  let now ← IO.monoMsNow
  update ref? fun s => { s with
    status, result, finishedAt := some now
    queryMs := s.queryMs + (s.queryStartedAt.map (now - ·)).getD 0
    queryStartedAt := none }

end Veil.Synthesizer.Progress
