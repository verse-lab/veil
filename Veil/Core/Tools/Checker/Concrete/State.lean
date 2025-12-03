import Veil.Frontend.DSL.State.SubState
import Veil.Frontend.DSL.Action.Semantics.Definitions
import Veil.Core.Tools.Checker.Concrete.DataStructure
-- import Veil.Core.Tools.Checker.Concrete.Datas

open Veil

variable {ℂ ℝ 𝔸: Type}
/-
- `κᵣ` :  set as Std.Format by default
- `κ`  :  State.Label
- `ρ`  :  Reader type
- `σᵣ` :  Concrete state representation type
-/
variable {κ κᵣ ρ σᵣ α: Type}
variable {ε σ: Type}

/-- Extract the resulting state from an ExceptT-wrapped execution, if successful. -/
def getStateFromExceptT (c : ExceptT ε DivM (α × σ)) : Option σ :=
  match c.run with
  | .res (.ok (_, st)) => .some st
  | .res (.error _)    => .none
  | .div => none

def getAllStatesFromExceptT (c : List (ExceptT ε DivM (α × σ))) : List (Option σ) :=
  c.map getStateFromExceptT

/-- Extract all valid states from a VeilMultiExecM computation -/
def extractValidStates (exec : VeilMultiExecM κᵣ ℤ ρ σᵣ Unit) (rd : ρ) (st : σᵣ) : List (Option σᵣ) :=
  exec rd st |>.map Prod.snd |> getAllStatesFromExceptT

/- Corresponds to `after_init` action, used for initialization -/
variable (initVeilMultiExecM : VeilMultiExecM κᵣ ℤ ρ σᵣ Unit)
variable (nextVeilMultiExecM : κ → VeilMultiExecM κᵣ ℤ ρ σᵣ Unit)

abbrev TsilE (κᵣ σᵣ : Type) := TsilT (ExceptT ℤ (PeDivM (List κᵣ))) (Unit × σᵣ)

def afterInit (rd : ρ) (s₀ : σᵣ) : TsilE κᵣ σᵣ :=
  ((initVeilMultiExecM |> ReaderT.run) rd |> StateT.run) s₀

/- Get all possible next states from current state `s` under label `l`. -/
def nonDetNexts (rd : ρ) (st : σᵣ) (l : κ) : TsilE κᵣ σᵣ :=
  nextVeilMultiExecM l rd st

def adjExec (rd : ρ) (st : σᵣ) (l : κ) :=
  let execs := nextVeilMultiExecM l rd st
  let succs := getAllStatesFromExceptT (execs.map Prod.snd)
  succs


/-
We do not require `Repr` instances for `σᵣ` and `κ` here, aimming to
seperate the concerns of model checking algorithm and representation.

`σₛ` is the type fingerprint, used for storage.
`σₛ` is usually in HashSet, which requires `Ord` and `Hashable` instance.

`σᵣ` need `Inhabited` instance, which is used in initialization.

TODO: If we hope to allow use `symmetric reduction`, then `σᵣ` requires
`Ord` instance, to make it comparable between each other.
-/
variable [Inhabited σᵣ]
variable {σₛ : Type}
variable [BEq σₛ] [Hashable σₛ]
variable (allLabels : List κ)
variable (INV : ρ → σᵣ → Prop)
variable (Terminate : ρ → σᵣ → Prop)
variable [dec_inv: ∀rd : ρ, ∀st : σᵣ, Decidable (INV rd st)]
variable [dec_term: ∀rd : ρ, ∀st : σᵣ, Decidable (Terminate rd st)]
variable [IsSubStateOf ℂ σᵣ]
variable [IsSubReaderOf ℝ ρ]

open CheckerM in
partial def bfsSearch (rd : ρ) (view : σᵣ → σₛ) : StateT (SearchContext σᵣ σₛ κ) Id Unit := do
  while true do
    let .some (st, fpSt) := (← dequeueState) | return ()
    let mut hasSuccessor := false
    for label in allLabels do
      let succs := extractValidStates (nextVeilMultiExecM label) rd st
      for succ? in succs do
        let .some st' := succ? | continue
        hasSuccessor := true
        let fingerprint := view st'
        unless (← wasSeen fingerprint) do
          addToSeen fingerprint
          addTransitionToLog fpSt fingerprint label
          if decide (INV rd st') then
            enqueueState st' fingerprint
          else
            addCounterExample fingerprint
            return ()
    -- Deadlock: no successors and state is not terminating
    if !hasSuccessor && !decide (Terminate rd st) then
      addCounterExample fpSt
      return ()


/-- Run BFS model checker starting from initial states, checking invariant `INV` -/
def runModelCheckerx (rd : ρ) (view : σᵣ → σₛ) : Id (Unit × (SearchContext σᵣ σₛ κ)) := do
  let mut cfg := SearchContext.empty
  -- Initialize with all valid initial states
  for st₀ in extractValidStates initVeilMultiExecM rd default |>.filterMap id do
    let fingerprint := view st₀
    cfg := {cfg with seen := cfg.seen.insert fingerprint }
    if decide (INV rd st₀) then
      cfg := {cfg with sq := cfg.sq.enqueue (st₀, fingerprint) }
    else
      return ((), {cfg with counterexample := [fingerprint] })
  (bfsSearch nextVeilMultiExecM allLabels INV Terminate rd view) |>.run cfg


open CheckerM in
def recoverTrace [Hashable σᵣ] [Repr κ] (rd : ρ) (traces : List (Trace UInt64 κ)) : Trace σᵣ κ := Id.run do
  if traces.isEmpty then
    return { start := default, steps := [] }
  /- Actually, we can assert that there is only one trace returned by `collectTrace.`
  Because when encounter counterexample, the model checker will terminate at once.-/
  let trace := traces[0]!
  let findByHash (succs : List (Option σᵣ)) (targetHash : UInt64) (fallback : σᵣ) : σᵣ :=
    succs.filterMap id |>.find? (fun s => hash s == targetHash) |>.getD fallback
  -- Recover initial state
  let initSuccs := extractValidStates initVeilMultiExecM rd default
  let start := findByHash initSuccs trace.start default
  -- Recover trace steps
  let mut curSt := start
  let mut steps : List (Step σᵣ κ) := []
  for step in trace.steps do
    let succs := extractValidStates (nextVeilMultiExecM step.label) rd curSt
    let nextSt := findByHash succs step.next curSt
    curSt := nextSt
    steps := steps.append [{ label := step.label, next := nextSt }]

  return { start := start, steps := steps }
