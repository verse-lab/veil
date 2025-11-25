import Veil.Frontend.DSL.Infra.State
import Veil.Frontend.DSL.Action.Semantics.Definitions
import Veil.Core.Tools.Checker.Concrete.DataStructure
import Veil.Frontend.DSL.Action.Extraction.Basic

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


def DivM.run (a : DivM α) : Option α :=
  match a with
  | .res x => .some x
  | .div => .none

/-- Extract the resulting state from an ExceptT-wrapped execution, if successful. -/
def getStateFromExceptT (c : ExceptT ε DivM (α × σ)) : Option σ :=
  match c.run with
  | .res (.ok (_, st)) => .some st
  | .res (.error _)    => .none
  | .div => none

def getAllStatesFromExceptT (c : List (ExceptT ε DivM (α × σ))) : List (Option σ) :=
  c.map getStateFromExceptT

/- Corresponds to `after_init` action, used for initialization -/
variable (initVeilMultiExecM : VeilMultiExecM κᵣ ℤ ρ σᵣ Unit)
variable (nextVeilMultiExecM : κ → VeilMultiExecM κᵣ ℤ ρ σᵣ Unit)
abbrev TsilE (κᵣ σᵣ : Type) := TsilT (ExceptT ℤ (PeDivM (List κᵣ))) (Unit × σᵣ)

def afterInit (rd : ρ) (s₀ : σᵣ) : TsilE κᵣ σᵣ :=
  ((initVeilMultiExecM |> ReaderT.run) rd |> StateT.run) s₀

/- Get all possible next states from current state `s` under label `l`. -/
def nonDetNexts (rd : ρ) (st : σᵣ) (l : κ) : TsilE κᵣ σᵣ :=
  nextVeilMultiExecM l rd st



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
partial def bfsSearch (st₀ : σᵣ) (rd : ρ) (view : σᵣ → σₛ)
: StateT (SearchContext σᵣ σₛ κ) Id Unit := do
  let fpSt₀ := view st₀
  addToSeen fpSt₀
  enqueueState st₀ fpSt₀
  while true do
    let .some (st, fpSt) := (← dequeueState) | return ()
    let mut emptyflag := true
    for label in allLabels do
      let execs := nonDetNexts nextVeilMultiExecM rd st label
      let succs := getAllStatesFromExceptT (execs.map Prod.snd)
      for succ? in succs do
        emptyflag := false
        let .some st' := succ? | continue -- divergence
        let fingerprint := view st'
        unless (← wasSeen fingerprint) do
          addToSeen fingerprint
          addTransitionToLog fpSt fingerprint label
          if decide (INV rd st') then
            enqueueState st' fingerprint
          else
            addCounterExample fingerprint
            return ()
    /- If there are no successors and `st` is not terminating, then this is a deadlock -/
    if emptyflag && !decide (Terminate rd st) then
      addCounterExample fpSt
      return ()


/-- Run BFS starting from `st₀` with reader `rd`, checking `INV` under `restrictions`. -/
def runModelCheckerx (rd : ρ) (view : σᵣ → σₛ) : Id (Unit × (SearchContext σᵣ σₛ κ)) := do
  let cfg := SearchContext.empty
  let restrictions := (fun (_ : ρ) (_ : σᵣ) => true)
  let st₀ := (((afterInit initVeilMultiExecM rd default |>.map Prod.snd).map getStateFromExceptT)[0]!).getD default
  (bfsSearch nextVeilMultiExecM allLabels INV Terminate st₀ rd view) |>.run cfg

open CheckerM in
def recoverTrace (rd : ρ) (linearLabels : List κ) [Repr κ] : Trace σᵣ κ := Id.run do
  if linearLabels.isEmpty then
    return { start := default, steps := [] }
  let st₀ := (((afterInit initVeilMultiExecM rd default |>.map Prod.snd).map getStateFromExceptT)[0]!).getD default
  let mut steps : List (Step σᵣ κ) := []
  let mut curSt := st₀
  for ll in linearLabels do
    let execs := nonDetNexts nextVeilMultiExecM rd curSt ll
    let succ? := (execs |>.map Prod.snd |>.map getStateFromExceptT)[0]!
    let .some st' := succ? | assert! false
    steps := steps.append [{ label := ll, next := st' }]
    curSt := st'
  let tr : Trace σᵣ κ := { start := st₀, steps := steps }
  return tr
