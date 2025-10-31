import Veil.Frontend.DSL.Infra.State
import Veil.Frontend.DSL.Action.Semantics.Definitions
import Veil.Core.Tools.Checker.Concrete.DataStructure
import Veil.Frontend.DSL.Action.Extraction.Basic


import Loom.MonadAlgebras.Instances.StateT
import Loom.MonadAlgebras.Instances.ExceptT
-- import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Lean

-- import CaseStudies.Cashmere.Syntax_Cashmere
import Loom.MonadAlgebras.WP.Tactic
open Lean.Elab.Term.DoNames
open ExceptionAsFailure

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
abbrev TsilE (κᵣ σᵣ : Type) := TsilT (ExceptT ℤ (PeDivM (List κᵣ))) (Unit × σᵣ)
/- Initialization, usually s₀ is a __default__ value from [Inhabited]. -/
def afterInit (rd : ρ) (s₀ : σᵣ) : TsilE κᵣ σᵣ :=
  ((initVeilMultiExecM |> ReaderT.run) rd |> StateT.run) s₀


/- Corresponds to `action` -/
variable (nextVeilMultiExecM : κ → VeilMultiExecM κᵣ ℤ ρ σᵣ Unit)
/- Get all possible next states from current state `s` under label `l`. -/
def nonDetNexts (rd : ρ) (st : σᵣ) (l : κ) : TsilE κᵣ σᵣ :=
  nextVeilMultiExecM l rd st

class MonadWasSeen (β : Type) (m : Type → Type u) where
  wasSeen : β → m Bool


/- `σₛ` is the type fingerprint, used for storage. -/
variable {σₛ : Type}
variable [Inhabited σₛ]
variable [BEq σₛ] [Hashable σₛ]

/- All possible labels -/
variable (allLabels : List κ)
/- Invariant to be checked -/
variable (INV : ρ → σᵣ → Prop)
variable [dec_inv: ∀rd : ρ, ∀st : σᵣ, Decidable (INV rd st)]
/- `κ` need [Repr] instance, which is used in log -/
variable [Repr κ]
/- `σᵣ` need [Repr] instance, which is used in log -/
variable [Repr σᵣ]
/- `σᵣ` need [Inhabited] instance, which is used in initialization -/
variable [Inhabited σᵣ]
variable [IsSubStateOf ℂ σᵣ] [IsSubReaderOf ℝ ρ]

open CheckerM in
partial def bfsSearch (st₀ : σᵣ) (rd : ρ) (view : σᵣ → σₛ) : StateT (SearchContext σᵣ σₛ) Id Unit := do
  let fpSt₀ := view st₀
  addToSeen fpSt₀
  enqueueState st₀ fpSt₀
  while true do
    let .some (st, fpSt) := (← dequeueState) | return ()
    for label in allLabels do
      -- dbg_trace s!"Exploring label: {repr label}"
      let execs := nonDetNexts nextVeilMultiExecM rd st label
      -- dbg_trace s!"received {(execs.length)} successors"
      let succs := getAllStatesFromExceptT (execs.map Prod.snd)
      for succ? in succs do
        let .some st' := succ? | continue -- divergence
        -- dbg_trace s!"Exploring state after executing {repr label}: {repr st'}"
        let fingerprint := view st'
        unless (← wasSeen fingerprint) do
          addToSeen fingerprint
          addTransitionToLog fpSt fingerprint s!"{repr label}"
          if decide (INV rd st') then
            enqueueState st' fingerprint
          else
            addCounterExample fingerprint
            return ()

/-- Run BFS starting from `st₀` with reader `rd`, checking `INV` under `restrictions`. -/
def runModelCheckerx (rd : ρ) (view : σᵣ → σₛ) : Id (Unit × (SearchContext σᵣ σₛ)) := do
  let cfg := SearchContext.empty
  let restrictions := (fun (_ : ρ) (_ : σᵣ) => true)
  let st₀ := (((afterInit initVeilMultiExecM rd default |>.map Prod.snd).map getStateFromExceptT)[0]!).getD default
  -- dbg_trace s!"Initial state: {repr st₀}"
  (bfsSearch nextVeilMultiExecM allLabels INV st₀ rd view) |>.run cfg
