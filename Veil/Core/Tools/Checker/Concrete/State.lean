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

#check VeilM
def getAllStatesFromExceptT (c : List (ExceptT ε DivM (α × σ))) : List (Option σ) :=
  c.map getStateFromExceptT


/- `κ` need [Repr] instance, which is used in log -/
variable [Repr κ]
/- `σᵣ` need [Repr] instance, which is used in log -/
variable [Repr σᵣ]
/- `σᵣ` need [Inhabited] instance, which is used in initialization -/
variable [Inhabited σᵣ]
/- `σᵣ` need to be stored in HashSet/TreeSet, requiring [BEq], [Hashable] instances -/
variable [BEq σᵣ] [Hashable σᵣ]
variable [IsSubStateOf ℂ σᵣ] [IsSubReaderOf ℝ ρ]
/- Corresponds to `after_init` action, used for initialization -/
variable (initVeilMultiExecM : VeilMultiExecM κᵣ ℤ ρ σᵣ Unit)
/- Corresponds to `action` -/
variable (nextVeilMultiExecM : κ → VeilMultiExecM κᵣ ℤ ρ σᵣ Unit)
/- All possible labels -/
variable (allLabels : List κ)
/- Invariant to be checked -/
variable (INV : ρ → σᵣ → Prop)
variable [dec_inv: ∀rd : ρ, ∀st : σᵣ, Decidable (INV rd st)]


abbrev TsilE (κᵣ σᵣ : Type) := TsilT (ExceptT ℤ (PeDivM (List κᵣ))) (Unit × σᵣ)
/- Initialization, usually s₀ is a __default__ value from [Inhabited]. -/
def afterInit (rd : ρ) (s₀ : σᵣ) : TsilE κᵣ σᵣ :=
  ((initVeilMultiExecM |> ReaderT.run) rd |> StateT.run) s₀

/- Get all possible next states from current state `s` under label `l`. -/
def nonDetNexts (rd : ρ) (st : σᵣ) (l : κ) : TsilE κᵣ σᵣ :=
  nextVeilMultiExecM l rd st


open CheckerM in
def BFSAlgorithmx (st₀ : σᵣ) (rd : ρ) : StateT (SearchContext σᵣ σᵣ) Id Unit := do
  addToSeen st₀
  enqueueState st₀
  while true do
    let .some st := (← dequeueState)
      | return ()
    for label in allLabels do
      let execs := nonDetNexts nextVeilMultiExecM rd st label
      let succs := getAllStatesFromExceptT (execs.map fun ⟨_, s⟩ => s)
      for succ? in succs do
        let .some st' := succ?
          | continue  -- divergence
        unless (← wasSeen st') do
          addToSeen st'
          addTransitionToLog st st' s!"{repr label}"
          if decide (INV rd st') then
            enqueueState st' -- f true /- decide (restrictions rd st') -/ then
          else
            addCounterExample st'
            return ()

open CheckerM in
def BFSAlgorithmx' (st₀ : σᵣ) (rd : ρ) : StateT (SearchContext σᵣ σᵣ) Id Unit := do
  -- (restrictions : ρ → σᵣ → Bool)
  addToSeen st₀
  -- CheckerM.addToSeen (hash st₀)
  enqueueState st₀
  let mut count := 1
  let mut search_continue := true
  while search_continue do
    -- invariant search_continue do
    let current_state_opt ← CheckerM.dequeueState
    match current_state_opt with
    | none =>
      -- dbg_trace "[BFS] explored all states, total {count}"
      search_continue := false
      return ()
    | some st =>
      -- let canMoveLabels := canMoveLabel rd st
      let canMoveLabels := allLabels
      for i in List.finRange canMoveLabels.length do
        match canMoveLabels[i]? with
        | none =>
          -- dbg_trace "[BFS] explored all states, total {count}"
          continue
        | some label =>
          let list_st'_opt := getAllStatesFromExceptT ((nonDetNexts nextVeilMultiExecM rd st label).map Prod.snd)
          -- dbg_trace "[BFS] {list_st'_opt.length} successors for label {reprStr label}"
          -- let mut print_flag := false
          for st'_opt in list_st'_opt do
            match st'_opt with
            | none =>
              -- dbg_trace "[BFS] divergence encountered, {reprStr label}"
              continue   -- divergence
            | some st' =>
              -- dbg_trace "[BFS] Current State: {reprStr st}"
              let already_seen ← CheckerM.wasSeen st'
              -- let already_seen ← CheckerM.wasSeen (hash st')
              if !already_seen then
                CheckerM.addToSeen st'
                CheckerM.addTransitionToLog st st' s!"{reprStr label}"
                if decide (INV rd st') then
                  if true /- decide (restrictions rd st') -/ then
                    CheckerM.enqueueState st'
                else
                  -- CheckerM.addCounterExample (hash st')
                  CheckerM.addCounterExample st'
                  -- dbg_trace "[BFS] invariant violated after {count} states explored, on label {reprStr label}"
                  search_continue := false
                  return ()

-- open PartialCorrectness DemonicChoice in
-- lemma test_lemma (st₀ : σᵣ) (rd : ρ) (restrictions : ρ → σᵣ → Bool) :
--     ∀ balanceOld : Bal,
--       triple
--       (fun balance : Bal => (balance = balanceOld) ∧ True)
--         (BFSAlgorithmx nextVeilMultiExecM allLabels INV st₀ rd)
--       (fun u => fun balance : Bal => with_name_prefix`ensures balance + amounts.sum = balanceOld) :=
--   by
--   unfold withdrawSession
--   -- loom_solve!
--   all_goals
--     try loom_solve


/-- Run BFS starting from `st₀` with reader `rd`, checking `INV` under `restrictions`. -/
def runModelCheckerx (rd : ρ) : Id (Unit × (SearchContext σᵣ σᵣ)) := do
  let cfg := SearchContext.empty
  let restrictions := (fun (_ : ρ) (_ : σᵣ) => true)
  let st₀ := (((afterInit initVeilMultiExecM rd default |>.map Prod.snd).map getStateFromExceptT)[0]!).getD default
  (BFSAlgorithmx nextVeilMultiExecM allLabels INV st₀ rd) |>.run cfg


def runModelCheckerxx (rd : ρ) : Id (Unit × (SearchContext σᵣ σᵣ)) := do
  let cfg := SearchContext.empty
  let restrictions := (fun (_ : ρ) (_ : σᵣ) => true)
  let st₀ := (((afterInit initVeilMultiExecM rd default |>.map Prod.snd).map getStateFromExceptT)[0]!).getD default
  (BFSAlgorithmx' nextVeilMultiExecM allLabels INV st₀ rd) |>.run cfg
