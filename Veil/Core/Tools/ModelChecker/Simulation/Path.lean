import Veil.Core.Tools.ModelChecker.Simulation.Basic
import Veil.Core.Tools.ModelChecker.Concrete.Core

namespace Veil.ModelChecker.Simulation

private inductive StepDecision (σ κ : Type) where
  | assertionFailure (exId : Int) (step : Step σ κ)
  | deadlock
  | terminated
  | continue (nexts : List (κ × σ))

private def decideAtState {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (currSt : σ) : StepDecision σ κ :=
  let outcomes := filterOutcomesByConstraints sys params th currSt
  let failingStep := outcomes.findSome? fun (label, outcome) =>
    match outcome with
    | .assertionFailure exId st => some (exId, { transitionLabel := label, nextState := st })
    | _ => none
  match failingStep with
  | some (exId, step) => .assertionFailure exId step
  | none =>
      let (nexts, _) := Veil.ModelChecker.Concrete.partitionExecutionOutcome outcomes
      if nexts.isEmpty then
        if !params.terminating.holdsOn th currSt then .deadlock else .terminated
      else
        .continue nexts

private def pickNextTransition {σ κ : Type}
  (nexts : List (κ × σ)) (gen : StdGen) [Inhabited (κ × σ)] : (κ × σ) × StdGen :=
  let (idx, gen) := randNat gen 0 (nexts.length - 1)
  (nexts[idx]!, gen)

@[inline, specialize]
partial def scanOnceLoop {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (stepsLeft : Nat)
  (currSt : σ)
  (gen : StdGen)
  [Inhabited (κ × σ)]
  : Bool × StdGen × Nat :=
  match stepsLeft with
  | 0 => (false, gen, 0)
  | stepsLeft + 1 =>
    match decideAtState sys params th currSt with
    | .assertionFailure _ _ => (true, gen, 1)
    | .deadlock => (true, gen, 0)
    | .terminated => (false, gen, 0)
    | .continue nexts =>
        let ((_, nextSt), gen) := pickNextTransition nexts gen
        if !(violatedInvariantNames params th nextSt).isEmpty then
          (true, gen, 1)
        else
          let (violated, gen, innerSteps) := scanOnceLoop sys params th stepsLeft nextSt gen
          (violated, gen, innerSteps + 1)

@[inline, specialize]
partial def scanOnce {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (gen : StdGen)
  (maxSteps : Nat)
  [Inhabited σ]
  [Inhabited (κ × σ)]
  : Bool × StdGen × Nat :=
  let initStates := filterInitStatesByConstraints sys params th
  if initStates.isEmpty then
    (false, gen, 0)
  else
    let (idx, gen) := randNat gen 0 (initStates.length - 1)
    let initSt := initStates[idx]!
    if !(violatedInvariantNames params th initSt).isEmpty then
      (true, gen, 0)
    else
      scanOnceLoop sys params th maxSteps initSt gen

@[inline, specialize]
partial def simulateOnceLoop {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (stepsLeft : Nat)
  (currSt : σ)
  (trace : Trace ρ σ κ)
  (gen : StdGen)
  [Inhabited (κ × σ)]
  : Option (ModelCheckingResult ρ σ κ Unit) × StdGen × Nat :=
  match stepsLeft with
  | 0 => (none, gen, 0)
  | stepsLeft + 1 =>
    match decideAtState sys params th currSt with
    | .assertionFailure exId step =>
        let failedTrace := { trace with failingStep := some step }
        (some (.foundViolation () (.assertionFailure exId) (some failedTrace)), gen, trace.steps.size + 1)
    | .deadlock =>
        (some (.foundViolation () .deadlock (some trace)), gen, trace.steps.size)
    | .terminated =>
        (none, gen, trace.steps.size)
    | .continue nexts =>
        let ((label, nextSt), gen) := pickNextTransition nexts gen
        let trace := trace.push { transitionLabel := label, nextState := nextSt }
        let violations := violatedInvariantNames params th nextSt
        if !violations.isEmpty then
          (some (.foundViolation () (.safetyFailure violations) (some trace)), gen, trace.steps.size)
        else
          simulateOnceLoop sys params th stepsLeft nextSt trace gen

@[inline, specialize]
partial def simulateOnce {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (gen : StdGen)
  (maxSteps : Nat)
  [Inhabited σ]
  [Inhabited (κ × σ)]
  : Option (ModelCheckingResult ρ σ κ Unit) × StdGen × Nat :=
  let initStates := filterInitStatesByConstraints sys params th
  if initStates.isEmpty then
    (none, gen, 0)
  else
    let (idx, gen) := randNat gen 0 (initStates.length - 1)
    let initSt := initStates[idx]!
    let initTrace : Trace ρ σ κ := { theory := th, initialState := initSt, steps := #[] }
    let initViolations := violatedInvariantNames params th initSt
    if !initViolations.isEmpty then
      (some (.foundViolation () (.safetyFailure initViolations) (some initTrace)), gen, 0)
    else
      simulateOnceLoop sys params th maxSteps initSt initTrace gen

def runTraceAtSeed {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  (traceIndex : Nat)
  [Inhabited σ]
  [Inhabited (κ × σ)]
  : Option (ModelCheckingResult ρ σ κ Unit × Nat) :=
  let traceSeed := cfg.seed + traceIndex
  let (violated, _, stepsUsed) := scanOnce sys params th (mkStdGen traceSeed) cfg.maxSteps
  if violated then
    let (maybeResult, _, _) := simulateOnce sys params th (mkStdGen traceSeed) cfg.maxSteps
    maybeResult.map (fun result => (result, stepsUsed))
  else
    none

end Veil.ModelChecker.Simulation
