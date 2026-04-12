import Veil.Core.Tools.ModelChecker.Interface
import Veil.Core.Tools.ModelChecker.Trace
import Veil.Core.Tools.ModelChecker.Concrete.Core
import Veil.Core.Tools.ModelChecker.Concrete.Progress

namespace Veil.ModelChecker.Simulation
open Veil.ModelChecker.Concrete

/-- Configuration for the `#simulate` command. -/
structure SimulateConfig where
  maxTraces : Nat := 10000
  maxSteps : Nat := 100
  seed : Nat := 0
deriving Inhabited, Repr

/-- Result of a simulation run, wrapping a `ModelCheckingResult` with metadata. -/
structure SimulateResult (ρ σ κ : Type) where
  result : ModelCheckingResult ρ σ κ Unit
  tracesRun : Nat
  elapsedMs : Nat
  seed : Nat
  depth : Nat

/-- Return names of invariants violated in the given state. -/
@[inline]
def violatedInvariantNames {ρ σ : Type}
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) : List Lean.Name :=
  params.invariants.filterMap fun p =>
    if !p.holdsOn th st then some p.name else none

/-- Filter initial states according to the search parameters' state constraints. -/
@[inline]
def filterInitStatesByConstraints {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) : List σ :=
  if params.stateConstraints.isEmpty then
    sys.initStates
  else
    sys.initStates.filter (params.satisfiesConstraints th)

/-- Filter transition outcomes according to the search parameters' state constraints.
Successful and assertion-failure outcomes whose post-state violates a state
constraint are silently skipped, matching `Concrete.findReachable`. -/
@[inline]
def filterOutcomesByConstraints {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) : List (κ × ExecutionOutcome Int σ) :=
  if params.stateConstraints.isEmpty then
    sys.tr th st
  else
    (sys.tr th st).filter fun (_, outcome) =>
      match outcome with
      | .success st' => params.satisfiesConstraints th st'
      | .assertionFailure _ st' => params.satisfiesConstraints th st'
      | .divergence => true

/-- Relational view of simulation semantics: initial states and successful
transitions filtered by the configured state constraints. -/
def simulationTransitionSystem {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) : RelationalTransitionSystem ρ σ κ where
  assumptions := fun _ => True
  init := fun th st => st ∈ filterInitStatesByConstraints sys params th
  tr := fun th st label st' =>
    (label, ExecutionOutcome.success st') ∈ filterOutcomesByConstraints sys params th st

/-- Boolean check that a concrete step list follows successful constrained
simulation transitions. Used as the decision procedure for simulation soundness. -/
def StepList.validFromSimulation {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) : StepList σ κ → Bool
  | [] => true
  | step :: steps =>
      (filterOutcomesByConstraints sys params th st).any fun (label, outcome) =>
        match outcome with
        | .success st' => label == step.transitionLabel && st' == step.nextState
        | _ => false
      && StepList.validFromSimulation sys params th step.nextState steps

/-- Boolean validity check for simulation traces, matching the constrained
search semantics used by `#simulate`. -/
def Trace.isSimulationValidB {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) : Bool :=
  (filterInitStatesByConstraints sys params trace.theory).contains trace.initialState &&
  StepList.validFromSimulation sys params trace.theory trace.initialState trace.steps.toList

/-- Validity predicate for simulation traces, matching the constrained search
semantics used by `#simulate`. -/
abbrev Trace.isSimulationValid {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) : Prop :=
  Trace.isSimulationValidB sys params trace = true

instance instDecidableTraceIsSimulationValid {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) :
  Decidable (Trace.isSimulationValid sys params trace) := by
  unfold Trace.isSimulationValid
  infer_instance

/-- Boolean checker used to decide whether a trace witnesses a simulation
violation; the exported theorem remains Prop-level. -/
def Trace.witnessesSimulationViolationB {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) : ViolationKind → Bool
  | .safetyFailure violates =>
      Trace.isSimulationValidB sys params trace &&
      trace.failingStep.isNone &&
      decide (violatedInvariantNames params trace.theory trace.lastState = violates) &&
      !violates.isEmpty
  | .deadlock =>
      Trace.isSimulationValidB sys params trace &&
      trace.failingStep.isNone &&
      !params.terminating.holdsOn trace.theory trace.lastState &&
      let (nexts, _) := partitionExecutionOutcome
        (filterOutcomesByConstraints sys params trace.theory trace.lastState)
      nexts.isEmpty
  | .assertionFailure exId =>
      match trace.failingStep with
      | some step =>
          Trace.isSimulationValidB sys params trace &&
          (filterOutcomesByConstraints sys params trace.theory trace.lastState).contains
            (step.transitionLabel, ExecutionOutcome.assertionFailure exId step.nextState)
      | none => false

/-- A concrete trace witnesses a particular simulation violation. -/
abbrev Trace.witnessesSimulationViolation {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) (violation : ViolationKind) : Prop :=
  Trace.witnessesSimulationViolationB sys params trace violation = true

def ResultSoundB {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (result : ModelCheckingResult ρ σ κ Unit) : Bool :=
  match result with
  | .foundViolation _ violation (some trace) => Trace.witnessesSimulationViolationB sys params trace violation
  | .foundViolation _ _ none => false
  | .noViolationFound _ _ => true
  | .cancelled => true

/-- Soundness predicate for `#simulate` results.
Simulation is not complete, so `noViolationFound` carries no proof obligation,
but any reported violation must come with a valid witness trace. -/
def ResultSound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (result : ModelCheckingResult ρ σ κ Unit) : Prop :=
  ResultSoundB sys params result = true

instance instDecidableResultSound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (result : ModelCheckingResult ρ σ κ Unit) :
  Decidable (ResultSound sys params result) := by
  unfold ResultSound
  infer_instance

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
    | .assertionFailure exId st =>
      some (exId, { transitionLabel := label, nextState := st })
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

/-- Lightweight scan loop: walk without building a trace.
Returns `(violated?, updatedRng, stepsTaken)`. -/
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
    | .assertionFailure _ _ =>
        (true, gen, 1)
    | .deadlock =>
        (true, gen, 0)
    | .terminated =>
        (false, gen, 0)
    | .continue nexts =>
        let ((_, nextSt), gen) := pickNextTransition nexts gen
        if !(violatedInvariantNames params th nextSt).isEmpty then
          (true, gen, 1)
        else
          let (violated, gen, innerSteps) := scanOnceLoop sys params th stepsLeft nextSt gen
          (violated, gen, innerSteps + 1)

/-- Lightweight scan: pick random init state, walk without trace.
Returns `(violated?, updatedRng, stepsTaken)`. -/
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

/-- Inner loop of a single random trace: walk from `currSt` for up to
`stepsLeft` steps, picking a random enabled transition at each step.
Returns `(violation?, updatedRng, stepsTaken)`. Used only for replay. -/
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
        -- +1 for the failing action itself (not in trace.steps, stored in failingStep)
        (some (.foundViolation () (.assertionFailure exId) (some failedTrace)),
          gen, trace.steps.size + 1)
    | .deadlock =>
        (some (.foundViolation () .deadlock (some trace)), gen, trace.steps.size)
    | .terminated =>
        (none, gen, trace.steps.size)
    | .continue nexts =>
        let ((label, nextSt), gen) := pickNextTransition nexts gen
        let trace := trace.push { transitionLabel := label, nextState := nextSt }
        let violations := violatedInvariantNames params th nextSt
        if !violations.isEmpty then
          (some (.foundViolation () (.safetyFailure violations) (some trace)),
            gen, trace.steps.size)
        else
          simulateOnceLoop sys params th stepsLeft nextSt trace gen

/-- Run a single random trace from a randomly chosen initial state.
Returns `(violation?, updatedRng, stepsTaken)`. Used only for replay. -/
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

/-- Pure simulation core for a fixed seed.
Scans without trace recording for speed; replays only the violating trace. -/
@[inline, specialize]
def simulateCoreLoop {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  (remaining : Nat)
  (traceIndex : Nat)
  [Inhabited σ]
  [Inhabited (κ × σ)]
  : SimulateResult ρ σ κ :=
  match remaining with
  | 0 => {
      result := .noViolationFound cfg.maxTraces
        (.earlyTermination (.reachedDepthBound cfg.maxTraces))
      tracesRun := cfg.maxTraces
      elapsedMs := 0
      seed := cfg.seed
      depth := 0
    }
  | remaining + 1 =>
      let traceSeed := cfg.seed + traceIndex
      let (violated, _, stepsUsed) := scanOnce sys params th (mkStdGen traceSeed) cfg.maxSteps
      if violated then
        let (maybeResult, _, _) := simulateOnce sys params th (mkStdGen traceSeed) cfg.maxSteps
        match maybeResult with
        | some result => {
            result := result
            tracesRun := traceIndex + 1
            elapsedMs := 0
            seed := cfg.seed
            depth := stepsUsed
          }
        | none => simulateCoreLoop sys params th cfg remaining (traceIndex + 1)
      else
        simulateCoreLoop sys params th cfg remaining (traceIndex + 1)

/-- Run `maxTraces` independent random traces for a fixed seed.
This function is pure and is the proof-producing core used by `#simulate`. -/
@[inline, specialize]
def simulateCore {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  [inhabσ : Inhabited σ]
  [inhabκσ : Inhabited (κ × σ)]
  : SimulateResult ρ σ κ :=
  simulateCoreLoop sys params th cfg cfg.maxTraces 0

/-- IO simulation runner with progress and cancellation hooks.
Uses the configured seed exactly once and reuses its per-trace derivation scheme. -/
@[inline, specialize]
def simulateWithProgress {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken)
  [inhabσ : Inhabited σ]
  [inhabκσ : Inhabited (κ × σ)]
  : IO (SimulateResult ρ σ κ) := do
  let actualSeed ← if cfg.seed == 0 then IO.rand 0 0xFFFFFFFFFFFFFFFF else pure cfg.seed
  let cfg := { cfg with seed := actualSeed }
  let startMs ← IO.monoMsNow
  let mut tracesRun := 0
  let mut lastStatusUpdate := startMs
  while tracesRun < cfg.maxTraces do
    if ← Veil.ModelChecker.Concrete.shouldStop cancelToken progressInstanceId then
      return {
        result := .cancelled
        tracesRun
        elapsedMs := (← IO.monoMsNow) - startMs
        seed := actualSeed
        depth := 0
      }
    let now ← IO.monoMsNow
    if now - lastStatusUpdate ≥ 100 then
      Veil.ModelChecker.Concrete.updateStatus progressInstanceId s!"Running random traces ({tracesRun}/{cfg.maxTraces})"
      lastStatusUpdate := now
    let traceSeed := cfg.seed + tracesRun
    let (violated, _, stepsUsed) := scanOnce sys params th (mkStdGen traceSeed) cfg.maxSteps
    if violated then
      let (maybeResult, _, _) := simulateOnce sys params th (mkStdGen traceSeed) cfg.maxSteps
      match maybeResult with
      | some result =>
          Veil.ModelChecker.Concrete.setViolationFound progressInstanceId
          return {
            result
            tracesRun := tracesRun + 1
            elapsedMs := (← IO.monoMsNow) - startMs
            seed := actualSeed
            depth := stepsUsed
          }
      | none =>
          tracesRun := tracesRun + 1
    else
      tracesRun := tracesRun + 1
  return {
    result := .noViolationFound cfg.maxTraces (.earlyTermination (.reachedDepthBound cfg.maxTraces))
    tracesRun := cfg.maxTraces
    elapsedMs := (← IO.monoMsNow) - startMs
    seed := actualSeed
    depth := 0
  }

/-- IO wrapper around `simulateCore` that fills in a seed when omitted and records
wall-clock time for UI/reporting. -/
@[inline, specialize]
def simulate {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  [inhabσ : Inhabited σ]
  [inhabκσ : Inhabited (κ × σ)]
  : IO (SimulateResult ρ σ κ) := do
  let cancelToken ← IO.CancelToken.new
  simulateWithProgress sys params th cfg 0 cancelToken

end Veil.ModelChecker.Simulation
