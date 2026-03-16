import Veil.Core.Tools.ModelChecker.Interface
import Veil.Core.Tools.ModelChecker.Trace
import Veil.Core.Tools.ModelChecker.Concrete.Core

namespace Veil.ModelChecker.Simulation


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
  totalSteps : Nat

/-- Return names of invariants violated in the given state. -/
@[inline]
def violatedInvariantNames {ρ σ : Type}
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) : List Lean.Name :=
  params.invariants.filterMap fun p =>
    if !p.holdsOn th st then some p.name else none


/-- Inner loop of a single random trace: walk from `currSt` for up to
`stepsLeft` steps, picking a random enabled transition at each step.
Returns `(violation?, updatedRng, stepsTaken)`. -/
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
    let outcomes := sys.tr th currSt
    -- Check assertion failures first (highest priority)
    let assertionFailures := outcomes.filterMap fun (_, outcome) =>
      match outcome with
      | .assertionFailure exId _ => some exId
      | _ => none
    match assertionFailures.head? with
    | some exId =>
      let failingStep := outcomes.findSome? fun (label, outcome) =>
        match outcome with
        | .assertionFailure exId' st =>
          if exId' == exId then some { transitionLabel := label, nextState := st } else none
        | _ => none
      let failedTrace := { trace with failingStep := failingStep }
      (some (.foundViolation () (.assertionFailure exId) (some failedTrace)),
        gen, trace.steps.size)
    | none =>
      let nexts := Concrete.extractSuccessfulTransitions outcomes
      if nexts.isEmpty then
        if !params.terminating.holdsOn th currSt then
          -- No enabled transitions and not a terminating state: deadlock
          (some (.foundViolation () .deadlock (some trace)), gen, trace.steps.size)
        else
          (none, gen, trace.steps.size)
      else
        let (idx, gen) := randNat gen 0 (nexts.length - 1)
        let (label, nextSt) := nexts[idx]!
        let trace := trace.push { transitionLabel := label, nextState := nextSt }
        let violations := violatedInvariantNames params th nextSt
        if !violations.isEmpty then
          (some (.foundViolation () (.safetyFailure violations) (some trace)),
            gen, trace.steps.size)
        else
          simulateOnceLoop sys params th stepsLeft nextSt trace gen


/-- Run a single random trace from a randomly chosen initial state.
Returns `(violation?, updatedRng, stepsTaken)`. -/
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
  if sys.initStates.isEmpty then
    (none, gen, 0)
  else
    let (idx, gen) := randNat gen 0 (sys.initStates.length - 1)
    let initSt := sys.initStates[idx]!
    let initTrace : Trace ρ σ κ := { theory := th, initialState := initSt, steps := #[] }
    let initViolations := violatedInvariantNames params th initSt
    if !initViolations.isEmpty then
      (some (.foundViolation () (.safetyFailure initViolations) (some initTrace)), gen, 0)
    else
      simulateOnceLoop sys params th maxSteps initSt initTrace gen


/-- Run `maxTraces` independent random traces, stopping on first violation.
Each trace uses an independent seed derived from `(masterSeed + traceIndex)`
for maximum prefix diversity across traces. -/
@[inline, specialize]
partial def simulate {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  [Inhabited σ]
  [Inhabited (κ × σ)]
  : IO (SimulateResult ρ σ κ) := do
  let actualSeed ← if cfg.seed == 0
    then IO.rand 0 0xFFFFFFFFFFFFFFFF
    else pure cfg.seed
  let startMs ← IO.monoMsNow
  let mut i := 0
  let mut totalSteps := 0
  while i < cfg.maxTraces do
    let traceGen := mkStdGen (actualSeed + i)
    let (maybeResult, _, stepsUsed) := simulateOnce sys params th traceGen cfg.maxSteps
    totalSteps := totalSteps + stepsUsed
    match maybeResult with
    | some result =>
      let elapsedMs := (← IO.monoMsNow) - startMs
      return {
        result := result
        tracesRun := i + 1
        elapsedMs := elapsedMs
        seed := actualSeed
        depth := stepsUsed
        totalSteps := totalSteps
      }
    | none =>
      i := i + 1
  let elapsedMs := (← IO.monoMsNow) - startMs
  return {
    result := .noViolationFound cfg.maxTraces
      (.earlyTermination (.reachedDepthBound cfg.maxTraces))
    tracesRun := cfg.maxTraces
    elapsedMs := elapsedMs
    seed := actualSeed
    depth := 0
    totalSteps := totalSteps
  }


end Veil.ModelChecker.Simulation
