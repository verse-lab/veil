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

/-- Return names of invariants violated in the given state. -/
@[inline]
def violatedInvariantNames {ρ σ : Type}
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) : List Lean.Name :=
  params.invariants.filterMap fun p =>
    if !p.holdsOn th st then some p.name else none

/-- Lightweight scan loop: walk without building a trace.
Returns `(violated?, updatedRng, stepsTaken)`. -/
-- NOTE: keep in sync with `simulateOnceLoop` (trace-building variant for replay)
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
    let outcomes := sys.tr th currSt
    let assertionFailureFound := outcomes.any fun (_, outcome) =>
      match outcome with
      | .assertionFailure _ _ => true
      | _ => false
    if assertionFailureFound then
      (true, gen, 1)
    else
      let (nexts, _) := Veil.ModelChecker.Concrete.partitionExecutionOutcome outcomes
      if nexts.isEmpty then
        if !params.terminating.holdsOn th currSt then
          (true, gen, 0)  -- deadlock
        else
          (false, gen, 0)
      else
        let (idx, gen) := randNat gen 0 (nexts.length - 1)
        let (_, nextSt) := nexts[idx]!
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
  if sys.initStates.isEmpty then
    (false, gen, 0)
  else
    let (idx, gen) := randNat gen 0 (sys.initStates.length - 1)
    let initSt := sys.initStates[idx]!
    if !(violatedInvariantNames params th initSt).isEmpty then
      (true, gen, 0)
    else
      scanOnceLoop sys params th maxSteps initSt gen

/-- Inner loop of a single random trace: walk from `currSt` for up to
`stepsLeft` steps, picking a random enabled transition at each step.
Returns `(violation?, updatedRng, stepsTaken)`. Used only for replay. -/
-- NOTE: keep in sync with `scanOnceLoop` (allocation-free variant for scanning)
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
    let failingStep := outcomes.findSome? fun (label, outcome) =>
      match outcome with
      | .assertionFailure exId st =>
        some (exId, { transitionLabel := label, nextState := st })
      | _ => none
    match failingStep with
    | some (exId, step) =>
      let failedTrace := { trace with failingStep := some step }
      -- +1 for the failing action itself (not in trace.steps, stored in failingStep)
      (some (.foundViolation () (.assertionFailure exId) (some failedTrace)),
        gen, trace.steps.size + 1)
    | none =>
      let (nexts, _) := Veil.ModelChecker.Concrete.partitionExecutionOutcome outcomes
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
Scans without trace recording for speed; replays only the violating trace.
Each trace uses an independent seed derived from `(masterSeed + traceIndex)`. -/
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
  while i < cfg.maxTraces do
    let traceSeed := actualSeed + i
    try
      -- Fast scan: no trace allocation
      let (violated, _, stepsUsed) := scanOnce sys params th (mkStdGen traceSeed) cfg.maxSteps
      if violated then
        -- Replay with same seed to build counterexample trace
        let (maybeResult, _, _) := simulateOnce sys params th (mkStdGen traceSeed) cfg.maxSteps
        match maybeResult with
        | some result =>
          let elapsedMs := (← IO.monoMsNow) - startMs
          return {
            result := result
            tracesRun := i + 1
            elapsedMs := elapsedMs
            seed := actualSeed
            depth := stepsUsed
          }
        | none =>
          i := i + 1
      else
        i := i + 1
    catch e =>
      IO.eprintln s!"#simulate: error on trace {i} (seed := {traceSeed}): {e.toString}"
      i := i + 1
  let elapsedMs := (← IO.monoMsNow) - startMs
  return {
    result := .noViolationFound cfg.maxTraces
      (.earlyTermination (.reachedDepthBound cfg.maxTraces))
    tracesRun := cfg.maxTraces
    elapsedMs := elapsedMs
    seed := actualSeed
    depth := 0
  }

end Veil.ModelChecker.Simulation
