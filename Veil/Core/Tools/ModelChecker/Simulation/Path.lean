import Veil.Core.Tools.ModelChecker.Simulation.Basic
import Veil.Core.Tools.ModelChecker.Concrete.Core

namespace Veil.ModelChecker.Simulation

private inductive StepDecision (σ κ : Type) where
  | assertionFailure (exId : Int) (step : Step σ κ)
  | deadlock
  | terminated
  | continue (nexts : List (κ × σ)) (hNonempty : nexts ≠ [])

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
      match nexts with
      | [] => if !params.terminating.holdsOn th currSt then .deadlock else .terminated
      | hd :: tl => .continue (hd :: tl) (by simp)

theorem randNat_lt_length {α : Type} (xs : List α) (h : xs ≠ []) (gen : StdGen) :
  (let p := randNat gen 0 (xs.length - 1); p.1 < xs.length) := by
  have hlen : 0 < xs.length := by simpa [List.length_pos_iff_ne_nil] using h
  have hk : xs.length - 1 + 1 = xs.length := Nat.sub_add_cancel (Nat.succ_le_of_lt hlen)
  unfold randNat
  simp [Nat.not_lt.mpr (Nat.zero_le (xs.length - 1)), hk]
  exact Nat.mod_lt _ hlen

structure PickedTransition {σ κ : Type} (nexts : List (κ × σ)) where
  value : κ × σ
  mem : value ∈ nexts
  gen : StdGen

def pickNextTransition {σ κ : Type}
  (nexts : List (κ × σ)) (gen : StdGen) (h : nexts ≠ []) [Inhabited (κ × σ)] : PickedTransition nexts :=
  let p := randNat gen 0 (nexts.length - 1)
  let idx := p.1
  let gen' := p.2
  have hlt : idx < nexts.length := by
    simpa [p, idx] using randNat_lt_length nexts h gen
  { value := nexts.get ⟨idx, hlt⟩
    mem := by simpa using List.get_mem nexts ⟨idx, hlt⟩
    gen := gen' }

theorem pickNextTransition_mem {σ κ : Type}
  (nexts : List (κ × σ)) (gen : StdGen) (h : nexts ≠ []) [Inhabited (κ × σ)] :
  (pickNextTransition nexts gen h).value ∈ nexts :=
  (pickNextTransition nexts gen h).mem

structure PickedInitState {σ : Type} (initStates : List σ) where
  value : σ
  mem : value ∈ initStates
  gen : StdGen

def pickInitialState {σ : Type}
  (initStates : List σ) (gen : StdGen) (h : initStates ≠ []) [Inhabited σ] : PickedInitState initStates :=
  let p := randNat gen 0 (initStates.length - 1)
  let idx := p.1
  let gen' := p.2
  have hlt : idx < initStates.length := by
    simpa [p, idx] using randNat_lt_length initStates h gen
  { value := initStates.get ⟨idx, hlt⟩
    mem := by simpa using List.get_mem initStates ⟨idx, hlt⟩
    gen := gen' }

theorem pickInitialState_mem {σ : Type}
  (initStates : List σ) (gen : StdGen) (h : initStates ≠ []) [Inhabited σ] :
  (pickInitialState initStates gen h).value ∈ initStates :=
  (pickInitialState initStates gen h).mem

@[inline, specialize]
def scanOnceLoop {ρ σ κ : Type} {th₀ : ρ}
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
    | .continue nexts hNonempty =>
        let picked := pickNextTransition nexts gen hNonempty
        let (_, nextSt) := picked.value
        let gen := picked.gen
        if !(violatedInvariantNames params th nextSt).isEmpty then
          (true, gen, 1)
        else
          let (violated, gen, innerSteps) := scanOnceLoop sys params th stepsLeft nextSt gen
          (violated, gen, innerSteps + 1)
termination_by stepsLeft

@[inline, specialize]
def scanOnce {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (gen : StdGen)
  (maxSteps : Nat)
  [Inhabited σ]
  [Inhabited (κ × σ)]
  : Bool × StdGen × Nat :=
  let initStates := filterInitStatesByConstraints sys params th
  match initStates with
  | [] => (false, gen, 0)
  | hd :: tl =>
      let picked := pickInitialState (hd :: tl) gen (by simp)
      let initSt := picked.value
      let gen := picked.gen
      if !(violatedInvariantNames params th initSt).isEmpty then
        (true, gen, 0)
      else
          scanOnceLoop sys params th maxSteps initSt gen

@[inline, specialize]
def simulateOnceLoop {ρ σ κ : Type} {th₀ : ρ}
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
    | .continue nexts hNonempty =>
        let picked := pickNextTransition nexts gen hNonempty
        let (label, nextSt) := picked.value
        let gen := picked.gen
        let trace := trace.push { transitionLabel := label, nextState := nextSt }
        let violations := violatedInvariantNames params th nextSt
        if !violations.isEmpty then
          (some (.foundViolation () (.safetyFailure violations) (some trace)), gen, trace.steps.size)
        else
          simulateOnceLoop sys params th stepsLeft nextSt trace gen
termination_by stepsLeft

@[inline, specialize]
def simulateOnce {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (gen : StdGen)
  (maxSteps : Nat)
  [Inhabited σ]
  [Inhabited (κ × σ)]
  : Option (ModelCheckingResult ρ σ κ Unit) × StdGen × Nat :=
  let initStates := filterInitStatesByConstraints sys params th
  match initStates with
  | [] => (none, gen, 0)
  | hd :: tl =>
      let picked := pickInitialState (hd :: tl) gen (by simp)
      let initSt := picked.value
      let gen := picked.gen
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
  let (maybeResult, _, depth) := simulateOnce sys params th (mkStdGen traceSeed) cfg.maxSteps
  maybeResult.map (fun result => (result, depth))

end Veil.ModelChecker.Simulation
