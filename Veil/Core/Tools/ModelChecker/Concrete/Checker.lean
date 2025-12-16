import Veil.Core.Tools.ModelChecker.TransitionSystem
import Veil.Core.Tools.ModelChecker.Interface
import Veil.Core.Tools.ModelChecker.Concrete.FunctionalQueue
import Veil.Core.Tools.ModelChecker.Trace

namespace Veil.ModelChecker.Concrete
open Std

/-- A function that maps a full state to a view of the state. -/
class StateView (FullState View : Type) where
  view : FullState → View

class abbrev StateFingerprint (FullState View : Type) := BEq View, LawfulBEq View, Hashable View, LawfulHashable View, StateView FullState View

instance StateFingerprint.ofHash (σ : Type) [Hashable σ] : StateFingerprint σ UInt64 where
  beq := BEq.beq
  rfl := BEq.rfl
  eq_of_beq := LawfulBEq.eq_of_beq
  hash_eq := LawfulHashable.hash_eq
  view := hash

/-- A model checker search context is parametrised by the system that's being
checked and the theory it's being checked under. -/
structure SearchContext {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ)
where
  seen  : Std.HashSet σₕ
  /-- Queue storing (fingerprint, state, depth) tuples for BFS traversal -/
  sq    : fQueue (σₕ × σ × Nat)
  /- We use a `HashMap σ_post (σ_pre × κ)` to store the log of transitions, which
  will make it easier to reconstruct counterexample trace. -/
  log                : Std.HashMap σₕ (σₕ × κ)
  violatingStates    : List σₕ
  /-- Have we finished the search? If so, why? -/
  finished           : Option TerminationReason
  /-- The depth up to which ALL states have been fully explored (successors enqueued) -/
  completedDepth     : Nat
  /-- The depth of the current BFS frontier being processed -/
  currentFrontierDepth : Nat
  queue_sound        : ∀ x : σ, ∀ d : Nat, ⟨fp.view x, x, d⟩ ∈ fQueue.toList sq → sys.reachable x
  visited_sound      : Function.Injective fp.view → ∀ x, (fp.view x) ∈ seen → sys.reachable x
  queue_sub_visited  : ∀ x : σ, ∀ d : Nat, ⟨fp.view x, x, d⟩ ∈ fQueue.toList sq → (fp.view x) ∈ seen
  queue_wellformed   : ∀ fingerprint st d, ⟨fingerprint, st, d⟩ ∈ fQueue.toList sq → fingerprint = fp.view st

@[inline, specialize]
def SearchContext.hasFinished {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @SearchContext ρ σ κ σₕ fp th sys params) : Bool := ctx.finished.isSome

def SearchContext.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ) :
  @SearchContext ρ σ κ σₕ fp th sys params := {
    seen := HashSet.insertMany HashSet.emptyWithCapacity (sys.initStates |> Functor.map fp.view),
    sq := fQueue.ofList (sys.initStates |> Functor.map (fun s => (fp.view s, s, 0))),
    log := Std.HashMap.emptyWithCapacity
    violatingStates := []
    finished := none
    completedDepth := 0
    currentFrontierDepth := 0
    queue_sound := by dsimp only [Functor.map]; intros; grind
    visited_sound := by
      dsimp only [Functor.map]
      intro h_view_inj x h_in
      have h_in_init : x ∈ sys.initStates := by {
        have h_in_list : fp.view x ∈ (sys.initStates).map fp.view := by
          { grind [Std.HashSet.mem_of_mem_insertMany_list] }
        rw [List.mem_map] at h_in_list
        obtain ⟨s, h_s_in, h_eq_view⟩ := h_in_list
        have h_eq_st : s = x := h_view_inj h_eq_view
        grind
      }
      grind
    queue_sub_visited := by dsimp only [Functor.map]; intros; grind
    queue_wellformed := by dsimp only [Functor.map]; intros; grind
  }

@[inline, specialize]
def SearchContext.shouldTerminateEarly {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @SearchContext ρ σ κ σₕ fp th sys params)
  (currSt : σ)
  (successors : List (κ × σ))
  : Option EarlyTerminationCondition :=
  match ctx.finished with
  | some (.earlyTermination condition) => some condition
  | _ => params.earlyTerminationConditions.findSome? (fun sc => match sc with
    | EarlyTerminationCondition.foundViolatingState =>
        if !params.safety.holdsOn th currSt then some sc else none
    | EarlyTerminationCondition.reachedDepthBound bound =>
        if ctx.completedDepth >= bound then some sc else none
    | EarlyTerminationCondition.deadlockOccurred =>
        if successors.isEmpty && !params.terminating.holdsOn th currSt then some sc else none
  )

/-- Process a single neighbor node during BFS traversal.
If the neighbor has been seen, return the current context unchanged.
Otherwise, add it to seen set and log, then enqueue it. -/
@[inline, specialize]
def SearchContext.tryExploreNeighbor {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)  -- fingerprint of state we're coming from (pre-state), for logging
  (depth : Nat)  -- depth of the current state (neighbor will be at depth + 1)
  (ctx : @SearchContext ρ σ κ σₕ fp th sys params)
  (neighbor : κ × σ)
  (h_neighbor : sys.reachable neighbor.2) :
  @SearchContext ρ σ κ σₕ fp th sys params :=
  let ⟨label, succ⟩ := neighbor
  let fingerprint := fp.view succ
  if ctx.seen.contains fingerprint then ctx
  else
    let ctx_with_seen : @SearchContext ρ σ κ σₕ fp th sys params := {
      ctx with
        seen := ctx.seen.insert fingerprint,
        log := ctx.log.insert fingerprint (fpSt, label),
        queue_sound := sorry
        visited_sound := sorry
        queue_sub_visited := sorry
        queue_wellformed := ctx.queue_wellformed
    }
    { ctx_with_seen with
        sq := ctx_with_seen.sq.enqueue (fingerprint, succ, depth + 1),
        queue_sound := sorry
        queue_sub_visited := sorry
        queue_wellformed := sorry
    }

/-- Process the current state, queuing its successors. -/
@[inline, specialize]
def SearchContext.processState {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)
  (depth : Nat)  -- depth of the current state
  (curr : σ)
  (h_curr : sys.reachable curr)
  (ctx : @SearchContext ρ σ κ σₕ fp th sys params) :
  @SearchContext ρ σ κ σₕ fp th sys params :=
  -- Log violating state, if found
  let ctx := if !params.safety.holdsOn th curr then {ctx with violatingStates := fpSt :: ctx.violatingStates} else ctx
  let successors := sys.tr th curr
  -- Check whether we should stop the search early
  match ctx.shouldTerminateEarly sys curr successors with
  | some .foundViolatingState => {ctx with finished := some (.earlyTermination .foundViolatingState)}
  | some (.reachedDepthBound bound) => {ctx with finished := some (.earlyTermination (.reachedDepthBound bound))}
  | some .deadlockOccurred => {ctx with finished := some (.earlyTermination .deadlockOccurred)}
  -- If not, explore all neighbors of the current state
  | none =>
      successors.attach.foldl (fun current_ctx ⟨⟨tr, postState⟩, h_neighbor_in_tr⟩ =>
      if current_ctx.hasFinished then current_ctx
      else
        let h_neighbor_reachable : sys.reachable postState :=
          EnumerableTransitionSystem.reachable.step curr postState h_curr ⟨tr, h_neighbor_in_tr⟩
        SearchContext.tryExploreNeighbor sys fpSt depth current_ctx ⟨tr, postState⟩ h_neighbor_reachable
    ) ctx

/-- Perform one step of BFS. -/
@[inline, specialize]
def SearchContext.bfsStep {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @SearchContext ρ σ κ σₕ fp th sys params) :
  @SearchContext ρ σ κ σₕ fp th sys params :=
  match ctx.sq.dequeue? with
  | none => { ctx with finished := some (.exploredAllReachableStates) }
  | some ((fpSt, curr, depth), q_tail) =>
    have h_curr : sys.reachable curr := sorry
    -- Update completed depth when we move to a new frontier level
    let (newCompletedDepth, newFrontierDepth) :=
      if depth > ctx.currentFrontierDepth then
        (depth - 1, depth)  -- All states at previous depth are now fully explored
      else
        (ctx.completedDepth, ctx.currentFrontierDepth)
    let ctx_dequeued : @SearchContext ρ σ κ σₕ fp th sys params := {
      ctx with
        sq := q_tail,
        completedDepth := newCompletedDepth,
        currentFrontierDepth := newFrontierDepth,
        queue_sound := sorry
        visited_sound := ctx.visited_sound
        queue_sub_visited := sorry
        queue_wellformed := sorry
    }
    SearchContext.processState sys fpSt depth curr h_curr ctx_dequeued

@[specialize]
def breadthFirstSearch {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ) :
  @SearchContext ρ σ κ σₕ fp th sys params := Id.run do
  let mut ctx : @SearchContext ρ σ κ σₕ fp th sys params := SearchContext.initial sys params
  while !ctx.hasFinished do
    ctx := SearchContext.bfsStep sys ctx
  return ctx

/-! ## Trace Recovery

These functions reconstruct a full trace with concrete states from a SearchContext
that contains fingerprint-based state references. -/

/-- Walk backward through the log to build a fingerprint-based path from a
state to an initial state. Returns `(initialStateFingerprint, steps)` where
each step has the transition label and the fingerprint of the post-state. -/
partial def retraceSteps [BEq σₕ] [Hashable σₕ]
  (log : Std.HashMap σₕ (σₕ × κ)) (cur : σₕ)
  (acc : List (Step σₕ κ) := []) : σₕ × List (Step σₕ κ) :=
  match log.get? cur with
  | none => (cur, acc)
  | some (prev, label) =>
    retraceSteps log prev ({ transitionLabel := label, nextState := cur } :: acc)

/-- Find a full state from a list that matches a given fingerprint. -/
@[inline, specialize]
def findByFingerprint [fp : StateFingerprint σ σₕ]
  (states : List σ) (targetFp : σₕ) (fallback : σ) : σ :=
  states.find? (fun s => fp.view s == targetFp) |>.getD fallback

/-- Extract fingerprint traces for all violating states in a SearchContext. -/
def collectTraces {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @SearchContext ρ σ κ σₕ fp th sys params)
  : List (σₕ × List (Step σₕ κ)) :=
  ctx.violatingStates.map (fun badState => retraceSteps ctx.log badState)

/-- Reconstruct a full trace with concrete states from a SearchContext.
This re-executes transitions to recover full state objects from fingerprints. -/
def recoverTrace {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [Inhabited κ] [Inhabited σ] [Repr σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @SearchContext ρ σ κ σₕ fp th sys params)
  : Trace ρ σ κ :=
  -- Get fingerprint traces from log
  let fingerprintTraces := collectTraces sys ctx
  match fingerprintTraces with
  | [] => { theory := th, initialState := default, steps := #[] }
  | (initFp, stepsFp) :: _ => Id.run do
    -- Recover initial state by matching fingerprint
    let initialState := findByFingerprint sys.initStates initFp default
    -- Recover trace steps by re-executing transitions and matching fingerprints
    let mut curSt := initialState
    let mut steps : Steps σ κ := #[]
    for step in stepsFp do
      let successors := sys.tr th curSt
      let (transitionLabel, nextSt) :=
        match successors.find? (fun (_, s) => fp.view s == step.nextState) with
        | some (tr, s) => (tr, s)
        | none => panic! s!"Could not recover transition from fingerprint {repr (fp.view curSt)} to {repr step.nextState}!"
      curSt := nextSt
      steps := steps.push { transitionLabel := transitionLabel, nextState := nextSt }
    return { theory := th, initialState := initialState, steps := steps }


/-! ## Model Checker -/

def findReachable {ρ σ κ : Type}
  [Inhabited κ] [Inhabited σ] [Repr σ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  [fp : StateFingerprint σ UInt64]
  (params : SearchParameters ρ σ)
  : ModelCheckingResult ρ σ κ :=
  let ctx : @SearchContext ρ σ κ UInt64 fp th sys params :=
    breadthFirstSearch sys params
  match ctx.finished with
  | some (.earlyTermination .foundViolatingState) =>
    ModelCheckingResult.foundViolation .safetyFailure (some (recoverTrace sys params ctx))
  | some (.earlyTermination .deadlockOccurred) =>
    ModelCheckingResult.foundViolation .deadlock (some (recoverTrace sys params ctx))
  | some (.earlyTermination (.reachedDepthBound _)) =>
    -- No violation found within depth bound; report number of states explored
    ModelCheckingResult.noViolationFound ctx.seen.size (.earlyTermination (.reachedDepthBound ctx.completedDepth))
  | some (.exploredAllReachableStates) =>
    if !ctx.violatingStates.isEmpty then
      ModelCheckingResult.foundViolation .safetyFailure (some (recoverTrace sys params ctx))
    else
      ModelCheckingResult.noViolationFound ctx.seen.size (.exploredAllReachableStates)
  | none => panic! s!"SearchContext.finished is none! This should never happen."

end Veil.ModelChecker.Concrete
