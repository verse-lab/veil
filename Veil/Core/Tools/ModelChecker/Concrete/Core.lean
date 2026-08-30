import Veil.Core.Tools.ModelChecker.TransitionSystem
import Veil.Core.Tools.ModelChecker.Interface
import Veil.Frontend.DSL.Action.Semantics.Definitions
import Veil.Core.Tools.ModelChecker.Trace
import Veil.Frontend.DSL.State.Types
import Veil.Util.ShardedSetUInt
import Batteries.Lean.HashMap

namespace Veil.ModelChecker.Concrete
open Std

/-- A function that maps a full state to a view of the state. -/
class StateView (FullState View : Type) where
  view : FullState → View

class abbrev StateFingerprint (FullState View : Type)
  := BEq View, LawfulBEq View, Hashable View, LawfulHashable View, StateView FullState View

-- NOTE: Without setting these, Lean might get stuck when synthesizing
-- `BEq` or `Hashable` instances in scenarios that are completely irrelevant
-- to `StateFingerprint`
attribute [instance low] StateFingerprint.toBEq StateFingerprint.toLawfulBEq StateFingerprint.toHashable StateFingerprint.toLawfulHashable StateFingerprint.toStateView

instance StateFingerprint.ofHash (σ : Type) [Hashable σ] : StateFingerprint σ UInt64 where
  beq := BEq.beq
  rfl := BEq.rfl
  eq_of_beq := LawfulBEq.eq_of_beq
  hash_eq := LawfulHashable.hash_eq
  view := hash

structure QueueItem (σₕ σ : Type) where
  fingerprint : σₕ
  state : σ
  depth : Nat
deriving BEq, DecidableEq, Repr

theorem QueueItem.fold_unfold {σₕ σ : Type} (item : QueueItem σₕ σ) :
  item = ⟨item.fingerprint, item.state, item.depth⟩ := rfl

/-- A queue item for the MapReduce checker, without the depth field.
    In MapReduce BFS, all items in the frontier share the same depth,
    tracked externally via `completedDepth`. -/
structure MapReduceQueueItem (σₕ σ : Type) where
  fingerprint : σₕ
  state : σ
deriving BEq, DecidableEq, Repr

structure ActionStat where
  statesGenerated : Nat
  distinctStates : Nat
deriving Lean.ToJson, Lean.FromJson, BEq, DecidableEq, Repr, Inhabited

@[inline]
def ActionStat.update (distinct? : Bool) (stat : ActionStat) : ActionStat :=
  let ⟨sg, ds⟩ := stat
  if distinct? then ⟨sg.succ, ds.succ⟩ else ⟨sg.succ, ds⟩

@[inline]
def ActionStat.merge (stat1 stat2 : ActionStat) : ActionStat :=
  let ⟨sg1, ds1⟩ := stat1
  let ⟨sg2, ds2⟩ := stat2
  ⟨sg1 + sg2, ds1 + ds2⟩

abbrev ActionStatsMap κ [BEq κ] [Hashable κ] := Std.HashMap κ ActionStat

-- Use `.alter` to ensure linear usage
-- NOTE: This doesn't seem `specialize`d; what happened?
@[inline]
def ActionStatsMap.update [BEq κ] [Hashable κ] (distinct? : Bool) (label : κ) (amap : ActionStatsMap κ) : ActionStatsMap κ :=
  if distinct? then
    amap.alter label fun
      | some ⟨as, ds⟩ => Option.some ⟨as + 1, ds + 1⟩
      | none => Option.some { statesGenerated := 1, distinctStates := 1 }
  else
    amap.alter label fun
      | some ⟨as, ds⟩ => Option.some ⟨as + 1, ds⟩
      | none => Option.some { statesGenerated := 1, distinctStates := 0 }

/-- Merge two `ActionStatsMap`s. Note that the time complexity depends on the *second* one;
but in the case here, the domain size of `m2` should be mostly fixed, so it should not
matter too much which operand the time complexity depends on. -/
def ActionStatsMap.combine [BEq κ] [Hashable κ] (m1 m2 : ActionStatsMap κ) : ActionStatsMap κ :=
  m1.mergeWith (other := m2) fun _ => ActionStat.merge

/-- Statistics for a single action (transition label), for display. -/
structure ActionStatDisplay extends ActionStat where
  /-- Action name (e.g., "Label.send_msg 1 2") -/
  name : String
  deriving Lean.ToJson, Lean.FromJson, Inhabited, Repr

/-- Abstract action statistics map. `asm` tracks `statesGenerated` per action label. -/
class ActionStatUpdate (κ : Type u) (asm : outParam (Type v)) where
  /-- Empty stats map -/
  empty : asm
  increment : κ → Bool → asm → asm
  /-- Combine (sum) two stats maps -/
  merge : asm → asm → asm
  -- /-- Read the count for a specific label -/
  -- lookup : κ → asm → Nat
  dump : asm → List ActionStatDisplay

/-- Array-based instance: O(1) increment and lookup.
    Selected when `FinEncodableInjOnly κ` is available. -/
instance (priority := high) [instf : FinEncodableInjOnly κ] [inste : Enumeration κ] [Repr κ] :
  ActionStatUpdate κ (Array ActionStat) where
  empty := Array.replicate instf.card default
  increment label distinct? arr := arr.modify (instf.encode label).val (ActionStat.update distinct?)
  merge arr1 arr2 := arr1.zipWith ActionStat.merge arr2
  dump arr := inste.allValues.map fun label =>
    let idx := instf.encode label
    let stat := arr.getD idx.val default
    { stat with name := repr label |>.pretty }

abbrev VectorForActionStatUpdate (α : Type u) (κ : Type v) [enc : FinEncodableInjOnly κ] := Vector α enc.card

/-- Vector-based instance: O(1) increment and lookup. -/
instance (priority := high + 100) [instf : FinEncodableInjOnly κ] [inste : Enumeration κ] [Repr κ] :
  ActionStatUpdate κ (VectorForActionStatUpdate ActionStat κ) where
  empty := Vector.replicate instf.card default
  increment label distinct? vec :=
    let idx := instf.encode label
    vec.modify idx.val (ActionStat.update distinct?) idx.isLt
  merge vec1 vec2 := vec1.zipWith ActionStat.merge vec2
  dump vec := inste.allValues.map fun label =>
    let idx := instf.encode label
    let stat := vec[idx]
    { stat with name := repr label |>.pretty }

/-- HashMap-based fallback instance for types without `FinEncodableInjOnly`. -/
instance (priority := low) [BEq κ] [Hashable κ] [Repr κ] : ActionStatUpdate κ (ActionStatsMap κ) where
  empty := {}
  increment label distinct? m := m.update distinct? label
  merge m1 m2 := m1.combine m2
  -- lookup label m := m.getD label 0
  dump m := m.fold (init := []) fun acc label stat =>
    { stat with name := repr label |>.pretty } :: acc

/-- A model checker search context is parametrised by the system that's being
checked and the theory it's being checked under. -/
structure BaseSearchContext (σ κ σₕ asm : Type)
  [fp : StateFingerprint σ σₕ]
  [ActionStatUpdate κ asm]
where
  /- We use a `HashMap σ_post (σ_pre × κ)` to store the log of transitions, which
  will make it easier to reconstruct counterexample trace. -/
  log                : Std.HashMap σₕ (Option (σₕ × κ))
  violatingStates    : List (σₕ × ViolationKind)
  /-- Have we finished the search? If so, why? -/
  finished           : Option (TerminationReason σₕ)
  /-- The depth up to which ALL states have been fully explored (successors enqueued) -/
  completedDepth     : Nat
  /-- The depth of the current BFS frontier being processed -/
  currentFrontierDepth : Nat
  /-- Total number of post-states generated (before deduplication) -/
  statesFound : Nat
  /-- Per-action statistics (only `statesGenerated`) -/
  actionStatsMap : asm

structure SearchContextInvariants {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Veil.ExId0 κ (List (κ × ExecutionOutcome Veil.ExId0 σ)) th)
  -- NOTE: Although `params` is not used in the invariants below yet,
  -- we should better keep it here for future extensions.
  (params : SearchParameters ρ σ)
  (inQueue : σₕ → σ → Prop)
  (seen : σₕ → Prop) : Prop
where
  queue_sound        : ∀ x st, inQueue x st → sys.reachable st ∧ seen x ∧ x = fp.view st
  visited_sound      : Function.Injective fp.view → ∀ x, seen (fp.view x) → sys.reachable x

variable {ρ σ κ σₕ asm : Type} [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm]
  (params : SearchParameters ρ σ) (th : ρ) (fpSt : σₕ) (curr : σ)

@[inline]
def BaseSearchContext.hasFinished (ctx : BaseSearchContext σ κ σₕ asm) : Bool := ctx.finished.isSome

@[inline]
def BaseSearchContext.initial (initialStates : List σ) : BaseSearchContext σ κ σₕ asm :=
  let initStates := initialStates.map fun x => (fp.view x, Option.none)
  {
    log := Std.HashMap.ofList initStates,
    violatingStates := [],
    finished := none,
    completedDepth := 0,
    currentFrontierDepth := 0,
    statesFound := initStates.length,
    actionStatsMap := ActionStatUpdate.empty (κ := κ)
  }

-- NOTE: Hopefully, if `outcomes` does not have any other reference, then
-- Lean should be able to reuse constructors inside it? Can we somehow
-- achieve zero additional memory allocation here?

/-- Partition a list of `(label × ExecutionOutcome)` pairs into two components:
a list of successful transitions, and a list of transitions where exceptions
were raised. The divergence part is discarded. -/
def partitionExecutionOutcome (outcomes : List (κ × ExecutionOutcome Veil.ExId0 σ)) :
  List (κ × σ) × List (Veil.ExId0 × σ) :=
  outcomes.foldr
    (init := ([], []))
    (fun (label, outcome) (succs, exns) =>
      match outcome with
      | .success st => ((label, st) :: succs, exns)
      | .assertionFailure exId st => (succs, (exId, st) :: exns)
      | .divergence => (succs, exns))

theorem partitionExecutionOutcome.fst_spec {κ σ : Type} (outcomes : List (κ × ExecutionOutcome Veil.ExId0 σ)) :
  ∀ (label : κ) (st : σ),
    (label, st) ∈ (partitionExecutionOutcome outcomes).fst ↔
    (label, ExecutionOutcome.success st) ∈ outcomes := by
  introv ; unfold partitionExecutionOutcome
  induction outcomes with
  | nil => simp
  | cons x l ih => rcases x with ⟨l, _ | _ | _⟩ <;> grind

-- NOTE: If this function is put inside `BaseSearchContext.checkViolationsAndMaybeTerminate`,
-- `specialize` of `List.filterMap` may not exhibit
def checkViolationsAndMaybeTerminate
  (completedDepth : Nat)
  (hasSuccessfulTransition : Bool)
  (assertionFailures : List (Veil.ExId0 × σ)) :
  List (σₕ × ViolationKind) × Option (EarlyTerminationReason σₕ) :=
  -- Compute all violation conditions once
  let safetyViolations := params.invariants.filterMap fun p =>
    if !p.holdsOn th curr then some p.name else none
  let safetyViolation := !safetyViolations.isEmpty
  let deadlock := !hasSuccessfulTransition && !params.terminating.holdsOn th curr

  -- Collect all violations to add in a single list
  let newViolations : List (σₕ × ViolationKind) :=
    (if safetyViolation then [(fpSt, .safetyFailure safetyViolations)] else []) ++
    (if deadlock then [(fpSt, .deadlock)] else []) ++
    -- NOTE: This should be further optimized to avoid extra memory allocation
    (assertionFailures.map fun (exId, _) => (fpSt, .assertionFailure exId.down))

  let earlyTermination := params.earlyTerminationConditions.findSome? fun
    | .foundViolatingState => if safetyViolation then some (.foundViolatingState fpSt safetyViolations) else none
    | .reachedDepthBound bound => if completedDepth >= bound then some (.reachedDepthBound bound) else none
    | .deadlockOccurred => if deadlock then some (.deadlockOccurred fpSt) else none
    | .assertionFailed => assertionFailures.head?.map fun (exId, _) => .assertionFailed fpSt exId.down
    | .cancelled => none  -- Cancellation is handled externally via cancel token, not through early termination conditions
  (newViolations, earlyTermination)

/-- Process the current state, queuing its successors. -/
-- @[inline, specialize]
def BaseSearchContext.processState
  (outcomes : List (κ × ExecutionOutcome Veil.ExId0 σ))
  (ctx : BaseSearchContext σ κ σₕ asm) : BaseSearchContext σ κ σₕ asm × Option (List (κ × σ)) :=
  let (successfulTransitions, assertionFailures) := partitionExecutionOutcome outcomes
  let hasSuccessfulTransition := !successfulTransitions.isEmpty
  let completedDepth := ctx.completedDepth
  let (newViolations, earlyTermination) :=
    checkViolationsAndMaybeTerminate params th fpSt curr completedDepth hasSuccessfulTransition assertionFailures
  let ctx := {ctx with violatingStates := newViolations ++ ctx.violatingStates}
  -- Check for violations, record them, and determine if we should terminate early
  let ctx := match earlyTermination with
    | some x =>
      match x with
      | .foundViolatingState fp violations => {ctx with finished := some (.earlyTermination (.foundViolatingState fp violations))}
      | .reachedDepthBound bound => {ctx with finished := some (.earlyTermination (.reachedDepthBound bound))}
      | .deadlockOccurred fp => {ctx with finished := some (.earlyTermination (.deadlockOccurred fp))}
      | .assertionFailed fp exId => {ctx with finished := some (.earlyTermination (.assertionFailed fp exId))}
      | .cancelled => {ctx with finished := some (.earlyTermination .cancelled)}
    | none => ctx
  (ctx, if earlyTermination.isSome then none else some successfulTransitions)

def BaseSearchContext.mergeWithoutDepthChange (ctx1 ctx2 : BaseSearchContext σ κ σₕ asm) : BaseSearchContext σ κ σₕ asm :=
  { log := ctx1.log.union ctx2.log,
    violatingStates := ctx1.violatingStates ++ ctx2.violatingStates,
    finished := ctx1.finished.or ctx2.finished,
    completedDepth := ctx1.completedDepth,    -- no change
    currentFrontierDepth := ctx1.currentFrontierDepth,    -- no change
    statesFound := ctx1.statesFound + ctx2.statesFound,
    actionStatsMap := ActionStatUpdate.merge (κ := κ) ctx1.actionStatsMap ctx2.actionStatsMap }

/-- Like `mergeWithoutDepthChange` but does NOT merge the `log` field.
    Used in the MapReduce path to delay log merging until trace recovery is needed. -/
def BaseSearchContext.mergeWithoutDepthChangeNoLog (ctx1 ctx2 : BaseSearchContext σ κ σₕ asm) : BaseSearchContext σ κ σₕ asm :=
  { log := ctx1.log,
    violatingStates := ctx1.violatingStates ++ ctx2.violatingStates,
    finished := ctx1.finished.or ctx2.finished,
    completedDepth := ctx1.completedDepth,
    currentFrontierDepth := ctx1.currentFrontierDepth,
    statesFound := ctx1.statesFound + ctx2.statesFound,
    actionStatsMap := ActionStatUpdate.merge (κ := κ) ctx1.actionStatsMap ctx2.actionStatsMap }

end Veil.ModelChecker.Concrete
