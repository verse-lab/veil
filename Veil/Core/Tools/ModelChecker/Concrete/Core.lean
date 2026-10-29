module

public import Veil.Core.Tools.ModelChecker.TransitionSystem
public import Veil.Core.Tools.ModelChecker.Interface
public import Veil.Core.Tools.ModelChecker.Trace
public import Veil.Frontend.DSL.State.Types
public import Veil.Util.ShardedSetUInt
public import Batteries.Lean.HashMap

@[expose] public section

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

/-- The hash as a 63-bit natural number. On 64-bit platforms a `Nat` below 2⁶³ is a tagged scalar,
so storing it in a polymorphic container (the log, the seen set, a queue item) allocates nothing,
whereas a `UInt64` there is a separate heap object. Clearing the top bit keeps the value below 2⁶³,
above which `UInt64.toNat` allocates. It must be the top bit: a state with a single field hashes to
that field's own, unmixed hash (an enum constructor's index, a `Fin`'s value), whose information is
in the low bits, so shifting out the lowest bit would give distinct states the same fingerprint.
(On 32-bit platforms only values below 2³¹ are scalars.) -/
instance StateFingerprint.ofHashNat (σ : Type) [Hashable σ] : StateFingerprint σ Nat where
  beq := BEq.beq
  rfl := BEq.rfl
  eq_of_beq := LawfulBEq.eq_of_beq
  hash_eq := LawfulHashable.hash_eq
  view s := (hash s &&& 0x7fffffffffffffff).toNat

structure QueueItem (σₕ σ : Type) where
  fingerprint : σₕ
  state : σ
  depth : Nat
deriving BEq, DecidableEq, Repr

theorem QueueItem.fold_unfold {σₕ σ : Type} (item : QueueItem σₕ σ) :
  item = ⟨item.fingerprint, item.state, item.depth⟩ := rfl

/-- How the search first reached a state, recorded against the state's fingerprint. Trace
recovery re-executes the system along these entries, so they hold positions in `sys.initStates`
and in the successes of `sys.tr` rather than fingerprints of post-states: the position does not
depend on fingerprints being injective. The label is redundant with the position, but lets a
path be displayed from the log alone. -/
inductive LogEntry (σₕ κ : Type) where
  /-- The state is `sys.initStates[idx]`. -/
  | init (idx : Nat)
  /-- The state is the post-state of `(sys.tr th parent).successes[idx]`, a transition labelled
  `label`. -/
  | step (parent : σₕ) (label : κ) (idx : Nat)
deriving Repr, Inhabited

/-- A queue item for the MapReduce checker, without the depth field.
    In MapReduce BFS, all items in the frontier share the same depth,
    tracked externally via `currentFrontierDepth`. The item carries the log entry of its state, so
    that the merge of a BFS round keeps, for each fingerprint, the entry of the very state it
    keeps in the frontier. -/
structure MapReduceQueueItem (σₕ σ κ : Type) where
  fingerprint : σₕ
  state : σ
  entry : LogEntry σₕ κ
deriving Repr

/-- What the search has found with one action label. Both of its fields count over the transitions of the
system that the search runs on; a post-state that violates a state constraint is not counted. -/
structure ActionStat where
  /-- The successful transitions with the label from the states that the search has expanded, one
  per post-state, whether the search had seen it or not. Summed over the labels, this is
  `BaseSearchContext.statesFound` minus the number of initial states. -/
  statesGenerated : Nat
  /-- The states that the search reached first by a transition with the label.
  Each state in the log but the initial ones counts under exactly one label,
  so the sum over the labels is the size of the log minus the number of initial states in it.

  A state reachable by several transitions counts under the label of the one that the order of
  exploration takes first, so the split among the labels differs between the sequential and the
  parallel search, and with the number of workers, though each state still counts once. The
  sequential search counts a state when it logs it; the parallel search counts it in the reduce phase,
  since a worker cannot tell whether another one has found the same state. -/
  distinctStates : Nat
deriving Lean.ToJson, Lean.FromJson, BEq, DecidableEq, Repr, Inhabited

/-- Count a transition with the label, and its post-state as distinct if `distinct?` is set. -/
@[inline]
def ActionStat.increment (distinct? : Bool) (stat : ActionStat) : ActionStat :=
  let ⟨sg, ds⟩ := stat
  if distinct? then ⟨sg.succ, ds.succ⟩ else ⟨sg.succ, ds⟩

/-- Statistics for a single action (transition label), for display. -/
structure ActionStatDisplay extends ActionStat where
  /-- The transition label, as its `Display` shows it: for a module's labels, a constructor
  (`ValueDisplay.ctorJson`), e.g. `send_msg(n=1, m=2)`. -/
  label : Lean.Json
  deriving Lean.ToJson, Lean.FromJson, Inhabited

/-- A table from the labels of `κ` to values, that is, a total function `κ → α`, stored as a `T α`.
The sequential search keeps its statistics in a table of `ActionStat`s; the parallel search keeps
each of the two counts in a table of `Nat`s, since its workers and its merge count them apart. -/
class LabelTable (κ : Type u) (T : outParam (Type → Type)) where
  /-- The table that maps every label to `a`. -/
  replicate : α → T α
  /-- Apply `f` to the value of `label`. -/
  modify (label : κ) (f : α → α) : T α → T α
  /-- Combine two tables label by label. -/
  zipWith (f : α → β → γ) : T α → T β → T γ
  /-- The labels with their values. A table may leave out the labels that still have the value it
  was replicated from. -/
  toList : T α → List (κ × α)

/-- A table with an entry for every label, at the label's encoding. -/
abbrev LabelVector (κ : Type u) [enc : FinEncodableInjOnly κ] (α : Type) := Vector α enc.card

/-- O(1) `modify`. Selected when `FinEncodableInjOnly κ` is available, as for the labels of a Veil
module. -/
instance [instf : FinEncodableInjOnly κ] [inste : Enumeration κ] : LabelTable κ (LabelVector κ) where
  replicate a := Vector.replicate instf.card a
  modify label f vec :=
    let idx := instf.encode label
    vec.modify idx.val f idx.isLt
  zipWith f vec1 vec2 := vec1.zipWith f vec2
  toList vec := inste.allValues.map fun label => (label, vec[instf.encode label])

/-- A table with entries for the labels whose values have been modified, and the value of the
others. -/
structure LabelHashMap (κ : Type u) [BEq κ] [Hashable κ] (α : Type) where
  -- CHECK Do we actually need this `default`?
  default : α
  map : Std.HashMap κ α

/-- The fallback for label types without `FinEncodableInjOnly`. -/
instance (priority := low) [BEq κ] [Hashable κ] : LabelTable κ (LabelHashMap κ) where
  replicate a := ⟨a, {}⟩
  -- Use `.alter` to ensure linear usage
  modify label f t := ⟨t.default, t.map.alter label fun a? => some (f (a?.getD t.default))⟩
  zipWith f t1 t2 :=
    let map := t1.map.fold (init := {}) fun map label a =>
      map.insert label (f a (t2.map.getD label t2.default))
    let map := t2.map.fold (init := map) fun map label b =>
      if t1.map.contains label then map else map.insert label (f t1.default b)
    ⟨f t1.default t2.default, map⟩
  toList t := t.map.toList

/-- The statistics of the labels in `stats`, with each label shown by its `Display`. -/
def ActionStatDisplay.ofTable [LabelTable κ T] [Display κ] (stats : T ActionStat) : List ActionStatDisplay :=
  (LabelTable.toList (κ := κ) stats).map fun (label, stat) => { stat with label := Display.display label }

/-- A model checker search context is parametrised by the system that's being
checked and the theory it's being checked under. -/
structure BaseSearchContext (σ κ σₕ : Type)
  [fp : StateFingerprint σ σₕ]
where
  violatingStates    : List (σₕ × ViolationKind)
  /-- Have we finished the search? If so, why? -/
  finished           : Option (TerminationReason σₕ)
  /-- The depth of the current BFS frontier being processed -/
  currentFrontierDepth : Nat
  /-- Total number of post-states generated (before deduplication) -/
  statesFound : Nat

structure SearchContextInvariants {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  -- NOTE: Although `params` is not used in the invariants below yet,
  -- we should better keep it here for future extensions.
  (params : SearchParameters ρ σ)
  (inQueue : σₕ → σ → Prop)
  (seen : σₕ → Prop) : Prop
where
  queue_sound        : ∀ x st, inQueue x st → sys.reachable st ∧ seen x ∧ x = fp.view st
  /-- Every seen fingerprint comes from a reachable state. Unreachable states may
      share its fingerprint even when the view is injective on reachable states. -/
  visited_sound      : ∀ x, seen x → ∃ st, sys.reachable st ∧ x = fp.view st

variable {ρ σ κ σₕ : Type} [fp : StateFingerprint σ σₕ]
  (params : SearchParameters ρ σ) (th : ρ) (fpSt : σₕ) (curr : σ)

@[inline]
def BaseSearchContext.hasFinished (ctx : BaseSearchContext σ κ σₕ) : Bool := ctx.finished.isSome

/-- The depth up to which ALL states have been fully explored (successors enqueued): the one before
the frontier's, and `0` while the frontier is at depth `0`. -/
@[inline]
def BaseSearchContext.completedDepth (ctx : BaseSearchContext σ κ σₕ) : Nat := ctx.currentFrontierDepth - 1

/-- The context of a search before any state is processed: the `numInitialStates` initial states
are all it has found. -/
@[inline]
def BaseSearchContext.initial (numInitialStates : Nat) : BaseSearchContext σ κ σₕ :=
  { violatingStates := [],
    finished := none,
    currentFrontierDepth := 0,
    statesFound := numInitialStates }

-- NOTE: Hopefully, if `outcomes` does not have any other reference, then
-- Lean should be able to reuse constructors inside it? Can we somehow
-- achieve zero additional memory allocation here?

-- NOTE: If this function is put inside `BaseSearchContext.checkViolationsAndMaybeTerminate`,
-- `specialize` of `List.filterMap` may not exhibit
def checkViolationsAndMaybeTerminate
  (completedDepth : Nat)
  (hasSuccessfulTransition : Bool)
  (assertionFailures : List (FailedTransition κ Int σ)) :
  List (σₕ × ViolationKind) × Option (EarlyTerminationReason σₕ) :=
  -- Compute all violation conditions once
  let safetyViolations := violatedInvariantNames params th curr
  let safetyViolation := !safetyViolations.isEmpty
  let deadlock := !hasSuccessfulTransition && !params.terminating.holdsOn th curr

  -- Collect all violations to add in a single list
  let newViolations : List (σₕ × ViolationKind) :=
    (if safetyViolation then [(fpSt, .safetyFailure safetyViolations)] else []) ++
    (if deadlock then [(fpSt, .deadlock)] else []) ++
    -- NOTE: This should be further optimized to avoid extra memory allocation
    (assertionFailures.map fun f => (fpSt, .assertionFailure f.error))

  let earlyTermination := params.earlyTerminationConditions.findSome? fun
    | .foundViolatingState => if safetyViolation then some (.foundViolatingState fpSt safetyViolations) else none
    | .reachedDepthBound bound => if completedDepth >= bound then some (.reachedDepthBound bound) else none
    | .deadlockOccurred => if deadlock then some (.deadlockOccurred fpSt) else none
    | .assertionFailed => assertionFailures.head?.map fun f => .assertionFailed fpSt f.error
    | .cancelled => none  -- Cancellation is handled externally via cancel token, not through early termination conditions
  (newViolations, earlyTermination)

/-- Process the current state, queuing its successors. `trs` is `sys.tr th curr`. -/
-- @[inline, specialize]
def BaseSearchContext.processState
  (trs : Transitions κ Int σ)
  (ctx : BaseSearchContext σ κ σₕ) : BaseSearchContext σ κ σₕ × Option (List (κ × σ)) :=
  let hasSuccessfulTransition := !trs.successes.isEmpty
  let completedDepth := ctx.completedDepth
  let (newViolations, earlyTermination) :=
    checkViolationsAndMaybeTerminate params th fpSt curr completedDepth hasSuccessfulTransition trs.failures
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
  (ctx, if earlyTermination.isSome then none else some trs.successes)

/-- Merge the violations and the found states of `ctx2` into `ctx1`, keeping the depths of `ctx1`. -/
def BaseSearchContext.mergeWithoutDepthChange (ctx1 ctx2 : BaseSearchContext σ κ σₕ) : BaseSearchContext σ κ σₕ :=
  { violatingStates := ctx1.violatingStates ++ ctx2.violatingStates,
    finished := ctx1.finished.or ctx2.finished,
    currentFrontierDepth := ctx1.currentFrontierDepth,
    statesFound := ctx1.statesFound + ctx2.statesFound }

theorem BaseSearchContext.mergeWithoutDepthChange_foldl_description
  (acc : BaseSearchContext σ κ σₕ) (ctxs : List (BaseSearchContext σ κ σₕ)) :
  let res := ctxs.foldl (init := acc) BaseSearchContext.mergeWithoutDepthChange
  res.finished = acc.finished.or ((ctxs.find? (·.hasFinished)).bind (fun x => x.finished)) := by
  dsimp only
  induction ctxs generalizing acc with
  | nil => simp [List.foldl]
  | cons ctx ctxs ih =>
    dsimp [List.foldl, List.find?, BaseSearchContext.hasFinished]
    rw [ih] ; clear ih
    unfold mergeWithoutDepthChange ; dsimp
    rcases acc.finished with _ | _
    on_goal 2=> rfl
    dsimp ; rcases h : ctx.finished with _ | _
    on_goal 2=> grind
    dsimp ; rfl

end Veil.ModelChecker.Concrete
