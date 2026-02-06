import Veil.Core.Tools.ModelChecker.ConcreteNew.Core
import Veil.Core.Tools.ModelChecker.ConcreteNew.Progress
import Veil.Core.Tools.ModelChecker.ConcreteNew.SequentialLemmas

namespace Veil.ModelChecker.Concrete
open Std
open Veil fQueue

variable {ρ σ κ σₕ : Type} [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ]
  (params : SearchParameters ρ σ) (th : ρ)

-- Use `.alter` to ensure linear usage
-- NOTE: This doesn't seem `specialize`d; what happened?
@[inline]
def updateActionStatsMap (distinct? : Bool) (label : κ) (amap : Std.HashMap κ ActionStat) : Std.HashMap κ ActionStat :=
  if distinct? then
    amap.alter label fun
      | some ⟨as, ds⟩ => Option.some ⟨as + 1, ds + 1⟩
      | none => Option.some { statesGenerated := 1, distinctStates := 1 }
  else
    amap.alter label fun
      | some ⟨as, ds⟩ => Option.some ⟨as + 1, ds⟩
      | none => Option.some { statesGenerated := 1, distinctStates := 0 }

-- CHECK inline this later? seems a good target to inline
/-- Process a single neighbor node during BFS traversal.
If the neighbor has been seen, return the current context unchanged.
Otherwise, add it to seen set and log, then enqueue it. -/
-- @[inline, specialize]
def SequentialSearchContext.tryExploreNeighbor
  (fpSt : σₕ)         -- fingerprint of state we're coming from (pre-state), for logging
  (nextDepth : Nat)       -- depth of the current state + 1
  (sctx : SequentialSearchContext σ κ σₕ)
  (label : κ)
  (succ : σ)
  : SequentialSearchContext σ κ σₕ :=
  let (ctx, sq) := sctx
  let fingerprint := fp.view succ
  if ctx.seen.contains fingerprint then
    ({ ctx with actionStatsMap := updateActionStatsMap false label ctx.actionStatsMap }, sq)
  else
    ({ ctx with
      seen := ctx.seen.insert fingerprint,
      log  := ctx.log.insert fingerprint (fpSt, label),
      actionStatsMap := updateActionStatsMap true label ctx.actionStatsMap,
    }, sq.enqueue ⟨fingerprint, succ, nextDepth⟩)

-- CHECK inline this later? seems a good target to inline
-- NOTE: `foldl` is not specialized here; why?
-- @[inline, specialize]
def SequentialSearchContext.processSuccessors
  (fpSt : σₕ)     -- fingerprint of curr
  (depth : Nat)   -- depth of curr
  (successors : List (κ × σ))
  (sctx : SequentialSearchContext σ κ σₕ) : SequentialSearchContext σ κ σₕ :=
  let nextDepth := depth + 1
  successors.foldl (init := sctx) fun current_sctx (tr, postState) =>
    SequentialSearchContext.tryExploreNeighbor fpSt nextDepth current_sctx tr postState

def SequentialSearchContext.processState
  (fpSt : σₕ)
  (depth : Nat)  -- depth of the current state
  (curr : σ)
  (outcomes : List (κ × ExecutionOutcome ℤ σ))
  (sctx : SequentialSearchContext σ κ σₕ)
  -- Depth tracking information computed by caller
  (newCompletedDepth : Nat)
  (newFrontierDepth : Nat) :
  SequentialSearchContext σ κ σₕ :=
  let (ctx, sq) := sctx
  let (ctx', outcomesOpt) := ctx.processState params th fpSt curr outcomes
  match outcomesOpt with
  | none =>
    -- Early termination case: processState returned none, meaning we're terminating early
    -- CHECK What does this update mean?
    ({ ctx' with
      completedDepth := newCompletedDepth,
      currentFrontierDepth := newFrontierDepth
    }, sq)
  | some successfulTransitions =>
    -- CHECK Is it useful/possible to remove the call to `successfulTransitions.length`?
    let newStatesFound := ctx.statesFound + successfulTransitions.length
    let ctx'' := { ctx with
      completedDepth := newCompletedDepth,
      currentFrontierDepth := newFrontierDepth
      statesFound := newStatesFound
    }
    SequentialSearchContext.processSuccessors fpSt depth successfulTransitions (ctx'', sq)

/-- Perform one step of BFS. -/
-- @[inline, specialize]
def SequentialSearchContext.bfsStep
  (outcomesComputer : ρ → σ → List (κ × ExecutionOutcome ℤ σ))
  (sctx : SequentialSearchContext σ κ σₕ) : SequentialSearchContext σ κ σₕ :=
  let (ctx, sq) := sctx
  match sq.dequeue? with
  | none =>
    -- Queue is empty: finished searching
    ({ ctx with finished := some (.exploredAllReachableStates) }, sq)
  | some (⟨fpSt, curr, depth⟩, q_tail) =>
    -- Update completed depth when we move to a new frontier level
    let (newCompletedDepth, newFrontierDepth) :=
      if depth > ctx.currentFrontierDepth then
        (depth - 1, depth)  -- All states at previous depth are now fully explored
      else
        (ctx.completedDepth, ctx.currentFrontierDepth)
    -- Process curr: add successors to seen, enqueue them, and dequeue curr
    -- processState handles the complete lifecycle of processing a state
    SequentialSearchContext.processState params th fpSt depth curr (outcomesComputer th curr)
      (ctx, q_tail) newCompletedDepth newFrontierDepth

theorem SequentialSearchContext.processSuccessors_preserves_invs
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) ℤ κ (List (κ × ExecutionOutcome ℤ σ)) th}
  {sctx : SequentialSearchContext σ κ σₕ}
  (h_not_finished : sctx.1.finished = .none)
  {fpSt depth} (curr : σ) {succs}
  (h_reachable : sys.reachable curr)
  (h_succs : ∀ (label : κ) (st : σ),
    (label, st) ∈ succs ↔ (label, ExecutionOutcome.success st) ∈ sys.tr th curr)
  (sctx_invs : SequentialSearchContextInvariants sys params (.some curr) sctx) :
  SequentialSearchContextInvariants sys params (.some curr) (sctx.processSuccessors fpSt depth succs) := by
  unfold processSuccessors ; dsimp
  -- need to attach some proofs
  have htmp := List.unattach_attachWith (p := fun a => (a.1, ExecutionOutcome.success a.2) ∈ sys.tr th curr)
    (l := succs) (H := by simp [← h_succs])
  generalize succs.attachWith _ _ = succs' at htmp
  rw [← htmp] ; clear htmp h_succs
  induction succs' generalizing sctx with
  | nil => simp ; assumption
  | cons x succs ih =>
    rcases x with ⟨⟨label, postState⟩, h⟩ ; dsimp [List.foldl] ; apply ih
    · fun_cases tryExploreNeighbor <;> dsimp at h_not_finished <;> simp [h_not_finished]
    · clear ih
      fun_cases tryExploreNeighbor
      on_goal 1=> cases sctx_invs ; constructor <;> assumption
      -- enqueue case
      rename_i ctx sq fingerprint h_not_seen ; subst fingerprint
      simp at h_not_seen h_not_finished
      rcases sctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed⟩
      constructor ; on_goal 1=> constructor
      all_goals dsimp only at * ; grind

theorem SequentialSearchContext.processSuccessors_add_to_seen
  {sctx : SequentialSearchContext σ κ σₕ}
  {fpSt depth succs} :
  letI res := sctx.processSuccessors fpSt depth succs
  ∀ l v, (l, v) ∈ succs.reverse → (fp.view v) ∈ res.1.seen := by
  unfold processSuccessors ; dsimp
  -- use `foldr` to make induction easier
  rw [List.foldl_eq_foldr_reverse]
  generalize succs.reverse = succs
  induction succs with
  | nil => simp
  | cons x succs ih =>
    rcases x with ⟨label, postState⟩ ; dsimp [List.foldr]
    simp only [List.mem_cons] ; introv ; intro h1 ; rcases h1 with h1 | h1
    · injection h1 with h1 h2 ; subst l v
      fun_cases tryExploreNeighbor fpSt (depth + 1) (List.foldr _ sctx succs) label postState <;> grind
    · rewrite (occs := .pos [1]) [tryExploreNeighbor]
      split_ifs with h <;> dsimp <;> grind

theorem SequentialSearchContext.bfsStep_preserves_invs
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) ℤ κ (List (κ × ExecutionOutcome ℤ σ)) th}
  {sctx : SequentialSearchContext σ κ σₕ}
  (h_not_finished : sctx.1.hasFinished = false)
  (sctx_invs : SequentialSearchContextInvariants sys params .none sctx) :
  SequentialSearchContextInvariants sys params .none (sctx.bfsStep params th sys.tr) := by
  rcases sctx with ⟨ctx, sq⟩ ; rcases sctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed⟩ ; dsimp only at *
  simp [BaseSearchContext.hasFinished] at h_not_finished
  unfold SequentialSearchContext.bfsStep ; dsimp only
  rcases h_deq : sq.dequeue? with _ | ⟨⟨fpSt, curr, depth⟩, q_tail⟩ <;> dsimp only
  on_goal 1=>
    -- easy case
    constructor ; on_goal 1=> constructor
    all_goals dsimp only ; try solve | assumption | grind
  -- simplify the depth expression
  generalize h_eq_ncd : (if depth > ctx.currentFrontierDepth then depth - 1 else ctx.completedDepth) = newCompleteDepth
  generalize h_eq_nfd : (if depth > ctx.currentFrontierDepth then depth else ctx.currentFrontierDepth) = newFrontierDepth
  have tmp : (if depth > ctx.currentFrontierDepth then (depth - 1, depth) else (ctx.completedDepth, ctx.currentFrontierDepth))
    = (newCompleteDepth, newFrontierDepth) := by grind
  rw [tmp] ; clear tmp
  -- now process the state
  dsimp [SequentialSearchContext.processState]
  fun_cases BaseSearchContext.processState params th fpSt curr (sys.tr th curr) ctx
  rename_i succs exns h_eq_part hasSuccessfulTransition completedDepth newViolations
    earlyTermination h_eq_checkvio ctx' ctx''
  subst completedDepth ; dsimp only
  revert h_eq_checkvio ; fun_cases checkViolationsAndMaybeTerminate params th fpSt curr ctx.completedDepth hasSuccessfulTransition exns
  rename_i safetyViolations safetyViolation deadlock tmp1 tmp2
  intro htmp ; injection htmp with h_eq_newvio h_eq_earlyterm ; subst tmp1 tmp2
  -- see if early termination happened
  rcases earlyTermination with _ | earlyTermination
  on_goal 2=>
    -- early termination case
    subst ctx' ctx'' ; dsimp
    cases earlyTermination
    all_goals (try solve
      | dsimp
        constructor ; on_goal 1=> constructor
        all_goals dsimp only at * ; try solve | assumption | grind)
  subst ctx' ctx'' ; dsimp ; rw [h_not_finished]
  -- normal case, in transit
  apply SequentialSearchContextInvariants.finish_stateInTransit (curr := curr)
  · apply SequentialSearchContext.processSuccessors_preserves_invs
    · rfl
    · grind
    · introv ; rw [← partitionExecutionOutcome.fst_spec, h_eq_part]
    · constructor ; on_goal 1=> constructor
      all_goals dsimp only [isStableClosed] at * ; try grind
  · introv ; intro h1 ; apply SequentialSearchContext.processSuccessors_add_to_seen l v
    simp ; rw [← partitionExecutionOutcome.fst_spec, h_eq_part] at h1 ; exact h1

@[inline]
def updateProgressDuringBFS [Monad m]
  [MonadLiftT BaseIO m] [MonadLiftT IO m] [Repr κ]
  (progressInstanceId : Nat)
  (ctx : BaseSearchContext σ κ σₕ)
  (sq : fQueue (QueueItem σₕ σ)) : m Unit := do
  updateProgress progressInstanceId
    ctx.currentFrontierDepth ctx.statesFound ctx.seen.size sq.size
    (toActionStatsList ctx.actionStatsMap)

inductive SequentialSearchPeriodicProgressUpdate where
  | searchCancelled
  | noUpdate
  | updateTime (newtime : Nat)

-- @[specialize]
omit th in
def breadthFirstSearchSequential {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m] [Repr κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken) :
  m (SequentialSearchContext σ κ σₕ) := do
  let mut sctx : LawfulSequentialSearchContext (fp := fp) sys params :=
    Subtype.mk (SequentialSearchContext.initial sys) (SequentialSearchContextInvariants.initial sys params)
  let mut lastUpdateTime : Nat := 0
  let mut cancelled := false
  while h_not_finished : sctx.val.1.hasFinished = false do
    let ⟨sctx_val, h_sctx⟩ := sctx
    let oldFrontierDepth := sctx_val.1.currentFrontierDepth
    let sctx' := sctx_val.bfsStep params th sys.tr
    let h_sctx' : SequentialSearchContextInvariants sys params .none sctx' :=
      SequentialSearchContext.bfsStep_preserves_invs params th h_not_finished h_sctx
    match heq : sctx' with
    | ⟨ctx', sq'⟩ =>
      -- If we found a violation, mark it so handoff is prevented
      trySetViolationFound ctx'
      tryUpdateProgressWithNewFrontierDepth oldFrontierDepth ctx' sq'
      let newtime? ← checkCancellation lastUpdateTime cancelToken ctx' sq'
      sctx := Subtype.mk (ctx', sq') (heq.symm ▸ h_sctx')
      match newtime? with
      | .updateTime t => lastUpdateTime := t
      | .searchCancelled => cancelled := true ; break
      | .noUpdate => pure ()
  let ⟨sctx_val, _⟩ := sctx
  let (ctx, sq) := sctx_val
  updateProgressDuringBFS progressInstanceId ctx sq
  if cancelled then
    let ctx' := { ctx with finished := some (.earlyTermination .cancelled) }
    return (ctx', sq)
  else
    return (ctx, sq)
where
 -- NOTE: Any attempt to inline these functions might lead to
 -- **significant** performance degradation, due to certain reason
 trySetViolationFound (ctx : BaseSearchContext σ κ σₕ) : m Unit := do
  if let some (.earlyTermination cond) := ctx.finished then
    if EarlyTerminationReason.isViolation cond then setViolationFound progressInstanceId
 tryUpdateProgressWithNewFrontierDepth
  (oldFrontierDepth : Nat)
  (ctx : BaseSearchContext σ κ σₕ)
  (sq : fQueue (QueueItem σₕ σ)) : m Unit := do
  if ctx.currentFrontierDepth > oldFrontierDepth then
    updateProgressDuringBFS progressInstanceId ctx sq
 checkCancellation
  (lastUpdateTime : Nat)
  (cancelToken : IO.CancelToken)
  (ctx : BaseSearchContext σ κ σₕ)
  (sq : fQueue (QueueItem σₕ σ)) : m SequentialSearchPeriodicProgressUpdate := do
  let now ← IO.monoMsNow
  if now - lastUpdateTime ≥ 1000 then
    if ← shouldStop cancelToken progressInstanceId then
      return .searchCancelled
    else
      updateProgressDuringBFS progressInstanceId ctx sq
      return .updateTime now
  else
    return .noUpdate

end Veil.ModelChecker.Concrete
