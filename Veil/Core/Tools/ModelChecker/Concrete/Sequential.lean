module

public import Veil.Core.Tools.ModelChecker.Concrete.Core
public import Veil.Core.Tools.ModelChecker.Concrete.Progress
public import Veil.Core.Tools.ModelChecker.Concrete.SequentialLemmas

public section

namespace Veil.ModelChecker.Concrete
open Std
open Veil fQueue

variable {ρ σ κ σₕ asm : Type} [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm]
  (params : SearchParameters ρ σ) (th : ρ)

-- CHECK inline this later? seems a good target to inline
/-- Process a single neighbor node during BFS traversal: the `idx`-th success of the state with
fingerprint `fpSt`, at depth `nextDepth`. If the neighbor has been seen, return the current
context unchanged. Otherwise, add it to the log and enqueue it. -/
-- @[inline, specialize]
def SequentialSearchContext.tryExploreNeighbor
  (fpSt : σₕ)         -- fingerprint of state we're coming from (pre-state), for logging
  (nextDepth : Nat)   -- depth of the current state + 1
  (idx : Nat)         -- position of the transition among the successes of the pre-state
  (sctx : SequentialSearchContext σ κ σₕ asm)
  (label : κ)
  (succ : σ)
  : SequentialSearchContext σ κ σₕ asm :=
  let ⟨ctx, log, sq⟩ := sctx
  let fingerprint := fp.view succ
  if log.contains fingerprint then
    ⟨{ ctx with actionStatsMap := ActionStatUpdate.increment label false ctx.actionStatsMap }, log, sq⟩
  else
    ⟨{ ctx with actionStatsMap := ActionStatUpdate.increment label true ctx.actionStatsMap },
      log.insert fingerprint (.step fpSt label idx), sq.enqueue ⟨fingerprint, succ, nextDepth⟩⟩

-- CHECK inline this later? seems a good target to inline
-- @[inline, specialize]
def SequentialSearchContext.processSuccessors
  (fpSt : σₕ)     -- fingerprint of curr
  (depth : Nat)   -- depth of curr
  (start : Nat)     -- usually 0
  (successors : List (κ × σ))
  (sctx : SequentialSearchContext σ κ σₕ asm) : SequentialSearchContext σ κ σₕ asm :=
  let nextDepth := depth + 1
  successors.foldlIdx (start := start) (init := sctx) fun i current_sctx (tr, postState) =>
    SequentialSearchContext.tryExploreNeighbor fpSt nextDepth i current_sctx tr postState

def SequentialSearchContext.processState
  (fpSt : σₕ)
  (depth : Nat)  -- depth of the current state
  (curr : σ)
  (trs : Transitions κ Int σ)
  (sctx : SequentialSearchContext σ κ σₕ asm)
  -- Depth tracking information computed by caller
  (newFrontierDepth : Nat) :
  SequentialSearchContext σ κ σₕ asm :=
  let ⟨ctx, log, sq⟩ := sctx
  let (ctx', outcomesOpt) := ctx.processState params th fpSt curr trs
  match outcomesOpt with
  | none =>
    -- Early termination case: processState returned none, meaning we're terminating early
    -- CHECK What does this update mean?
    ⟨{ ctx' with
      currentFrontierDepth := newFrontierDepth
    }, log, sq⟩
  | some successfulTransitions =>
    -- CHECK Is it useful/possible to remove the call to `successfulTransitions.length`?
    let newStatesFound := ctx'.statesFound + successfulTransitions.length
    let ctx'' := { ctx' with
      currentFrontierDepth := newFrontierDepth
      statesFound := newStatesFound
    }
    SequentialSearchContext.processSuccessors fpSt depth 0 successfulTransitions ⟨ctx'', log, sq⟩

/-- Perform one step of BFS. -/
-- @[inline, specialize]
def SequentialSearchContext.bfsStep
  (outcomesComputer : ρ → σ → Transitions κ Int σ)
  (sctx : SequentialSearchContext σ κ σₕ asm) : SequentialSearchContext σ κ σₕ asm :=
  let ⟨ctx, log, sq⟩ := sctx
  match sq.dequeue? with
  | none =>
    -- Queue is empty: finished searching
    ⟨{ ctx with finished := some (.exploredAllReachableStates) }, log, sq⟩
  | some (⟨fpSt, curr, depth⟩, q_tail) =>
    -- Update the frontier depth when we move to a new frontier level
    let newFrontierDepth :=
      if depth > ctx.currentFrontierDepth then
        depth  -- All states at previous depth are now fully explored
      else
        ctx.currentFrontierDepth
    -- Process curr: add successors to seen, enqueue them, and dequeue curr
    -- processState handles the complete lifecycle of processing a state
    SequentialSearchContext.processState params th fpSt depth curr (outcomesComputer th curr)
      ⟨ctx, log, q_tail⟩ newFrontierDepth

/-! ### The search invariants -/

theorem SequentialSearchContext.processSuccessors_preserves_invs
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}
  {sctx : SequentialSearchContext σ κ σₕ asm}
  (h_not_finished : sctx.base.finished = .none)
  {fpSt depth} (start : Nat) (curr : σ) {succs}
  (h_reachable : sys.reachable curr)
  (h_succs : ∀ (label : κ) (st : σ),
    (label, st) ∈ succs ↔ (label, ExecutionOutcome.success st) ∈ sys.tr th curr)
  (sctx_invs : SequentialSearchContextInvariants sys params (.some curr) sctx) :
  SequentialSearchContextInvariants sys params (.some curr) (sctx.processSuccessors fpSt depth start succs) := by
  unfold processSuccessors ; dsimp
  -- need to attach some proofs
  have htmp := List.unattach_attachWith (p := fun a => (a.1, ExecutionOutcome.success a.2) ∈ sys.tr th curr)
    (l := succs) (H := by simp [← h_succs])
  generalize succs.attachWith _ _ = succs' at htmp
  rw [← htmp] ; clear htmp h_succs
  induction succs' generalizing sctx start with
  | nil => simp ; assumption
  | cons x succs ih =>
    rcases x with ⟨⟨label, postState⟩, h⟩ ; dsimp [List.foldlIdx] ; apply ih
    · fun_cases tryExploreNeighbor <;> dsimp at h_not_finished <;> simp [h_not_finished]
    · clear ih
      fun_cases tryExploreNeighbor
      on_goal 1=> cases sctx_invs ; constructor <;> assumption
      -- enqueue case
      rename_i ctx log sq fingerprint h_not_seen ; subst fingerprint
      simp at h_not_seen h_not_finished
      rcases sctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed⟩ ; simp at h_q_sound
      have h_post_reachable : sys.reachable postState :=
        .step curr postState h_reachable ⟨label, h⟩
      constructor ; on_goal 1=> constructor
      all_goals dsimp only at * ; grind

theorem SequentialSearchContext.processSuccessors_add_to_seen
  {sctx : SequentialSearchContext σ κ σₕ asm}
  {fpSt depth start succs} :
  letI res := sctx.processSuccessors fpSt depth start succs
  ∀ l v, (l, v) ∈ succs ∨ fp.view v ∈ sctx.log → (fp.view v) ∈ res.log := by
  unfold processSuccessors ; dsimp
  induction succs generalizing sctx start with
  | nil => simp
  | cons x succs ih =>
    rcases x with ⟨label, postState⟩
    dsimp [processSuccessors, List.foldlIdx]
    intro l v hv
    apply ih l v
    fun_cases tryExploreNeighbor <;> dsimp only at * <;> grind

theorem SequentialSearchContext.bfsStep_preserves_invs
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}
  {sctx : SequentialSearchContext σ κ σₕ asm}
  (h_not_finished : sctx.base.hasFinished = false)
  (sctx_invs : SequentialSearchContextInvariants sys params .none sctx) :
  SequentialSearchContextInvariants sys params .none (sctx.bfsStep params th sys.tr) := by
  rcases sctx with ⟨ctx, log, sq⟩ ; rcases sctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed⟩ ; dsimp only at * ; simp at h_q_sound
  simp [BaseSearchContext.hasFinished] at h_not_finished
  unfold SequentialSearchContext.bfsStep ; dsimp only
  rcases h_deq : sq.dequeue? with _ | ⟨⟨fpSt, curr, depth⟩, q_tail⟩ <;> dsimp only
  on_goal 1=>
    -- easy case
    constructor ; on_goal 1=> constructor
    all_goals (try dsimp only) ; try solve | assumption | grind
  -- simplify the depth expression
  generalize h_eq_nfd : (if depth > ctx.currentFrontierDepth then depth else ctx.currentFrontierDepth) = newFrontierDepth
  -- now process the state
  dsimp [SequentialSearchContext.processState]
  fun_cases BaseSearchContext.processState params th fpSt curr (sys.tr th curr) ctx
  rename_i hasSuccessfulTransition completedDepth newViolations
    earlyTermination h_eq_checkvio ctx' ctx''
  subst completedDepth ; dsimp only
  revert h_eq_checkvio ; fun_cases checkViolationsAndMaybeTerminate params th fpSt curr ctx.completedDepth hasSuccessfulTransition (sys.tr th curr).failures
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
        -- nothing may be left for `dsimp only` to do: `trs` is `sys.tr th curr`, not a pair to project
        all_goals (try dsimp only at *) ; (try solve | assumption | grind))
  subst ctx' ctx'' ; dsimp ; rw [h_not_finished]
  -- normal case, in transit
  apply SequentialSearchContextInvariants.finish_stateInTransit (curr := curr)
  · apply SequentialSearchContext.processSuccessors_preserves_invs
    · rfl
    · grind
    · introv ; exact Transitions.mem_success_iff.symm
    · constructor ; on_goal 1=> constructor
      all_goals dsimp only [isStableClosed] at * ; grind
  · introv ; intro h1 ; apply SequentialSearchContext.processSuccessors_add_to_seen l v
    simp ; grind [Transitions.mem_success_iff]

/-! ### The log: what it says about the queued states and the recorded violations -/

section LogSound

variable {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}

theorem SequentialSearchContext.processSuccessors_log_sound
  {sctx : SequentialSearchContext σ κ σₕ asm} {rep : σₕ → Option σ} {dep : σₕ → Nat}
  (hls : SequentialSearchContext.LogSound sys params sctx rep dep)
  {fpSt : σₕ} {curr : σ} {depth : Nat}
  (hrep : rep fpSt = some curr) :
  ∃ rep' dep', SequentialSearchContext.LogSound sys params
    (sctx.processSuccessors fpSt depth 0 (sys.tr th curr).successes) rep' dep' := by
  unfold processSuccessors ; dsimp
  rw [List.foldlIdx_eq_foldl_zipIdx, ← List.foldl_attach]
  generalize (sys.tr th curr).successes.zipIdx.attach = succs
  induction succs generalizing sctx rep dep with
  | nil => exact ⟨rep, dep, hls⟩
  | cons x succs ih =>
    rcases x with ⟨⟨⟨label, succ⟩, idx⟩, hmem⟩
    dsimp [List.foldl]
    fun_cases tryExploreNeighbor
    · apply ih <;> try assumption
      rcases hls with ⟨⟨hv, hf⟩, hlog, hq⟩ ; exact ⟨⟨hv, hf⟩, hlog, hq⟩    -- `hls` is not affected by the changed fields
    · rename_i ctx log sq fingerprint hnotseen ; subst fingerprint
      rcases hls with ⟨⟨hv, hf⟩, hlog, hq⟩
      dsimp only at *
      simp at hnotseen
      have hle : ∀ x s, rep x = some s → repUpdate rep (fp.view succ) succ x = some s := by
        unfold repUpdate ; grind [LogInvariants.mem_of_rep_isSome]
      apply ih (rep := repUpdate rep (fp.view succ) succ)
        (dep := depUpdate dep (fp.view succ) (dep fpSt + 1))
      on_goal 2=> unfold repUpdate ; grind [LogInvariants.mem_of_rep_isSome]
      constructor
      · exact ⟨fun v hv' => (hv v hv').mono sys hle, hf.mono sys hle⟩
      · rw [logLookup_insert] ; apply hlog.update_step <;> try trivial
        all_goals grind [List.mem_zipIdx_iff_getElem?]
      · intro item hi ; rw [fQueue.mem_enqueue_iff] at hi ; unfold repUpdate ; grind [LogInvariants.mem_of_rep_isSome]

theorem SequentialSearchContext.processState_log_sound
  {sctx : SequentialSearchContext σ κ σₕ asm} {rep : σₕ → Option σ} {dep : σₕ → Nat}
  (hls : SequentialSearchContext.LogSound sys params sctx rep dep)
  {fpSt : σₕ} {depth : Nat} {curr : σ}
  (hrep : rep fpSt = some curr)
  {newFrontierDepth : Nat} :
  ∃ rep' dep', SequentialSearchContext.LogSound sys params
    (sctx.processState params th fpSt depth curr (sys.tr th curr) newFrontierDepth) rep' dep' := by
  rcases sctx with ⟨ctx, log, sq⟩
  rcases hls with ⟨⟨hv, hf⟩, hlog, hq⟩ ; dsimp only at *
  have hsound := BaseSearchContext.processState_sound sys params (fpSt := fpSt) (curr := curr) ctx hrep hv hf
  have hsnd := BaseSearchContext.processState_snd params th fpSt curr (sys.tr th curr) ctx
  unfold SequentialSearchContext.processState ; dsimp only
  generalize ctx.processState params th fpSt curr (sys.tr th curr) = pr at hsound hsnd ⊢
  rcases pr with ⟨ctx', outcomesOpt⟩
  dsimp only at *
  obtain ⟨hv', hf'⟩ := hsound
  rcases outcomesOpt with _ | succs
  · exact ⟨rep, dep, ⟨hv', hf'⟩, hlog, hq⟩
  · obtain rfl := hsnd _ rfl
    exact processSuccessors_log_sound params th ⟨⟨hv', hf'⟩, hlog, hq⟩ hrep

theorem SequentialSearchContext.bfsStep_log_sound
  {sctx : SequentialSearchContext σ κ σₕ asm}
  (h : ∃ rep dep, SequentialSearchContext.LogSound sys params sctx rep dep) :
  ∃ rep dep, SequentialSearchContext.LogSound sys params (sctx.bfsStep params th sys.tr) rep dep := by
  obtain ⟨rep, dep, hls⟩ := h
  rcases sctx with ⟨ctx, log, sq⟩
  unfold bfsStep ; dsimp only
  rcases hdeq : sq.dequeue? with _ | ⟨⟨fpSt, curr, depth⟩, q_tail⟩ <;> dsimp only
  · rcases hls with ⟨⟨hv, _⟩, hlog, hq⟩ ; dsimp only at *
    exact ⟨rep, dep, ⟨hv, by simp [TerminationSound]⟩, hlog, hq⟩
  · have hmem : (⟨fpSt, curr, depth⟩ : QueueItem σₕ σ) ∈ sq := fQueue.mem_of_dequeue _ _ _ hdeq
    have hrep := hls.queue_rep _ hmem
    have hls' : SequentialSearchContext.LogSound sys params ⟨ctx, log, q_tail⟩ rep dep :=
      ⟨hls.toViolationTerminationSound, hls.log_invs,
        fun item hitem => hls.queue_rep item (fQueue.mem_of_mem_dequeue_tail _ _ _ _ hdeq hitem)⟩
    exact processState_log_sound params th hls' hrep

end LogSound

omit th in
/-- `sctx` marked as cancelled, which finishes it. -/
def LawfulSequentialSearchContext.setCancelled {th : ρ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}
  (sctx : LawfulSequentialSearchContext (fp := fp) sys params) :
  { sctx : LawfulSequentialSearchContext (fp := fp) sys params // sctx.val.base.finished.isSome } :=
  let ⟨⟨ctx, log, sq⟩, h_sctx⟩ := sctx
  ⟨⟨⟨{ ctx with finished := some (.earlyTermination .cancelled) }, log, sq⟩,
    ⟨SequentialSearchContextInvariants.setCancelled sys params h_sctx.1,
      h_sctx.2.elim fun rep h => h.elim fun dep h => ⟨rep, dep, SequentialSearchContext.LogSound.setCancelled sys params h⟩⟩⟩,
    rfl⟩

omit th in
/-- The search loop of `breadthFirstSearchSequential`, from `sctx`. It returns only once the search
has finished, so the context it returns records why. -/
def breadthFirstSearchSequential.loop {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (updateTimeInterval : Nat)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken)
  (sctx : LawfulSequentialSearchContext (fp := fp) sys params)
  (lastUpdateTime : Nat) :
  m { sctx : LawfulSequentialSearchContext (fp := fp) sys params // sctx.val.base.finished.isSome } := do
  if h_finished : sctx.val.base.finished.isSome then
    return ⟨sctx, h_finished⟩
  else
    have h_not_finished : sctx.val.base.hasFinished = false := by
      simpa [BaseSearchContext.hasFinished] using h_finished
    let sctx_val := sctx.val
    have h_sctx := sctx.property
    let oldFrontierDepth := sctx_val.base.currentFrontierDepth
    let sctx' := sctx_val.bfsStep params th sys.tr
    have h_sctx' : SequentialSearchContextInvariants sys params .none sctx' ∧
        ∃ rep dep, SequentialSearchContext.LogSound sys params sctx' rep dep :=
      ⟨SequentialSearchContext.bfsStep_preserves_invs params th h_not_finished h_sctx.1,
        SequentialSearchContext.bfsStep_log_sound params th h_sctx.2⟩
    match heq : sctx' with
    | ⟨ctx', log', sq'⟩ =>
      -- If we found a violation, mark it so handoff is prevented
      trySetViolationFound progressInstanceId ctx'
      tryUpdateProgressWithNewFrontierDepth progressInstanceId oldFrontierDepth ctx' sq'.size log'.size
      let newtime? ← checkCancellationWithPeriodicUpdate progressInstanceId lastUpdateTime updateTimeInterval cancelToken ctx' sq'.size log'.size
      let sctx : LawfulSequentialSearchContext (fp := fp) sys params := Subtype.mk ⟨ctx', log', sq'⟩ (heq.symm ▸ h_sctx')
      match newtime? with
      | .updateTime t => breadthFirstSearchSequential.loop sys updateTimeInterval progressInstanceId cancelToken sctx t
      | .searchCancelled => return sctx.setCancelled params
      | .noUpdate => breadthFirstSearchSequential.loop sys updateTimeInterval progressInstanceId cancelToken sctx lastUpdateTime
partial_fixpoint

-- @[specialize]
omit th in
def breadthFirstSearchSequential {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (updateTimeInterval : Nat)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken) :
  m { sctx : LawfulSequentialSearchContext (fp := fp) sys params // sctx.val.base.finished.isSome } := do
  let res ← breadthFirstSearchSequential.loop (fp := fp) params sys updateTimeInterval progressInstanceId cancelToken
    (Subtype.mk (SequentialSearchContext.initial sys) (SequentialSearchContext.initial_invs sys params)) 0
  let ⟨⟨⟨ctx, log, sq⟩, _⟩, _⟩ := res
  updateProgressDuringBFS progressInstanceId ctx sq.size log.size
  return res

end Veil.ModelChecker.Concrete
