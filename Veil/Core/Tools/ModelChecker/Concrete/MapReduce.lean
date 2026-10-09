module

public import Veil.Core.Tools.ModelChecker.Concrete.MapReduceLemmas
public import Veil.Core.Tools.ModelChecker.Concrete.Progress
public import Veil.Core.Tools.ModelChecker.Concrete.Subtypes
public import Veil.Util.ListSplit

public section

namespace Veil.ModelChecker.Concrete
open Veil

attribute [local grind =] ShardedMapUSize.contains_iff_mem ShardedHashMapUSize.contains_iff_mem
attribute [local simp] ShardedMapUSize.contains_iff_mem ShardedHashMapUSize.contains_iff_mem
  ShardedHashMapUSize.not_mem_emptyUSize

variable {ρ σ κ σₕ asm : Type} [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm]
  {Shard : Type} [Membership σₕ Shard] [MapShard σₕ (LogEntry σₕ κ) Shard]

@[inline]
def MapReduceSearchContextLocal.hasFinished (lctx : MapReduceSearchContextLocal σ κ σₕ asm) : Bool :=
  lctx.base.hasFinished

section

variable (globalSeen : MapReduceGlobalSeen σₕ κ Shard)

-- FIXME: The logic of `tryExploreNeighbor`, `processSuccessors`, and `processState`
-- seems very similar to the sequential processing logic. We should try to unify them

/-- Process a single neighbor in the local context: the `idx`-th success of the state with
fingerprint `fpSt`. `globalSeen` is the main context's seen set, used to check if a state is
already globally seen. The new item carries its log entry, so that the merge of the round keeps
the entry together with the state. -/
@[inline]
def MapReduceSearchContextLocal.tryExploreNeighbor
  (fpSt : σₕ) (idx : Nat)
  (lctx : MapReduceSearchContextLocal σ κ σₕ asm)
  (label : κ) (succ : σ) : MapReduceSearchContextLocal σ κ σₕ asm :=
  let ⟨ctx, seen, q⟩ := lctx
  let fingerprint := fp.view succ
  if globalSeen.contains fingerprint || seen.contains fingerprint then
    ⟨{ ctx with actionStatsMap := ActionStatUpdate.increment label false ctx.actionStatsMap }, seen, q⟩
  else
    ⟨{ ctx with actionStatsMap := ActionStatUpdate.increment label true ctx.actionStatsMap },
      seen.insert fingerprint, ⟨fingerprint, succ, .step fpSt label idx⟩ :: q⟩

/-- Process all successors of a state in the local context, recording their indices from `start`. -/
@[inline]
def MapReduceSearchContextLocal.processSuccessors
  (fpSt : σₕ)
  (start : Nat)
  (successors : List (κ × σ))
  (lctx : MapReduceSearchContextLocal σ κ σₕ asm) : MapReduceSearchContextLocal σ κ σₕ asm :=
  successors.foldlIdx (start := start) (init := lctx) fun i current_lctx (label, postState) =>
    MapReduceSearchContextLocal.tryExploreNeighbor globalSeen fpSt i current_lctx label postState

/-- Process a single state: check violations via BaseSearchContext.processState,
    then process successors if no early termination. -/
def MapReduceSearchContextLocal.processState
  (params : SearchParameters ρ σ) (th : ρ)
  (fpSt : σₕ) (curr : σ)
  (trs : Transitions κ Int σ)
  (lctx : MapReduceSearchContextLocal σ κ σₕ asm) : MapReduceSearchContextLocal σ κ σₕ asm :=
  let ⟨ctx, seen, q⟩ := lctx
  let (ctx', outcomesOpt) := ctx.processState params th fpSt curr trs
  match outcomesOpt with
  | none => ⟨ctx', seen, q⟩
  | some successfulTransitions =>
    -- CHECK Is it useful/possible to remove the call to `successfulTransitions.length`?
    let ctx'' := { ctx' with statesFound := ctx'.statesFound + successfulTransitions.length }
    MapReduceSearchContextLocal.processSuccessors globalSeen fpSt 0 successfulTransitions ⟨ctx'', seen, q⟩

end

section

-- FIXME: The proofs are also very similar to the sequential one

variable {params : SearchParameters ρ σ} {th : ρ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}
  {lctx : MapReduceSearchContextLocal σ κ σₕ asm}
  {globalSeen : MapReduceGlobalSeen σₕ κ Shard}

theorem MapReduceSearchContextLocalInvariants.processSuccessors_preserves_invs
  {p : MapReduceQueueItem σₕ σ κ → Prop}
  {fpSt} (start : Nat) (curr : σ) {succs}
  (h_not_finished : lctx.base.finished = .none)
  (h_reachable : sys.reachable curr)
  (h_succs : ∀ (label : κ) (st : σ),
    (label, st) ∈ succs ↔ (label, ExecutionOutcome.success st) ∈ sys.tr th curr)
  (lctx_invs : MapReduceSearchContextLocalInvariants sys params globalSeen p lctx) :
  MapReduceSearchContextLocalInvariants sys params globalSeen p
    (lctx.processSuccessors globalSeen fpSt start succs) := by
  unfold MapReduceSearchContextLocal.processSuccessors ; dsimp
  -- need to attach some proofs
  have htmp := List.unattach_attachWith (p := fun a => (a.1, ExecutionOutcome.success a.2) ∈ sys.tr th curr)
    (l := succs) (H := by simp [← h_succs])
  generalize succs.attachWith _ _ = succs' at htmp
  rw [← htmp] ; clear htmp h_succs
  induction succs' generalizing lctx start with
  | nil => simp ; assumption
  | cons x succs ih =>
    rcases x with ⟨⟨label, postState⟩, h⟩ ; dsimp [List.foldlIdx] ; apply ih
    · fun_cases MapReduceSearchContextLocal.tryExploreNeighbor <;> dsimp at h_not_finished <;> simp [h_not_finished]
    · clear ih
      fun_cases MapReduceSearchContextLocal.tryExploreNeighbor
      on_goal 1=> cases lctx_invs ; constructor <;> assumption
      -- enqueue case
      rename_i ctx seen sq fingerprint h_not_seen ; subst fingerprint
      simp at h_not_seen h_not_finished
      rcases lctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_not_explored_all, h_dj, h_same_dom, h_succ_coll⟩ ; dsimp only at *
      simp at h_q_sound
      constructor ; on_goal 1=> constructor
      all_goals dsimp only at * ; simp ; grind

omit params th sys in
theorem MapReduceSearchContextLocalInvariants.processSuccessors_successors_collected
  {fpSt start succs} :
  letI res := lctx.processSuccessors globalSeen fpSt start succs
  ∀ l v, (l, v) ∈ succs ∨ fp.view v ∈ globalSeen ∨ fp.view v ∈ lctx.seen →
    fp.view v ∈ globalSeen ∨ fp.view v ∈ res.seen := by
  unfold MapReduceSearchContextLocal.processSuccessors ; dsimp
  induction succs generalizing lctx start with
  | nil => simp
  | cons x succs ih =>
    rcases x with ⟨label, postState⟩ ; dsimp [List.foldlIdx]
    intro l v hv
    apply ih l v
    fun_cases MapReduceSearchContextLocal.tryExploreNeighbor <;> dsimp only at * <;> grind

theorem MapReduceSearchContextLocalInvariants.processState_progress
  {p : MapReduceQueueItem σₕ σ κ → Prop}
  (fpSt : σₕ) (curr : σ) (entry : LogEntry σₕ κ)
  (h_reachable : sys.reachable curr)
  (h_not_finished : lctx.base.finished = .none)
  (lctx_invs : MapReduceSearchContextLocalInvariants sys params globalSeen p lctx) :
  MapReduceSearchContextLocalInvariants sys params globalSeen (fun x => p x ∨ x = ⟨fpSt, curr, entry⟩)
    (MapReduceSearchContextLocal.processState globalSeen params th fpSt curr (sys.tr th curr) lctx) := by
  rcases lctx with ⟨ctx, seen, q⟩ ; rcases lctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_not_explored_all, h_dj, h_succ_coll⟩ ; dsimp only at *

  dsimp [MapReduceSearchContextLocal.processState]
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
        all_goals dsimp only at * ; try solve | assumption | grind)
  subst ctx' ctx'' ; dsimp ; rw [h_not_finished]
  -- normal case
  apply MapReduceSearchContextLocalInvariants.progress_by_one_state (p := p) (curr := curr) (fpSt := fpSt) (e := entry)
  · apply MapReduceSearchContextLocalInvariants.processSuccessors_preserves_invs
    · rfl
    · exact h_reachable
    · introv ; exact Transitions.mem_success_iff.symm
    · constructor ; on_goal 1=> constructor
      all_goals dsimp only at * ; try solve | assumption | grind
  · introv ; intro h1
    exact MapReduceSearchContextLocalInvariants.processSuccessors_successors_collected l v (.inl (Transitions.mem_success_iff.mp h1))
  · simp

/-! ### What a worker's results say -/

theorem MapReduceSearchContextLocal.processSuccessors_log_sound {rep : σₕ → Option σ}
  (hls : lctx.LogSound sys params rep) {fpSt : σₕ} {curr : σ} (hrep : rep fpSt = some curr) :
  (lctx.processSuccessors globalSeen fpSt 0 (sys.tr th curr).successes).LogSound sys params rep := by
  unfold MapReduceSearchContextLocal.processSuccessors
  rw [List.foldlIdx_eq_foldl_zipIdx, ← List.foldl_attach]
  generalize (sys.tr th curr).successes.zipIdx.attach = succs
  induction succs generalizing lctx with
  | nil => exact hls
  | cons x succs ih =>
    rcases x with ⟨⟨⟨label, succ⟩, idx⟩, hmem⟩
    dsimp [List.foldl] ; apply ih
    fun_cases MapReduceSearchContextLocal.tryExploreNeighbor
    · rcases hls with ⟨⟨hv, hf⟩, hent⟩ ; exact ⟨⟨hv, hf⟩, hent⟩    -- `hls` is not affected by the changed fields
    · rename_i ctx seen q fingerprint _ ; subst fingerprint
      rcases hls with ⟨⟨hv, hf⟩, hent⟩
      refine ⟨⟨hv, hf⟩, ?_⟩
      intro item hi ; rcases List.mem_cons.mp hi with rfl | hi
      · exact ⟨fpSt, label, idx, curr, rfl, hrep, by grind [List.mem_zipIdx_iff_getElem?]⟩
      · exact hent item hi

theorem MapReduceSearchContextLocal.processState_log_sound {rep : σₕ → Option σ}
  (hls : lctx.LogSound sys params rep) {fpSt : σₕ} {curr : σ} (hrep : rep fpSt = some curr) :
  (lctx.processState globalSeen params th fpSt curr (sys.tr th curr)).LogSound sys params rep := by
  rcases lctx with ⟨ctx, seen, q⟩
  rcases hls with ⟨⟨hv, hf⟩, hent⟩ ; dsimp only at *
  have hsound := BaseSearchContext.processState_sound sys params (fpSt := fpSt) (curr := curr) ctx hrep hv hf
  have hsnd := BaseSearchContext.processState_snd params th fpSt curr (sys.tr th curr) ctx
  unfold MapReduceSearchContextLocal.processState ; dsimp only
  generalize ctx.processState params th fpSt curr (sys.tr th curr) = pr at hsound hsnd ⊢
  rcases pr with ⟨ctx', outcomesOpt⟩
  dsimp only at *
  obtain ⟨hv', hf'⟩ := hsound
  rcases outcomesOpt with _ | succs
  · exact ⟨⟨hv', hf'⟩, hent⟩
  · obtain rfl := hsnd _ rfl
    exact processSuccessors_log_sound ⟨⟨hv', hf'⟩, hent⟩ hrep

end

namespace LawfulMapReduceSearchContextLocal

-- CHECK For now, separate proofs out to reduce the risk of having weird performance
private theorem processWorkQueue.subproof1 {α : Type u}
  -- (p : α → Prop) : p = (fun x => p x ∨ x ∈ ([] : List α)) := by simp
  {p q : α → Prop} (h : ∀ x, q x ↔ p x ∨ x ∈ ([] : List α)) : p = q := by simp at h ; grind

private theorem processWorkQueue.subproof2 {α : Type u}
  {p q : α → Prop} {a : α} {l : List α}
  (h : ∀ x, q x ↔ p x ∨ x ∈ a :: l) : ∀ x, q x ↔ (p x ∨ x = a) ∨ x ∈ l := by grind

private theorem processWorkQueue.subproof3
  {α : Type u}
  {a : Option α} : (¬ a.isSome = true) → a = none := by simp

private theorem processWorkQueue.subproof4 {α : Type u}
  {p : α → Prop} {a : α} {l : List α}
  (h : ∀ x ∈ a :: l, p x) : ∀ x ∈ l, p x := by grind

private theorem processWorkQueue.subproof5 {α : Type u}
  {p : α → Prop} {a : α} {l : List α}
  (h : ∀ x ∈ a :: l, p x) : p a := by grind

private theorem processWorkQueue.subproof6 {α : Type u} {l : List α} :
  ∀ x, x ∈ l ↔ False ∨ x ∈ l := by grind

-- NOTE: A different way to reason about this is to use a subtype like
-- `{ a // a = f b }`, where `f` is like "applying `processState` for multiple iterations".
-- Then the proof about the invariant can be extrinsic.

def processWorkQueue
  {params : SearchParameters ρ σ} {th : ρ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}
  {globalSeen : MapReduceGlobalSeen σₕ κ Shard}
  (queue : List (MapReduceQueueItem σₕ σ κ))
  {p q : MapReduceQueueItem σₕ σ κ → Prop} (h : ∀ x, q x ↔ p x ∨ x ∈ queue)
  (h_inqueue_reachable : ∀ item ∈ queue, sys.reachable item.state)
  (lctx : LawfulMapReduceSearchContextLocal (κ := κ) sys params globalSeen p) :
    LawfulMapReduceSearchContextLocal (κ := κ) sys params globalSeen q :=
  let ⟨v, hl⟩ := lctx
  match queue with
  | [] => ⟨v, by simpa [← processWorkQueue.subproof1 h] using hl⟩
  | item :: rest =>
    if h_finished : v.hasFinished
    then ⟨v, hl.1.finished_change_visited_pred_in_invs h_finished,
      fun rep hrep => hl.2 rep fun c hc => hrep c ((h c).mpr (.inl hc))⟩
    else
      let ⟨fpSt, curr, entry⟩ := item
      let v' := v.processState globalSeen params th fpSt curr (sys.tr th curr)
      -- CHECK Is this proper tail-recursive?
      processWorkQueue rest
        (by exact processWorkQueue.subproof2 h)
        (by exact processWorkQueue.subproof4 h_inqueue_reachable)
        <| Subtype.mk v' ⟨hl.1.processState_progress fpSt curr entry
          (by exact processWorkQueue.subproof5 (α := MapReduceQueueItem σₕ σ κ) h_inqueue_reachable)
          (by exact processWorkQueue.subproof3 h_finished),
          fun rep hrep => MapReduceSearchContextLocal.processState_log_sound
            (hl.2 rep fun c hc => hrep c (.inl hc)) (hrep ⟨fpSt, curr, entry⟩ (.inr rfl))⟩

/-- Main worker entry point. Creates a neutral context and processes the work queue.
    This function is called by each parallel task. -/
def bfsBigStep
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  (params : SearchParameters ρ σ) {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (globalSeen : MapReduceGlobalSeen σₕ κ Shard)
  (completedDepth : Nat)
  (queue : List (MapReduceQueueItem σₕ σ κ))
  (h_inqueue_reachable : ∀ item ∈ queue, sys.reachable item.state) :
  m (LawfulMapReduceSearchContextLocal (κ := κ) sys params globalSeen (· ∈ queue)) :=
  let lctx : LawfulMapReduceSearchContextLocal sys params globalSeen (fun _ => False) :=
    ⟨MapReduceSearchContextLocal.initial completedDepth,
      MapReduceSearchContextLocalInvariants.initial sys params globalSeen completedDepth,
      fun rep _ => MapReduceSearchContextLocal.LogSound.initial sys params completedDepth rep⟩
  let res := lctx.processWorkQueue queue (by exact processWorkQueue.subproof6) h_inqueue_reachable
  pure res

end LawfulMapReduceSearchContextLocal

/-- The accumulator of a layer's merge: the frontier kept so far, and the log entries of its items
by fingerprint. -/
structure MergeAcc (σ κ σₕ : Type) [fp : StateFingerprint σ σₕ] (numShards : USize) where
  tovisit : List (MapReduceQueueItem σₕ σ κ)
  seen : ShardedHashMapUSize σₕ (LogEntry σₕ κ) numShards

@[inline]
def MergeAcc.innerMerge {numShards : USize}
  (acc : MergeAcc σ κ σₕ numShards) (item : MapReduceQueueItem σₕ σ κ) : MergeAcc σ κ σₕ numShards :=
  if !acc.seen.contains item.fingerprint then
    ⟨item :: acc.tovisit, acc.seen.insert item.fingerprint item.entry⟩
  else
    acc

def MergeAcc.innerMergeDescription {numShards : USize}
  (acc res : MergeAcc σ κ σₕ numShards) (inQ : MapReduceQueueItem σₕ σ κ → Prop) : Prop :=
  ∃ pfx, res.tovisit = pfx ++ acc.tovisit ∧
    (pfx.map MapReduceQueueItem.fingerprint).Nodup ∧
    (∀ fp, (∃ item, inQ item ∧ item.fingerprint = fp) → fp ∉ acc.seen →
      fp ∈ (pfx.map MapReduceQueueItem.fingerprint)) ∧
    (∀ item ∈ pfx, inQ item ∧ item.fingerprint ∉ acc.seen) ∧
    (∀ fp, fp ∈ res.seen ↔ fp ∈ acc.seen ∨ fp ∈ (pfx.map MapReduceQueueItem.fingerprint))

theorem MergeAcc.innerMergeDescription.concat
  {numShards : USize} {p q : MapReduceQueueItem σₕ σ κ → Prop}
  {a1 a2 a3 : MergeAcc σ κ σₕ numShards}
  (h1 : MergeAcc.innerMergeDescription a1 a2 p) (h2 : MergeAcc.innerMergeDescription a2 a3 q) :
  MergeAcc.innerMergeDescription a1 a3 fun x => p x ∨ q x := by
  rcases h1 with ⟨pfx1, h_pfx1, h_nodup1, h_inQ1, h_fps1, h_mem_iff1⟩
  rcases h2 with ⟨pfx2, h_pfx2, h_nodup2, h_inQ2, h_fps2, h_mem_iff2⟩
  exists (pfx2 ++ pfx1) ; simp only [List.map_append, List.append_assoc] ; grind

theorem MergeAcc.innerMerge_foldl_descriptive {numShards : USize}
  (acc : MergeAcc σ κ σₕ numShards) (lq : List (MapReduceQueueItem σₕ σ κ)) :
  let res := lq.foldl (init := acc) MergeAcc.innerMerge
  MergeAcc.innerMergeDescription acc res (· ∈ lq) := by
  dsimp only [MergeAcc.innerMergeDescription]
  induction lq generalizing acc with
  | nil => exists [] ; simp [List.foldl]
  | cons item lq' ih =>
    dsimp [List.foldl]
    specialize ih (MergeAcc.innerMerge acc item)
    revert ih ; fun_cases MergeAcc.innerMerge acc item
    · intro ih ; rcases ih with ⟨pfx, h_pfx, h_nodup, h_subseq, h_fps, h_mem_iff⟩
      rename_i hh ; simp at *
      exists (pfx ++ [item]) ; simp ; split_ands <;> try grind
    · intro ih ; rcases ih with ⟨pfx, h_pfx, h_nodup, h_subseq, h_fps, h_mem_iff⟩
      exists pfx ; split_ands <;> grind

/-- Merging the items of several lists, one list after the other. -/
theorem MergeAcc.innerMerge_foldl_foldl_descriptive {numShards : USize}
  (acc : MergeAcc σ κ σₕ numShards) (lists : List (List (MapReduceQueueItem σₕ σ κ))) :
  let res := lists.foldl (init := acc) fun acc lq => lq.foldl MergeAcc.innerMerge acc
  MergeAcc.innerMergeDescription acc res (fun item => ∃ lq ∈ lists, item ∈ lq) := by
  dsimp only
  induction lists generalizing acc with
  | nil => exists [] ; simp
  | cons lq lists ih =>
    rw [List.foldl_cons]
    have := (MergeAcc.innerMerge_foldl_descriptive acc lq).concat (ih (lq.foldl MergeAcc.innerMerge acc))
    simp only [List.mem_cons, exists_eq_or_imp] ; exact this

theorem BaseSearchContext.mergeWithoutDepthChange_foldl_description
  (acc : BaseSearchContext σ κ σₕ asm) (ctxs : List (BaseSearchContext σ κ σₕ asm)) :
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

/-- Deduplicate the items of `lists`, keeping the first of each fingerprint, and add the kept
ones to the frontier, and their fingerprints with their log entries to the seen set: the merge of a
BFS layer (`mergeWithLocalOnes`) and of the initial states (`MapReduceSearchContextMain.initial`). -/
def MapReduceSearchContextMain.mergeLayer (mctx : MapReduceSearchContextMain σ κ σₕ asm Shard)
    (lists : List (List (MapReduceQueueItem σₕ σ κ))) : MapReduceSearchContextMain σ κ σₕ asm Shard :=
  let ⟨ctx, len, q, globalSeen⟩ := mctx
  let ⟨mq, st⟩ := lists.foldl
    (init := (⟨q, ShardedHashMapUSize.emptyUSize globalSeen.numShards globalSeen.h_numShards_pos⟩ :
      MergeAcc σ κ σₕ globalSeen.numShards))
    fun acc lq => lq.foldl MergeAcc.innerMerge acc
  ⟨ctx, len + st.size, mq, globalSeen.insertManySHM st⟩

-- FIXME: This is very long. How can we shorten it?
/-- What `mergeLayer` does: it keeps one item per fingerprint of `lists`, puts them in front of the
frontier, and adds their fingerprints to the seen set. -/
theorem MapReduceSearchContextMain.mergeLayer_description
    (mctx : MapReduceSearchContextMain σ κ σₕ asm Shard) (lists : List (List (MapReduceQueueItem σₕ σ κ))) :
    let res := mctx.mergeLayer lists
    res.base = mctx.base ∧
    ∃ pfx, res.tovisit = pfx ++ mctx.tovisit ∧
      (pfx.map MapReduceQueueItem.fingerprint).Nodup ∧
      (∀ fp, (∃ item, (∃ lq ∈ lists, item ∈ lq) ∧ item.fingerprint = fp) →
        fp ∈ pfx.map MapReduceQueueItem.fingerprint) ∧
      (∀ item ∈ pfx, ∃ lq ∈ lists, item ∈ lq) ∧
      (∀ fp, fp ∈ res.globalSeen ↔ fp ∈ mctx.globalSeen ∨ fp ∈ pfx.map MapReduceQueueItem.fingerprint) ∧
      res.tovisitLen = mctx.tovisitLen + pfx.length := by
  rcases mctx with ⟨ctx, len, q, gs⟩
  dsimp only [mergeLayer]
  have h := MergeAcc.innerMerge_foldl_foldl_descriptive
    (⟨q, ShardedHashMapUSize.emptyUSize gs.numShards gs.h_numShards_pos⟩ : MergeAcc σ κ σₕ gs.numShards) lists
  generalize lists.foldl _ _ = res at h ⊢
  rcases res with ⟨mq, st⟩
  rcases h with ⟨pfx, h_pfx, h_nodup, h_cov, h_inQ, h_fps⟩
  simp only [ShardedHashMapUSize.not_mem_emptyUSize, not_false_eq_true, and_true, false_or,
    forall_const] at h_cov h_inQ h_fps
  refine ⟨rfl, pfx, h_pfx, h_nodup, h_cov, h_inQ, ?_, ?_⟩
  · intro x ; rw [ShardedMapUSize.mem_insertManySHM, h_fps]
  · dsimp only ; congr 1
    -- the size of the kept fingerprints' map is the number of kept items
    rw [ShardedHashMapUSize.length_toList, ← List.length_map MapReduceQueueItem.fingerprint]
    apply List.Perm.length_eq ; rw [List.perm_ext_iff_of_nodup]
    · simp only [ShardedHashMapUSize.toList, ShardedHashMapUSize.mem_iff_exists_shard] at h_fps ⊢
      simp only [List.mem_flatMap, Std.HashMap.mem_keys] at h_fps ⊢
      exact h_fps
    · apply ShardedHashMapUSize.nodup_elements
    · exact h_nodup

/-- Merge a worker's statistics into the main context's. -/
@[inline]
def BaseSearchContext.mergeWorker (acc : BaseSearchContext σ κ σₕ asm) (lctx : MapReduceSearchContextLocal σ κ σₕ asm) :
    BaseSearchContext σ κ σₕ asm :=
  acc.mergeWithoutDepthChange lctx.base

/-- Merge the workers' results into the main context: their statistics into the base context,
and their new states into the frontier, the seen set and the log (`mergeLayer`). -/
def MapReduceSearchContextMain.mergeWithLocalOnes
  {params : SearchParameters ρ σ} {th : ρ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}
  (mctx : MapReduceSearchContextMain σ κ σₕ asm Shard)
  {preds : List (MapReduceQueueItem σₕ σ κ → Prop)}
  {globalSeen : MapReduceGlobalSeen σₕ κ Shard}
  (lctxs : IteratedProd (preds.map fun P => LawfulMapReduceSearchContextLocal (κ := κ) sys params globalSeen P)) :
  MapReduceSearchContextMain σ κ σₕ asm Shard :=
  let workers := IteratedProd.subtypesToList lctxs
  -- CHECK Will unzipping `workers` first be better?
  let mbase := workers.foldl (init := mctx.base) BaseSearchContext.mergeWorker
  MapReduceSearchContextMain.mergeLayer { mctx with base := mbase } (workers.map (·.queue))

/-- The items of the initial states, each with its fingerprint and its `init` entry, the position
of the state in `initStates`. -/
@[expose] def initialMapReduceQueueItems (initStates : List σ) : List (MapReduceQueueItem σₕ σ κ) :=
  -- CHECK Maybe parallelize this `map`?
  initStates.mapIdx fun i s => ⟨fp.view s, s, .init i⟩

/-- The main context before any state is processed: the initial states merged as round 0, into an
empty seen set, so that each kept item and the seen set share its entry. -/
@[expose] def MapReduceSearchContextMain.initial (initStates : List σ) (numShards : Nat)
    (h_pos : 0 < USize.ofNat numShards := by native_decide) : MapReduceSearchContextMain σ κ σₕ asm Shard :=
  -- CHECK There might be some very bad performance regression here, if `initStates` are many
  MapReduceSearchContextMain.mergeLayer
    ⟨BaseSearchContext.initial initStates.length, 0, [], ShardedMapUSize.empty (USize.ofNat numShards) h_pos⟩
    [initialMapReduceQueueItems initStates]

/-- Merging the initial items into a context that has seen nothing yet establishes the invariants. -/
theorem MapReduceSearchContextMainInvariants.of_mergeLayer_initialMapReduceQueueItems
    {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}
    {params : SearchParameters ρ σ} (m0 : MapReduceSearchContextMain σ κ σₕ asm Shard)
    (h_tv : m0.tovisit = []) (h_len : m0.tovisitLen = 0) (h_gs : ∀ x, x ∉ m0.globalSeen)
    (h_fin : m0.base.finished = none) :
    MapReduceSearchContextMainInvariants sys params (m0.mergeLayer [initialMapReduceQueueItems sys.initStates]) := by
  have h := m0.mergeLayer_description [initialMapReduceQueueItems sys.initStates]
  generalize m0.mergeLayer [initialMapReduceQueueItems sys.initStates] = res at h ⊢
  rcases res with ⟨base', len', tv', gs'⟩
  rcases h with ⟨h_base, pfx, h_pfx, h_nodup, h_cov, h_inQ, h_fps, h_len'⟩
  dsimp only at h_base h_pfx h_len' h_fps
  rw [h_tv, List.append_nil] at h_pfx ; subst h_pfx
  simp only [List.mem_singleton, exists_eq_left, initialMapReduceQueueItems, List.mem_mapIdx] at h_cov h_inQ
  simp only [h_gs, false_or, List.mem_map] at h_fps
  constructor ; on_goal 1=> constructor
  all_goals (try simp at *) ; try grind
  · simp [h_fps]
    intro s hs
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
    grind

theorem MapReduceSearchContextMainInvariants.initial
    (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
    (params : SearchParameters ρ σ) (numShards : Nat) {h_pos} :
    MapReduceSearchContextMainInvariants sys params
      (MapReduceSearchContextMain.initial (fp := fp) (Shard := Shard) (asm := asm) sys.initStates numShards h_pos) := by
  unfold MapReduceSearchContextMain.initial
  apply MapReduceSearchContextMainInvariants.of_mergeLayer_initialMapReduceQueueItems <;> try rfl
  intro x ; exact ShardedMapUSize.not_mem_empty

private theorem List.zip_mem {α : Type u} {β : Type v} {l1 : List α} {l2 : List β}
  (hl : l1.length ≤ l2.length) (h : i < l1.length) :
  (l1[i], l2[i]) ∈ l1.zip l2 := by
  induction l1 generalizing i l2 with
  | nil => simp at h
  | cons a l1 ih =>
    cases l2 with
    | nil => simp at hl
    | cons b l2 =>
      cases i with
      | zero => exact .head _
      | succ i =>
        simp only [List.length_cons] at hl h
        exact .tail _ (ih (by omega) (by omega))

-- FIXME: Later make this update of `depth` a reusable definition

theorem MapReduceSearchContextMain.mergeWithLocalOnes_preserves_invs
  {params : SearchParameters ρ σ} {th : ρ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}
  {mctx : MapReduceSearchContextMain σ κ σₕ asm Shard}
  (h_not_finished : mctx.base.hasFinished = false)
  (h_mctx : MapReduceSearchContextMainInvariants sys params mctx)
  {numSplits chunkSize numLarge : Nat}
  (lctxs :
    let preds := (ListSplit.splitList numSplits chunkSize numLarge mctx.tovisit).map fun a item => item ∈ a
    IteratedProd (preds.map fun P => LawfulMapReduceSearchContextLocal (κ := κ) sys params mctx.globalSeen P)) :
  let mctx' := MapReduceSearchContextMain.mergeWithLocalOnes
    ⟨{ mctx.base with currentFrontierDepth := mctx.base.currentFrontierDepth + 1 }, 0, [], mctx.globalSeen⟩ lctxs
  MapReduceSearchContextMainInvariants sys params mctx' := by
  rcases mctx with ⟨ctx, mlen_orig, tovisit, gs⟩
  let ctx' : BaseSearchContext σ κ σₕ asm :=
    { ctx with currentFrontierDepth := ctx.currentFrontierDepth + 1 }
  dsimp ; unfold mergeWithLocalOnes ; dsimp only
  have h_local_invs := IteratedProd.externalize_proofs lctxs ; dsimp at h_local_invs
  rcases h_local_invs with ⟨h_length_eq, h_local_invs⟩
  replace h_local_invs := fun x b h => (h_local_invs x b h).1
  generalize IteratedProd.subtypesToList lctxs = lctxs' at *
  -- the merge of the bases
  have h_base_desc := BaseSearchContext.mergeWithoutDepthChange_foldl_description ctx' (lctxs'.map (·.base))
  rw [List.foldl_map] at h_base_desc
  change (lctxs'.foldl BaseSearchContext.mergeWorker ctx').finished = _ at h_base_desc
  simp [BaseSearchContext.hasFinished] at h_not_finished
  try dsimp at h_base_desc
  rw [h_not_finished] at h_base_desc ; try dsimp at h_base_desc
  generalize lctxs'.foldl BaseSearchContext.mergeWorker ctx' = mbase at *
  -- the merge of the layer
  have h_layer := mergeLayer_description ⟨mbase, 0, [], gs⟩ (lctxs'.map (·.queue))
  generalize mergeLayer ⟨mbase, 0, [], gs⟩ (lctxs'.map (·.queue)) = res at h_layer ⊢
  rcases res with ⟨mbase', mlen, mq, gs'⟩
  rcases h_layer with ⟨h_base_eq, pfx, h_pfx, h_nodup, h_in_pfx, h_inQ, h_fps, h_len⟩
  dsimp only at h_base_eq h_pfx h_len ; subst mbase'
  rw [List.append_nil] at h_pfx ; subst mq
  simp at h_inQ h_fps h_in_pfx

  rcases h_mctx with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed, h_orig_len⟩
  whnf at h_closed ; dsimp only at *
  clear h_q_emp

  -- prove a theorem first, since it will be used in both `terminate_empty_queue` and `stable_closed`
  have h_not_explored_all : mbase.finished ≠ Option.some (TerminationReason.exploredAllReachableStates) := by
    intro h ; rw [h_base_desc, Option.bind_eq_some_iff] at h
    rcases h with ⟨lbctx, h_find, h_finished⟩
    rw [List.find?_map, Option.map_eq_some_iff] at h_find
    rcases h_find with ⟨lctx, h_find, rfl⟩
    -- deriving false here
    rw [List.find?_eq_some_iff_getElem] at h_find
    rcases h_find with ⟨_, i, h_i, h_getElem, _⟩
    -- NOTE: This is repeating
    have h_in_zip := List.zip_mem (by apply Nat.le_of_eq ; symm ; apply h_length_eq) (by rw [← h_length_eq] ; apply h_i)
    rw [h_getElem] at h_in_zip
    specialize h_local_invs _ _ h_in_zip
    have := h_local_invs.not_explored_all ; grind

  constructor ; on_goal 1=> constructor
  · simp [h_fps]
    intro fpSt curr e hh
    specialize h_inQ _ hh
    rcases h_inQ with ⟨_, ⟨lctx, h_in_lctxs', rfl⟩, h_in_q⟩
    -- This is annoying ...
    rw [List.mem_iff_getElem] at h_in_lctxs'
    rcases h_in_lctxs' with ⟨i, h_i, h_getElem⟩
    have h_in_zip := List.zip_mem (by apply Nat.le_of_eq ; symm ; apply h_length_eq) (by rw [← h_length_eq] ; apply h_i)
    rw [h_getElem] at h_in_zip
    specialize h_local_invs _ _ h_in_zip
    rcases h_local_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_not_explored_all, h_dj, h_same_dom, h_succ_coll⟩
    have := h_q_sound fpSt curr ⟨e, h_in_q⟩
    grind
  · simp [h_fps]
    intro x hh ; rcases hh with hh | hh
    · grind
    · rcases hh with ⟨⟨fpSt, curr, e⟩, hh, heq⟩ ; dsimp at heq ; subst fpSt
      -- NOTE: This is repeating
      specialize h_inQ _ hh
      rcases h_inQ with ⟨_, ⟨lctx, h_in_lctxs', rfl⟩, h_in_q⟩
      rw [List.mem_iff_getElem] at h_in_lctxs'
      rcases h_in_lctxs' with ⟨i, h_i, h_getElem⟩
      have h_in_zip := List.zip_mem (by apply Nat.le_of_eq ; symm ; apply h_length_eq) (by rw [← h_length_eq] ; apply h_i)
      rw [h_getElem] at h_in_zip
      specialize h_local_invs _ _ h_in_zip
      rcases h_local_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_not_explored_all, h_dj, h_same_dom, h_succ_coll⟩
      exact h_vis_sound x ⟨curr, e, h_in_q⟩
  · simp [h_fps] ; grind
  · simp ; grind
  · whnf ; simp [h_fps]
    intro hinj hor u h_reachable hh h_not_in_pfx
    rcases hor with _ | h_not_finished_mbase
    on_goal 1=> grind
    rcases hh with hh | hh
    · by_cases h_in_tovisit? : (∀ item ∈ tovisit, item.fingerprint ≠ StateView.view u)
      · grind  -- easy case
      · clear h_closed
        simp at h_in_tovisit? ; rcases h_in_tovisit? with ⟨⟨fpSt, curr, ent⟩, h_in_tovisit, heq⟩
        dsimp at heq ; subst fpSt
        have := hinj h_reachable (h_q_sound _ _ ⟨ent, h_in_tovisit⟩ |>.left)
          (h_q_sound _ _ ⟨ent, h_in_tovisit⟩ |>.right.right) ; subst curr -- unify `curr` with `u`
        -- here, need the split covering theorem
        obtain ⟨chunk, h_chunk_in, h_in_chunk⟩ := ListSplit.splitList_mem numSplits chunkSize numLarge tovisit ⟨fp.view u, u, ent⟩ h_in_tovisit
        rw [List.mem_iff_getElem] at h_chunk_in
        rcases h_chunk_in with ⟨j, h_j, h_getElem_chunk⟩
        have h_in_zip := List.zip_mem (by apply Nat.le_of_eq ; symm ; apply h_length_eq) (by simpa using h_j)
        simp [h_getElem_chunk] at h_in_zip
        specialize h_local_invs _ _ h_in_zip ; try simp at h_local_invs
        -- show that no `lctx` has finished
        rw [h_base_desc] at h_not_finished_mbase
        revert h_not_finished_mbase ; rcases heq : List.find? _ _ with _ | lctx
        on_goal 2=>
          dsimp ; intro heq' ; rw [List.find?_map, Option.map_eq_some_iff] at heq
          rcases heq with ⟨lctx', heq, rfl⟩
          rw [List.find?_eq_some_iff_getElem] at heq
          try simp only [Function.comp_def, BaseSearchContext.hasFinished] at heq
          grind
        intro _ ; rw [List.find?_map, Option.map_eq_none_iff, List.find?_eq_none] at heq
        -- NOTE: Here Lean has some trouble proving the index validity of `j` from the scratch, so use some trick
        set e := getElem lctxs' j _
        specialize heq e (by exact List.getElem_mem _) ; simp [BaseSearchContext.hasFinished] at heq
        rcases h_local_invs with ⟨_, _, h_dj, h_same_dom, h_succ_coll⟩
        specialize h_succ_coll heq (fp.view u) u ent (h_getElem_chunk ▸ h_in_chunk)
        grind
    · grind
  · simp [h_len]

omit [ActionStatUpdate κ asm] in
private theorem breadthFirstSearchParallel.subproof1 {ρ σₕ σ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}
  {seen : σₕ → Prop}
  {tovisit : List (MapReduceQueueItem σₕ σ κ)}
  (h : ∀ x st, (∃ e, ⟨x, st, e⟩ ∈ tovisit) → sys.reachable st ∧ seen x ∧ x = fp.view st)
  (splitLists : List (List (MapReduceQueueItem σₕ σ κ)))
  (h_mem_inv : ∀ item, (∃ l ∈ splitLists, item ∈ l) → item ∈ tovisit) :
  ∀ sublist ∈ splitLists,
    ∀ item ∈ sublist, sys.reachable item.state := by
  intro sublist h_sublist_in item h_item_in
  exact (h item.fingerprint item.state ⟨item.entry, h_mem_inv _ ⟨sublist, h_sublist_in, h_item_in⟩⟩).1

private theorem not_too_small_not_too_large (n : Nat) :
  let t := max 1 (min n 4294967295)
  0 < USize.ofNat t ∧ t < USize.size := by
  apply (fun (p : _ → _) q => And.intro (p q) q)
  · intro h ; simp [USize.lt_ofNat_iff h]; omega
  · cases USize.size_eq <;> rename_i h <;> rw [h] <;> omega

def breadthFirstSearchParallel {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  (params : SearchParameters ρ σ)
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (parallelCfg : ParallelConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken) :
  m (MapReduceSearchContextMain σ κ σₕ asm Shard) := do
  let numShards := max 1 <| min parallelCfg.numSubTasks 4294967295
  have h_bounds : 0 < USize.ofNat numShards ∧ numShards < USize.size := by
    exact not_too_small_not_too_large parallelCfg.numSubTasks
  have ⟨h_pos, _⟩ := h_bounds
  let mut mctx : LawfulMapReduceSearchContextMain (fp := fp) (Shard := Shard) sys params :=
    Subtype.mk (MapReduceSearchContextMain.initial sys.initStates numShards h_pos)
      (MapReduceSearchContextMainInvariants.initial sys params numShards)
  let mut lastUpdateTime : Nat := 0
  let mut cancelled := false
  while h_not_finished : mctx.val.base.hasFinished = false do
    let mctxVal := mctx.val
    have h_not_finished_val : mctxVal.base.hasFinished = false := h_not_finished
    have h_mctx : MapReduceSearchContextMainInvariants sys params mctxVal := mctx.property
    let base := mctxVal.base
    let tovisitLen := mctxVal.tovisitLen
    let tovisit := mctxVal.tovisit
    let globalSeen := mctxVal.globalSeen
    -- Check if the frontier is empty
    if h_empty : tovisit.isEmpty then
      mctx := Subtype.mk ⟨{ base with finished := some (.exploredAllReachableStates) }, tovisitLen, tovisit, globalSeen⟩
        (h_mctx.setExploredAll_preserves_invs h_not_finished_val h_empty)
      break
    else
      -- FIXME: Need to add a proper sequential fallback if the frontier is too small
      -- Split the queue into sub-lists; fall back to 1 split (sequential) if frontier is too small
      let numSplits := if tovisitLen < parallelCfg.thresholdToParallel then 1
                       else max 1 parallelCfg.numSubTasks
      let chunkSize := tovisitLen / numSplits
      let numLarge := tovisitLen % numSplits
      let splitLists := ListSplit.splitList numSplits chunkSize numLarge tovisit
      let completedDepth := base.completedDepth
      -- Map step: spawn parallel tasks
      -- **CAVEAT**: The call to `IO.asTask` **SHOULD NOT** be put in this procedure,
      -- as that might cause parallelism to vanish!!! Instead, the call should be defined
      -- in some other file.
      let tasks ← IteratedProd.taskSplit splitLists fun subList h_sublist_in =>
        LawfulMapReduceSearchContextLocal.bfsBigStep params sys globalSeen completedDepth subList
          (by
            exact breadthFirstSearchParallel.subproof1 h_mctx.queue_sound splitLists
              (fun item hm => (ListSplit.splitList_mem_iff numSplits chunkSize numLarge tovisit item).mp hm) _ h_sublist_in)
      -- Functions on an `IteratedProd` walk its index list at run time, passing each element to
      -- their callback. Indexed by `splitLists`, the tasks would make the main thread keep the
      -- whole frontier alive until the merge below, and free it there. Index them by the
      -- predicates `(· ∈ chunk)` instead, which are erased: then each task holds the last
      -- reference to its chunk and frees it. The cast does nothing at run time.
      let preds := splitLists.map fun a item => item ∈ a
      let tasks : IteratedProd (preds.map fun P =>
          Task (Except IO.Error (LawfulMapReduceSearchContextLocal sys params globalSeen P))) := by
        simp only [preds, List.map_map] ; exact tasks
      let results ← IteratedProd.mapM (as := preds)
        (T₂ := (fun P => LawfulMapReduceSearchContextLocal sys params globalSeen P))
        (fun task => IO.ofExcept task.get) tasks
      -- CHECK Ideally, `tovisit` should not be involved in any computational part from this point on
      -- Reduce step
      let mctxValForMerge : MapReduceSearchContextMain σ κ σₕ asm Shard :=
        { base := { base with currentFrontierDepth := base.currentFrontierDepth + 1 } , tovisitLen := 0, tovisit := [], globalSeen := globalSeen }
      let mctxVal' := mctxValForMerge.mergeWithLocalOnes (preds := preds) results
      have h_mctx' : MapReduceSearchContextMainInvariants sys params mctxVal' :=
        MapReduceSearchContextMain.mergeWithLocalOnes_preserves_invs h_not_finished_val h_mctx results
      match heq : mctxVal' with
      | ⟨base', tovisitLen', tovisit', globalSeen'⟩ =>
        trySetViolationFound progressInstanceId base'
        -- Update progress on every diameter change
        updateProgressDuringBFS progressInstanceId base' tovisitLen' globalSeen'.size
        -- Prove invariants are preserved using local invariants from `lawfulResults`
        mctx := Subtype.mk ⟨base', tovisitLen', tovisit', globalSeen'⟩ (heq.symm ▸ h_mctx')
        -- Check for cancellation/handoff at most once per second
        let newtime? ← checkCancellationWithoutPeriodicUpdate progressInstanceId lastUpdateTime 1000 cancelToken
        match newtime? with
        | .updateTime t => lastUpdateTime := t
        | .searchCancelled => cancelled := true ; break
        | .noUpdate => pure ()
  -- Final update to ensure stats reflect finished state, with the depth of the last frontier
  -- explored rather than of the next one. Only the display shows that depth: setting it as the
  -- frontier depth of the context would change its `completedDepth` too.
  let ⟨mctxVal, _⟩ := mctx
  let displayBase : BaseSearchContext σ κ σₕ asm :=
    { mctxVal.base with currentFrontierDepth := mctxVal.base.completedDepth }
  updateProgressDuringBFS progressInstanceId displayBase mctxVal.tovisitLen mctxVal.globalSeen.size
  if cancelled then
    return { mctxVal with base := { mctxVal.base with finished := some (.earlyTermination .cancelled) } }
  else
    return mctxVal

end Veil.ModelChecker.Concrete
