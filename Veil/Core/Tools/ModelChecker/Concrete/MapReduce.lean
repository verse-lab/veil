module

public import Veil.Core.Tools.ModelChecker.Concrete.MapReduceLemmas
public import Veil.Core.Tools.ModelChecker.Concrete.Progress
public import Veil.Core.Tools.ModelChecker.Concrete.Subtypes
public import Veil.Util.ListSplit

public section

namespace Veil.ModelChecker.Concrete
open Veil

attribute [local grind =] ShardedUSize.contains_iff_mem
attribute [local simp] ShardedUSize.contains_iff_mem ShardedUSize.not_mem_empty

-- NOTE: Before the section variables, since `numShards` cannot name a declaration while it names one.
private theorem not_too_small_not_too_large (n : Nat) :
  let t := max 1 (min n 4294967295)
  0 < USize.ofNat t ∧ t < USize.size := by
  apply (fun (p : _ → _) q => And.intro (p q) q)
  · intro h ; simp [USize.lt_ofNat_iff h]; omega
  · cases USize.size_eq <;> rename_i h <;> rw [h] <;> omega

/-- The number of shards of the parallel search's seen set: the number of sub-tasks, between 1 and
`2³² - 1`. -/
def _root_.Veil.ModelChecker.ParallelConfig.numShards (cfg : ParallelConfig) : PosUSize :=
  ⟨USize.ofNat (max 1 (min cfg.numSubTasks 4294967295)), (not_too_small_not_too_large cfg.numSubTasks).1⟩

variable {ρ σ κ σₕ asm : Type} [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm]
  {Shard : Type} [Membership σₕ Shard] [MapShard σₕ (LogEntry σₕ κ) Shard] {numShards : PosUSize}

@[inline]
def MapReduceSearchContextLocal.hasFinished (lctx : MapReduceSearchContextLocal σ κ σₕ asm) : Bool :=
  lctx.base.hasFinished

section

variable (globalSeen : MapReduceGlobalSeen σₕ κ Shard numShards)

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
  {globalSeen : MapReduceGlobalSeen σₕ κ Shard numShards}

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
  {globalSeen : MapReduceGlobalSeen σₕ κ Shard numShards}
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
  (globalSeen : MapReduceGlobalSeen σₕ κ Shard numShards)
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
structure MergeAcc (σ κ σₕ : Type) [fp : StateFingerprint σ σₕ] (numShards : PosUSize) where
  tovisit : List (MapReduceQueueItem σₕ σ κ)
  seen : ShardedHashMapUSize σₕ (LogEntry σₕ κ) numShards

@[inline]
def MergeAcc.innerMerge {numShards : PosUSize}
  (acc : MergeAcc σ κ σₕ numShards) (item : MapReduceQueueItem σₕ σ κ) : MergeAcc σ κ σₕ numShards :=
  if !acc.seen.contains item.fingerprint then
    ⟨item :: acc.tovisit, acc.seen.insert item.fingerprint item.entry⟩
  else
    acc

/-- Specialize the generic deduplicating-fold description to a merge accumulator. -/
abbrev MergeAcc.DescriptionWithAcc {numShards : PosUSize}
    (lq : List (MapReduceQueueItem σₕ σ κ)) (acc res : MergeAcc σ κ σₕ numShards) : Prop :=
  DedupFoldDescriptionWithAcc
    (key := MapReduceQueueItem.fingerprint)
    (val := MapReduceQueueItem.entry)
    (proj := id)
    (lst := MergeAcc.tovisit)
    (look := fun acc x => acc.seen.get? x) lq acc res

-- FIXME: Deduplicate the definition
abbrev MergeAcc.Description {numShards : PosUSize}
    (lq : List (MapReduceQueueItem σₕ σ κ)) (res : MergeAcc σ κ σₕ numShards) : Prop :=
  DedupFoldDescription
    (key := MapReduceQueueItem.fingerprint)
    (val := MapReduceQueueItem.entry)
    (proj := id)
    (lst := MergeAcc.tovisit)
    (look := fun acc x => acc.seen.get? x) lq res

/-- The merge of a round folds `innerMerge` over the items of the workers: a deduplicating fold. -/
theorem MergeAcc.innerMerge_foldl_descriptive {numShards : PosUSize}
  (acc : MergeAcc σ κ σₕ numShards) (lq : List (MapReduceQueueItem σₕ σ κ)) :
  MergeAcc.DescriptionWithAcc lq acc (lq.foldl MergeAcc.innerMerge acc) := by
  apply DedupFoldDescriptionWithAcc.of_foldl <;> intro acc item h <;> simp [MergeAcc.innerMerge]
  · grind [ShardedUSize.contains_iff_mem, ShardedMapUSize.mem_iff_isSome_get?]
  · open Classical in simp only [ShardedUSize.not_contains_iff_not_mem]
    simp only [← ShardedMapUSize.not_mem_iff_get?_none] at h
    simp [h, ShardedMapUSize.get?_insert]

/-- Deduplicate the items of `lists`, keeping the first of each fingerprint, and add the kept
ones to the frontier, and their fingerprints with their log entries to the seen set: the merge of a
BFS layer (`mergeWithLocalOnes`) and of the initial states (`MapReduceSearchContextMain.initial`). -/
def MapReduceSearchContextMain.mergeLayer (mctx : MapReduceSearchContextMain σ κ σₕ asm Shard numShards)
    (lists : List (List (MapReduceQueueItem σₕ σ κ))) : MapReduceSearchContextMain σ κ σₕ asm Shard numShards :=
  let ⟨ctx, len, q, globalSeen⟩ := mctx
  let ⟨mq, st⟩ := lists.foldl
    (init := (⟨q, ShardedUSize.empty⟩ : MergeAcc σ κ σₕ numShards))
    fun acc lq => lq.foldl MergeAcc.innerMerge acc
  ⟨ctx, len + st.size, mq, globalSeen.insertMany st⟩

/-- A layer first deduplicates its items into an empty per-round map, then adds the resulting
frontier and entries to the main context. Existing global entries are overwritten by the round. -/
theorem MapReduceSearchContextMain.mergeLayer_description_with_acc
    (mctx : MapReduceSearchContextMain σ κ σₕ asm Shard numShards) (lists : List (List (MapReduceQueueItem σₕ σ κ))) :
    ∃ merged : MergeAcc σ κ σₕ numShards,
      MergeAcc.DescriptionWithAcc lists.flatten
        ⟨mctx.tovisit, ShardedUSize.empty⟩
        merged ∧
      mctx.mergeLayer lists =
        ⟨mctx.base, mctx.tovisitLen + merged.seen.size, merged.tovisit,
          mctx.globalSeen.insertMany merged.seen⟩ := by
  rcases mctx with ⟨ctx, len, q, gs⟩
  refine ⟨_, MergeAcc.innerMerge_foldl_descriptive _ lists.flatten, ?_⟩
  simp only [mergeLayer, List.foldl_flatten]

-- FIXME: Maybe eventually remove this duplicate?
theorem MapReduceSearchContextMain.mergeLayer_description
    (mctx : MapReduceSearchContextMain σ κ σₕ asm Shard numShards) (lists : List (List (MapReduceQueueItem σₕ σ κ)))
    (h : mctx.tovisit = []) :
    ∃ merged : MergeAcc σ κ σₕ numShards,
      MergeAcc.Description lists.flatten merged ∧
      mctx.mergeLayer lists =
        ⟨mctx.base, mctx.tovisitLen + merged.seen.size, merged.tovisit,
          mctx.globalSeen.insertMany merged.seen⟩ := by
  obtain ⟨merged, hd, h_merge⟩ := mctx.mergeLayer_description_with_acc lists
  refine ⟨merged, ?_, h_merge⟩
  apply DedupFoldDescription.ofDedupFoldDescriptionWithAcc <;> try assumption
  simp [ShardedMapUSize.get?_empty]

/-- Specialize the deduplicating fold's key and length description to the sharded seen map. -/
private theorem MergeAcc.Description.extra {numShards : PosUSize} (acc : MergeAcc σ κ σₕ numShards)
    {lq : List (MapReduceQueueItem σₕ σ κ)} (h : MergeAcc.Description lq acc) :
    (∀ x, x ∈ acc.seen ↔ x ∈ acc.tovisit.map MapReduceQueueItem.fingerprint) ∧
      acc.seen.size = acc.tovisit.length := by
  rcases h with ⟨pfx, h1, h2, h3, h4, h5⟩ ; simp at * ; subst_vars
  constructor
  · intro x ; rw [ShardedMapUSize.mem_iff_isSome_get?, Option.isSome_iff_exists] ; aesop
  · rw [ShardedUSize.length_toList]
    trans (acc.tovisit.map MapReduceQueueItem.fingerprint).length
    on_goal 2=> simp
    apply List.Perm.length_eq ; rw [List.perm_ext_iff_of_nodup] <;> try assumption
    on_goal 2=> apply ShardedUSize.nodup_toList
    simp only [ShardedUSize.toList, List.mem_flatMap, KeyShard.mem_toList,
      ← ShardedUSize.mem_iff_exists_shard, ShardedMapUSize.mem_iff_isSome_get?]
    simp ; intro x ; rw [Option.isSome_iff_exists] ; aesop

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
  (mctx : MapReduceSearchContextMain σ κ σₕ asm Shard numShards)
  {preds : List (MapReduceQueueItem σₕ σ κ → Prop)}
  {globalSeen : MapReduceGlobalSeen σₕ κ Shard numShards}
  (lctxs : IteratedProd (preds.map fun P => LawfulMapReduceSearchContextLocal (κ := κ) sys params globalSeen P)) :
  MapReduceSearchContextMain σ κ σₕ asm Shard numShards :=
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
@[expose] def MapReduceSearchContextMain.initial (initStates : List σ) :
    MapReduceSearchContextMain σ κ σₕ asm Shard numShards :=
  -- CHECK There might be some very bad performance regression here, if `initStates` are many
  MapReduceSearchContextMain.mergeLayer
    ⟨BaseSearchContext.initial initStates.length, 0, [], ShardedUSize.empty⟩
    [initialMapReduceQueueItems initStates]

/-- Merging the initial items into a context that has seen nothing yet establishes the invariants. -/
theorem MapReduceSearchContextMainInvariants.of_mergeLayer_initialMapReduceQueueItems
    {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}
    {params : SearchParameters ρ σ} (m0 : MapReduceSearchContextMain σ κ σₕ asm Shard numShards)
    (h_tv : m0.tovisit = []) (h_len : m0.tovisitLen = 0)
    (h_gs : ∀ x, x ∉ m0.globalSeen) (h_fin : m0.base.finished = none) :
    MapReduceSearchContextMainInvariants sys params (m0.mergeLayer [initialMapReduceQueueItems sys.initStates]) := by
  obtain ⟨⟨tovisit, seen⟩, hd, h_merge⟩ :=
    m0.mergeLayer_description [initialMapReduceQueueItems sys.initStates] h_tv
  rw [h_merge] ; clear h_merge
  obtain ⟨h_seen, h_size⟩ := MergeAcc.Description.extra ⟨tovisit, seen⟩ hd
  obtain ⟨pfx, h_pfx, h_nodup, h_cov, h_inQ, h_content⟩ := hd
  simp [initialMapReduceQueueItems] at *
  subst_vars
  constructor ; on_goal 1=> constructor
  all_goals (try simp [ShardedMapUSize.mem_insertMany] at *) ; try grind
  · simp only [h_seen]
    intro s hs ; obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
    right ; exact h_cov ⟨fp.view sys.initStates[i], sys.initStates[i], .init i⟩ i hi rfl
  · whnf ; simp only [ShardedMapUSize.mem_insertMany, h_gs, false_or, h_seen] ; grind

theorem MapReduceSearchContextMainInvariants.initial
    (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
    (params : SearchParameters ρ σ) :
    MapReduceSearchContextMainInvariants sys params
      (MapReduceSearchContextMain.initial (fp := fp) (Shard := Shard) (asm := asm) (numShards := numShards)
        sys.initStates) := by
  unfold MapReduceSearchContextMain.initial
  apply MapReduceSearchContextMainInvariants.of_mergeLayer_initialMapReduceQueueItems <;> try rfl
  intro x ; exact ShardedUSize.not_mem_empty

/-- Merging the initial items into a context that has seen nothing yet makes its log sound: the
representative of a fingerprint is the initial state that its `init` entry points to. -/
theorem MapReduceSearchContextMain.LogSound.of_mergeLayer_initialMapReduceQueueItems
    {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}
    {params : SearchParameters ρ σ} (m0 : MapReduceSearchContextMain σ κ σₕ asm Shard numShards)
    (h_tv : m0.tovisit = []) (h_gs : ∀ x, x ∉ m0.globalSeen)
    (h_vs : m0.base.violatingStates = []) (h_fin : m0.base.finished = none) :
    ∃ rep dep, (m0.mergeLayer [initialMapReduceQueueItems sys.initStates]).LogSound sys params rep dep := by
  obtain ⟨⟨tovisit, seen⟩, hd, h_merge⟩ :=
    m0.mergeLayer_description [initialMapReduceQueueItems sys.initStates] h_tv
  rw [h_merge] ; clear h_merge
  obtain ⟨pfx, h_pfx, h_nodup, h_cov, h_inQ, h_content⟩ := hd
  have h_gs' : ∀ x, ShardedMapUSize.get? m0.globalSeen x = none :=
    fun x => ShardedMapUSize.not_mem_iff_get?_none.mp (h_gs x)
  simp [initialMapReduceQueueItems] at h_pfx h_inQ h_content
  subst_vars
  let rep (a : σₕ) := (seen.get? a).bind fun
    | .init j => sys.initStates[j]?
    | .step .. => none
  exists rep, fun _ => 0 ; dsimp [rep]
  refine ⟨⟨by simp [h_vs], by simp [h_fin, TerminationSound]⟩, ?_, ?_⟩    -- nothing recorded yet
  on_goal 1=> constructor
  all_goals (try simp [ShardedMapUSize.get?_insertMany, h_gs', Option.bind_eq_some_iff]) ; try grind
  · intro x ; cases ShardedMapUSize.get? seen x <;> simp
  · intro x i hx
    obtain ⟨a, ha, -, he⟩ := (h_content _ _).mp hx ; obtain ⟨j, hj, rfl⟩ := h_inQ a ha
    cases he ; simp [hx, hj]
  · intro item hitem ; obtain ⟨j, hj, rfl⟩ := h_inQ item hitem
    exact ⟨_, (h_content _ _).mpr ⟨_, hitem, rfl, rfl⟩, by simp [hj]⟩

theorem MapReduceSearchContextMain.LogSound.initial
    (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
    (params : SearchParameters ρ σ) :
    ∃ rep dep, (MapReduceSearchContextMain.initial (fp := fp) (Shard := Shard) (asm := asm)
      (numShards := numShards) sys.initStates).LogSound sys params rep dep := by
  unfold MapReduceSearchContextMain.initial
  apply MapReduceSearchContextMain.LogSound.of_mergeLayer_initialMapReduceQueueItems <;> try rfl
  intro x ; exact ShardedUSize.not_mem_empty

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
  {mctx : MapReduceSearchContextMain σ κ σₕ asm Shard numShards}
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
  obtain ⟨merged, hd, h_merge⟩ :=
    mergeLayer_description ⟨mbase, 0, [], gs⟩ (lctxs'.map (·.queue)) rfl
  rw [h_merge]
  obtain ⟨h_seen, h_size⟩ := hd.extra
  obtain ⟨pfx, h_pfx, h_nodup, h_in_pfx, h_inQ, h_content⟩ := hd
  simp only [List.map_id] at h_pfx
  simp only [h_pfx] at h_seen h_size
  have h_fps := fun x => (ShardedMapUSize.mem_insertMany (st := gs) (items := merged.seen) (k := x)).trans
    (or_congr Iff.rfl (h_seen x))
  simp [List.mem_flatten] at h_inQ h_fps h_in_pfx
  simp only [h_pfx, h_size, Nat.zero_add]

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
  · rfl

/-- Merging the workers' results keeps the log sound, for representatives extended with the states
of the new frontier: each new entry is a transition from a state of the old frontier. -/
theorem MapReduceSearchContextMain.mergeWithLocalOnes_log_sound
  {params : SearchParameters ρ σ} {th : ρ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}
  {mctx : MapReduceSearchContextMain σ κ σₕ asm Shard numShards}
  (h_ls : ∃ rep dep, mctx.LogSound sys params rep dep)
  {numSplits chunkSize numLarge : Nat}
  (lctxs :
    let preds := (ListSplit.splitList numSplits chunkSize numLarge mctx.tovisit).map fun a item => item ∈ a
    IteratedProd (preds.map fun P => LawfulMapReduceSearchContextLocal (κ := κ) sys params mctx.globalSeen P)) :
  let mctx' := MapReduceSearchContextMain.mergeWithLocalOnes
    ⟨{ mctx.base with currentFrontierDepth := mctx.base.currentFrontierDepth + 1 }, 0, [], mctx.globalSeen⟩ lctxs
  ∃ rep dep, mctx'.LogSound sys params rep dep := by
  obtain ⟨rep, dep, hls⟩ := h_ls
  let workers := IteratedProd.subtypesToList lctxs
  let ctx' : BaseSearchContext σ κ σₕ asm :=
    { mctx.base with currentFrontierDepth := mctx.base.currentFrontierDepth + 1 }
  obtain ⟨h_length, h_local⟩ : workers.length = _ ∧ _ := IteratedProd.externalize_proofs lctxs
  have h_workers : ∀ lctx ∈ workers,
      (∃ P, MapReduceSearchContextLocalInvariants sys params mctx.globalSeen P lctx) ∧ lctx.LogSound sys params rep := by
    intro lctx h_in
    rw [← List.map_snd_zip (Nat.le_of_eq h_length)] at h_in
    obtain ⟨⟨P, lctx⟩, h_zip, rfl⟩ := List.mem_map.mp h_in
    obtain ⟨h_inv, h_sound⟩ := h_local _ _ h_zip
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.of_mem_zip h_zip).1
    refine ⟨⟨_, h_inv⟩, h_sound rep fun c hc => hls.tovisit_rep c ?_⟩
    exact (ListSplit.splitList_mem_iff numSplits chunkSize numLarge mctx.tovisit c).mp ⟨a, ha, hc⟩
  have h_base := BaseSearchContext.mergeWithoutDepthChange_foldl_sound sys params (acc := ctx')
    (ctxs := workers.map (·.base)) ⟨hls.violations_sound, hls.termination_sound⟩ (by
      simp only [List.mem_map] ; rintro _ ⟨lctx, h_in, rfl⟩
      exact (h_workers lctx h_in).2.toViolationTerminationSound)
  rw [List.foldl_map] at h_base
  obtain ⟨merged, ⟨pfx, h_pfx, h_nodup, -, h_inQ, h_content⟩, h_merge⟩ :=
    mergeLayer_description ⟨workers.foldl BaseSearchContext.mergeWorker ctx', 0, [], mctx.globalSeen⟩
      (workers.map (·.queue)) rfl
  dsimp only [mergeWithLocalOnes]
  rw [h_merge] ; simp only [List.map_id] at h_pfx ; simp only [h_pfx]
  simp only [List.mem_flatten, List.mem_map] at h_inQ
  have h_items : ∀ item ∈ pfx, mctx.globalSeen.get? item.fingerprint = none ∧
      fp.view item.state = item.fingerprint ∧ ∃ p l i sp,
      item.entry = .step p l i ∧ rep p = some sp ∧ (sys.tr th sp).successes[i]? = some (l, item.state) := by
    intro item hitem
    obtain ⟨_, ⟨lctx, h_in, rfl⟩, h_q⟩ := h_inQ item hitem
    obtain ⟨⟨_, h_inv⟩, h_sound⟩ := h_workers lctx h_in
    exact ⟨ShardedMapUSize.not_mem_iff_get?_none.mp (h_inv.tovisit_globalSeen_disjoint item h_q),
      (h_inv.queue_sound _ _ ⟨item.entry, h_q⟩).2.2.symm, h_sound.entries_sound item h_q⟩
  obtain ⟨rep', dep', hinv, hitems, hmono⟩ := hls.log_invs.update_layer sys pfx h_nodup
    (fun item hi => (h_items item hi).1) (fun item hi => (h_items item hi).2.1)
    (fun item hi => (h_items item hi).2.2)
    (look' := ShardedMapUSize.get? (mctx.globalSeen.insertMany merged.seen))
    (fun item hi => by
      simp [ShardedMapUSize.get?_insertMany, (h_content _ _).mpr (List.mem_map_of_mem hi)])
    (fun x hx => by
      rw [ShardedMapUSize.get?_insertMany]
      apply Option.or_eq_right_of_none
      simp only [Option.eq_none_iff_forall_ne_some]
      grind only [List.mem_map])
  exact ⟨rep', dep', ⟨fun v hv => (h_base.violations_sound v hv).mono sys hmono,
    h_base.termination_sound.mono sys hmono⟩, hinv, hitems⟩

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

def breadthFirstSearchParallel {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  (params : SearchParameters ρ σ)
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (parallelCfg : ParallelConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken) :
  m (LawfulMapReduceSearchContextMain (fp := fp) (Shard := Shard) (numShards := parallelCfg.numShards) sys params) := do
  let mut mctx : LawfulMapReduceSearchContextMain (fp := fp) (Shard := Shard) (numShards := parallelCfg.numShards)
      sys params :=
    Subtype.mk (MapReduceSearchContextMain.initial sys.initStates)
      ⟨MapReduceSearchContextMainInvariants.initial sys params, MapReduceSearchContextMain.LogSound.initial sys params⟩
  let mut lastUpdateTime : Nat := 0
  let mut cancelled := false
  while h_not_finished : mctx.val.base.hasFinished = false do
    let mctxVal := mctx.val
    have h_not_finished_val : mctxVal.base.hasFinished = false := h_not_finished
    have h_mctx : MapReduceSearchContextMainInvariants sys params mctxVal := mctx.property.1
    have h_ls : ∃ rep dep, mctxVal.LogSound sys params rep dep := mctx.property.2
    let base := mctxVal.base
    let tovisitLen := mctxVal.tovisitLen
    let tovisit := mctxVal.tovisit
    let globalSeen := mctxVal.globalSeen
    -- Check if the frontier is empty
    if h_empty : tovisit.isEmpty then
      mctx := Subtype.mk ⟨{ base with finished := some (.exploredAllReachableStates) }, tovisitLen, tovisit, globalSeen⟩
        ⟨h_mctx.setExploredAll_preserves_invs h_not_finished_val h_empty,
          h_ls.elim fun rep h => h.elim fun dep h => ⟨rep, dep, h.setExploredAll⟩⟩
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
      let mctxValForMerge : MapReduceSearchContextMain σ κ σₕ asm Shard parallelCfg.numShards :=
        { base := { base with currentFrontierDepth := base.currentFrontierDepth + 1 } , tovisitLen := 0, tovisit := [], globalSeen := globalSeen }
      let mctxVal' := mctxValForMerge.mergeWithLocalOnes (preds := preds) results
      have h_mctx' : MapReduceSearchContextMainInvariants sys params mctxVal' ∧
          ∃ rep dep, mctxVal'.LogSound sys params rep dep :=
        ⟨MapReduceSearchContextMain.mergeWithLocalOnes_preserves_invs h_not_finished_val h_mctx results,
          MapReduceSearchContextMain.mergeWithLocalOnes_log_sound h_ls results⟩
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
  let ⟨mctxVal, h_mctx⟩ := mctx
  let displayBase : BaseSearchContext σ κ σₕ asm :=
    { mctxVal.base with currentFrontierDepth := mctxVal.base.completedDepth }
  updateProgressDuringBFS progressInstanceId displayBase mctxVal.tovisitLen mctxVal.globalSeen.size
  if cancelled then
    return ⟨{ mctxVal with base := { mctxVal.base with finished := some (.earlyTermination .cancelled) } },
      ⟨h_mctx.1.setCancelled, h_mctx.2.elim fun rep h => h.elim fun dep h => ⟨rep, dep, h.setCancelled⟩⟩⟩
  else
    return ⟨mctxVal, h_mctx⟩

end Veil.ModelChecker.Concrete
