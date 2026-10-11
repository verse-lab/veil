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

/-! ### The merge of a layer, shard by shard

The items of a layer are put in buckets by the shard of their fingerprint, on the main thread, one
hash per item. Each bucket is then merged into its shard of the seen set in a task of its own: the
items whose fingerprints the shard does not have yet are added to it with their log entries, and
kept for the next frontier. -/

open ShardedSetUInt in
/-- The items of `lists`, in buckets by the shard of their fingerprint, each bucket last first. -/
@[inline]
def bucketsOf (numShards : PosUSize) (lists : List (List (MapReduceQueueItem σₕ σ κ))) :
    VectorUSize (List (MapReduceQueueItem σₕ σ κ)) numShards :=
  lists.foldl (init := .replicateUSize numShards [])
    (VectorUSize.distributeInto MapReduceQueueItem.fingerprint numShards.property)

open ShardedSetUInt in
theorem mem_bucketsOf {numShards : PosUSize} {lists : List (List (MapReduceQueueItem σₕ σ κ))}
    {i : USize} {h : i < numShards} {x : MapReduceQueueItem σₕ σ κ} :
    x ∈ (bucketsOf numShards lists).uget i h ↔
      x ∈ lists.flatten ∧ shardIdxOfUSize numShards x.fingerprint = i := by
  unfold bucketsOf VectorUSize.distributeInto
  rw [← List.foldl_flatten, ← VectorUSize.distributeInto, VectorUSize.mem_uget_distributeInto,
    VectorUSize.uget_replicateUSize] ; simp

/-- The result of merging the bucket of a shard into it. -/
structure ShardMerge (σ κ σₕ Shard : Type) where
  /-- The kept items of the bucket, last first: the first of each fingerprint that the shard did not
  have. -/
  kept : List (MapReduceQueueItem σₕ σ κ)
  /-- The shard with the log entries of the kept items. -/
  shard : Shard

/-- Merge a bucket into its shard of the seen set: add each item whose fingerprint the shard does
not have yet, with its log entry, and keep it. -/
@[inline]
def mergeShard (bucket : List (MapReduceQueueItem σₕ σ κ)) (shard : Shard) : ShardMerge σ κ σₕ Shard :=
  bucket.foldl (init := ⟨[], shard⟩) fun acc item =>
    if KeyShard.contains acc.shard item.fingerprint then acc
    else ⟨item :: acc.kept, MapShard.insert acc.shard item.fingerprint item.entry⟩

/-- Merging a bucket into a shard is a deduplicating fold whose map is the shard. -/
theorem mergeShard_description (bucket : List (MapReduceQueueItem σₕ σ κ)) (shard : Shard) :
    DedupFoldDescriptionWithAcc (key := MapReduceQueueItem.fingerprint) (val := MapReduceQueueItem.entry)
      (proj := id) (lst := ShardMerge.kept) (look := fun acc k => MapShard.get? acc.shard k)
      bucket ⟨[], shard⟩ (mergeShard bucket shard) := by
  unfold mergeShard
  apply DedupFoldDescriptionWithAcc.of_foldl <;> intro acc item h
  · simp [← MapShard.mem_iff_isSome_get?] at h
    open Classical in simp [KeyShard.contains_iff_mem, h]
  · have hc : KeyShard.contains acc.shard item.fingerprint = false := by
      rw [Bool.eq_false_iff, ne_eq, KeyShard.contains_iff_mem, MapShard.mem_iff_isSome_get? (β := LogEntry σₕ κ)]
      simp [h]
    simp only [hc, Bool.false_eq_true, if_false, id, MapShard.get?_insert, implies_true, and_self]

-- CHECK Is this proof necessary?
open ShardedSetUInt in
/-- Each merged shard of the seen set `gs` holds the keys of its own index only. -/
theorem mergeShards_keys {numShards : PosUSize} {lists : List (List (MapReduceQueueItem σₕ σ κ))}
    (gs : MapReduceGlobalSeen σₕ κ Shard numShards) (i : USize) (hi : i < numShards) (k : σₕ)
    (hk : k ∈ (((bucketsOf numShards lists).zipPar gs.shards mergeShard).uget i hi).shard) :
    shardIdxOfUSize numShards k = i := by
  rw [VectorUSize.uget_zipPar, MapShard.mem_iff_isSome_get? (β := LogEntry σₕ κ), Option.isSome_iff_exists] at hk
  obtain ⟨v, hv⟩ := hk
  obtain ⟨pfx, -, -, -, h_inQ, h_content⟩ :=
    mergeShard_description ((bucketsOf numShards lists).uget i hi) (gs.shards.uget i hi)
  rcases (h_content k v).mp hv with h | h
  · exact gs.h_in_correct_shard i hi k ((MapShard.mem_iff_isSome_get? (β := LogEntry σₕ κ)).mpr (by simp [h]))
  · obtain ⟨a, ha, h_eq⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at h_eq ; obtain ⟨rfl, -⟩ := h_eq
    exact (mem_bucketsOf.mp (h_inQ a ha).1).2

/-- Merge the items of `lists` into the main context: keep one item of each fingerprint that the
seen set does not have yet, add it to the frontier, and its fingerprint with its log entry to the
seen set. The merge of a BFS layer (`mergeWithLocalOnes`) and of the initial states
(`MapReduceSearchContextMain.initial`). Each shard is merged in a task of its own. The frontier
grows by as many items as the seen set. -/
def MapReduceSearchContextMain.mergeLayer (mctx : MapReduceSearchContextMain σ κ σₕ asm Shard numShards)
    (lists : List (List (MapReduceQueueItem σₕ σ κ))) : MapReduceSearchContextMain σ κ σₕ asm Shard numShards :=
  let ⟨ctx, len, q, globalSeen⟩ := mctx
  -- before the tasks take over the shards, to update them in place
  let size := globalSeen.size
  let merges := (bucketsOf numShards lists).zipPar globalSeen.shards mergeShard
  let seen : MapReduceGlobalSeen σₕ κ Shard numShards := .ofMap merges ShardMerge.shard (mergeShards_keys globalSeen)
  ⟨ctx, len + (seen.size - size), merges.val.foldr (init := q) (·.kept ++ ·), seen⟩

section LayerMerge

open ShardedSetUInt

variable {numShards : PosUSize} {lists : List (List (MapReduceQueueItem σₕ σ κ))}
  {shards : VectorUSize Shard numShards}

/-- Each merged shard of `lists` is described by the deduplicating fold of its bucket into it. -/
theorem mergeShards_description (i : USize) (hi : i < numShards) :
    DedupFoldDescriptionWithAcc (key := MapReduceQueueItem.fingerprint) (val := MapReduceQueueItem.entry)
      (proj := id) (lst := ShardMerge.kept) (look := fun acc k => MapShard.get? acc.shard k)
      ((bucketsOf numShards lists).uget i hi) ⟨[], shards.uget i hi⟩
      (((bucketsOf numShards lists).zipPar shards mergeShard).uget i hi) := by
  rw [VectorUSize.uget_zipPar] ; exact mergeShard_description _ _

/-- The kept items of a merged shard of `lists` are items of `lists` of that shard. -/
theorem mergeShards_kept {i : USize} {hi : i < numShards} {a : MapReduceQueueItem σₕ σ κ}
    (ha : a ∈ (((bucketsOf numShards lists).zipPar shards mergeShard).uget i hi).kept) :
    a ∈ lists.flatten ∧ shardIdxOfUSize numShards a.fingerprint = i := by
  obtain ⟨pfx, h_lst, -, -, h_inQ, -⟩ := mergeShards_description (shards := shards) (lists := lists) i hi
  simp only [List.map_id, List.append_nil] at h_lst
  exact mem_bucketsOf.mp (h_inQ a (h_lst ▸ ha)).1

theorem mem_flatMap_mergeShards {a : MapReduceQueueItem σₕ σ κ} :
    a ∈ ((bucketsOf numShards lists).zipPar shards mergeShard).val.toList.flatMap (·.kept) ↔
      ∃ (i : USize) (hi : i < numShards), a ∈ (((bucketsOf numShards lists).zipPar shards mergeShard).uget i hi).kept := by
  simp only [List.mem_flatMap, VectorUSize.mem_toList_iff]
  constructor
  · rintro ⟨r, ⟨i, hi, rfl⟩, ha⟩ ; exact ⟨i, hi, ha⟩
  · rintro ⟨i, hi, ha⟩ ; exact ⟨_, ⟨i, hi, rfl⟩, ha⟩

end LayerMerge

-- CHECK Still don't believe this proof is this long, but go back to this later
open ShardedSetUInt in
/-- The merge of a layer is a deduplicating fold of its items into the main context, whose map is
the seen set: an item is kept, put in front of the frontier and added to the seen set with its log
entry, exactly when it is the first of its fingerprint and the seen set does not have that
fingerprint yet. The frontier's length grows with it. -/
theorem MapReduceSearchContextMain.mergeLayer_description
    (mctx : MapReduceSearchContextMain σ κ σₕ asm Shard numShards) (lists : List (List (MapReduceQueueItem σₕ σ κ))) :
    (mctx.mergeLayer lists).base = mctx.base ∧
    (mctx.mergeLayer lists).tovisitLen + mctx.tovisit.length = mctx.tovisitLen + (mctx.mergeLayer lists).tovisit.length ∧
    DedupFoldDescriptionWithAcc (key := MapReduceQueueItem.fingerprint) (val := MapReduceQueueItem.entry)
      (proj := id) (lst := MapReduceSearchContextMain.tovisit) (look := fun m k => m.globalSeen.get? k)
      lists.flatten mctx (mctx.mergeLayer lists) := by
  suffices hd : DedupFoldDescriptionWithAcc (key := MapReduceQueueItem.fingerprint) (val := MapReduceQueueItem.entry)
      (proj := id) (lst := MapReduceSearchContextMain.tovisit) (look := fun m k => m.globalSeen.get? k)
      lists.flatten mctx (mctx.mergeLayer lists) by
    refine ⟨by rcases mctx ; rfl, ?_, hd⟩
    -- the seen set grows by the fingerprints of the kept items, and the frontier by the kept items
    have h_keys := hd.length_keys ShardedUSize.nodup_toList ShardedUSize.nodup_toList
      (fun _ => ShardedUSize.mem_toList.trans ShardedMapUSize.mem_iff_isSome_get?)
      (fun _ => ShardedUSize.mem_toList.trans ShardedMapUSize.mem_iff_isSome_get?)
    have h_len : (mctx.mergeLayer lists).tovisitLen =
        mctx.tovisitLen + ((mctx.mergeLayer lists).globalSeen.size - mctx.globalSeen.size) := by
      rcases mctx ; rfl
    obtain ⟨pfx, h_lst, -⟩ := hd
    simp only [← ShardedUSize.length_toList, h_lst, List.length_append] at h_keys
    simp only [h_len, h_lst, List.length_append]
    omega
  rcases mctx with ⟨ctx, len, q, gs⟩
  unfold mergeLayer ; dsimp only
  -- `gs.get? k` is defined as `MapShard.get?` on the shard of `k`, which the merges are described with
  refine ⟨((bucketsOf numShards lists).zipPar gs.shards mergeShard).val.toList.flatMap (·.kept),
    ?_, ?_, ?_, ?_, ?_⟩
  · -- the frontier: the kept items of all shards, in front of the old one
    simp only [List.map_id, ← Array.foldr_toList]
    rw [List.foldr_append_eq_append] ; grind
  · -- the fingerprints of the kept items are distinct: within a shard, and across shards
    have h := VectorUSize.nodup_flatMap_of_shards (v := (bucketsOf numShards lists).zipPar gs.shards mergeShard)
      (fun r => r.kept.map MapReduceQueueItem.fingerprint)
      (fun i hi k hk => by grind only [List.mem_map, → mergeShards_kept])
      (fun i hi => by
        obtain ⟨pfx, h_lst, h_nodup, -⟩ := mergeShards_description (shards := gs.shards) (lists := lists) i hi
        grind only [List.map_id, List.append_nil])
    simpa only [List.map_flatMap] using h
  · -- each item whose fingerprint is new has its fingerprint kept, in the shard of its fingerprint
    intro a ha h_new
    obtain ⟨pfx, h_lst, -, h_cov, -⟩ := mergeShards_description (shards := gs.shards) (lists := lists)
      (shardIdxOfUSize numShards a.fingerprint) (shardIdxOfUSize_lt _ numShards.property)
    have := h_cov a (mem_bucketsOf.mpr ⟨ha, rfl⟩) h_new
    grind only [List.map_id, List.append_nil, List.mem_map, mem_flatMap_mergeShards]
  · -- each kept item is an item of the layer, whose fingerprint was new
    intro a ha
    obtain ⟨i, hi, ha⟩ := mem_flatMap_mergeShards.mp ha
    obtain ⟨pfx, h_lst, -, -, h_inQ, -⟩ := mergeShards_description (shards := gs.shards) (lists := lists) i hi
    obtain ⟨h_in, rfl⟩ := mergeShards_kept ha
    change a ∈ lists.flatten ∧ MapShard.get? (gs.shards.uget _ hi) a.fingerprint = none
    grind only [List.map_id, List.append_nil]
  · -- the seen set maps each kept fingerprint to its entry, in the shard of the fingerprint
    intro k v
    simp only [ShardedMapUSize.get?_ofMap]
    obtain ⟨pfx, h_lst, -, -, -, h_content⟩ := mergeShards_description (shards := gs.shards) (lists := lists)
      (shardIdxOfUSize numShards k) (shardIdxOfUSize_lt _ numShards.property)
    simp only [List.map_id, List.append_nil] at h_lst
    rw [h_content, ← h_lst]
    apply or_congr Iff.rfl
    grind only [List.mem_map, mem_flatMap_mergeShards, → mergeShards_kept]

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
  obtain ⟨h_base, h_tvl, hd⟩ := m0.mergeLayer_description [initialMapReduceQueueItems sys.initStates]
  replace hd := DedupFoldDescription.ofDedupFoldDescriptionWithAcc hd h_tv
    (fun x => ShardedMapUSize.not_mem_iff_get?_none.mp (h_gs x))
  have h_seen := hd.isSome_iff (key' := MapReduceQueueItem.fingerprint) (fun _ _ => rfl)
  generalize m0.mergeLayer [initialMapReduceQueueItems sys.initStates] = res at *
  rcases res with ⟨base, len, tovisit, seen⟩
  simp only [← ShardedMapUSize.mem_iff_isSome_get?] at h_seen
  obtain ⟨pfx, h_pfx, h_nodup, h_cov, h_inQ, h_content⟩ := hd
  dsimp only at h_base h_tvl h_pfx h_seen
  simp only [h_tv, h_len, List.length_nil, Nat.add_zero, Nat.zero_add, List.map_id] at h_tvl h_pfx
  subst h_base h_tvl h_pfx
  simp [initialMapReduceQueueItems] at h_cov h_inQ
  constructor ; on_goal 1=> constructor
  all_goals (try simp [h_seen, h_fin]) ; try grind
  intro s hs ; obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
  exact h_cov ⟨fp.view sys.initStates[i], sys.initStates[i], .init i⟩ i hi rfl

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
  obtain ⟨h_base, -, hd⟩ := m0.mergeLayer_description [initialMapReduceQueueItems sys.initStates]
  replace hd := DedupFoldDescription.ofDedupFoldDescriptionWithAcc hd h_tv
    (fun x => ShardedMapUSize.not_mem_iff_get?_none.mp (h_gs x))
  generalize m0.mergeLayer [initialMapReduceQueueItems sys.initStates] = res at *
  rcases res with ⟨base, len, tovisit, seen⟩
  obtain ⟨pfx, h_pfx, h_nodup, h_cov, h_inQ, h_content⟩ := hd
  simp [initialMapReduceQueueItems] at h_pfx h_inQ h_content
  dsimp only at h_base ; subst_vars
  let rep (a : σₕ) := (seen.get? a).bind fun
    | .init j => sys.initStates[j]?
    | .step .. => none
  exists rep, fun _ => 0 ; dsimp [rep]
  refine ⟨⟨by simp [h_vs], by simp [h_fin, TerminationSound]⟩, ?_, ?_⟩    -- nothing recorded yet
  on_goal 1=> constructor
  all_goals (try simp [Option.bind_eq_some_iff]) ; try grind
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
  obtain ⟨h_base', h_tvl, ⟨pfx, h_pfx, h_nodup, h_cov, h_inQ, h_content⟩⟩ :=
    mergeLayer_description ⟨mbase, 0, [], gs⟩ (lctxs'.map (·.queue))
  generalize mergeLayer ⟨mbase, 0, [], gs⟩ (lctxs'.map (·.queue)) = res at *
  rcases res with ⟨base', len', tovisit', seen'⟩
  dsimp only at h_base' h_tvl h_pfx h_content h_inQ h_cov
  simp only [List.map_id, List.append_nil, List.length_nil, Nat.add_zero, Nat.zero_add] at h_pfx h_tvl
  subst base' h_tvl ; subst tovisit'
  -- the merged seen set: the old one, with the fingerprints of the kept items
  have h_fps : ∀ x, x ∈ seen' ↔ x ∈ gs ∨ x ∈ pfx.map MapReduceQueueItem.fingerprint := by
    intro x
    simp only [ShardedMapUSize.mem_iff_isSome_get?, Option.isSome_iff_exists, h_content, List.mem_map,
      Prod.mk.injEq]
    grind
  -- each item of the layer has its fingerprint in the old seen set, or kept
  have h_in_pfx : ∀ a ∈ (lctxs'.map (·.queue)).flatten,
      a.fingerprint ∈ gs ∨ a.fingerprint ∈ pfx.map MapReduceQueueItem.fingerprint := by
    intro a ha
    by_cases h : a.fingerprint ∈ gs
    · exact .inl h
    · exact .inr (h_cov a ha (ShardedMapUSize.not_mem_iff_get?_none.mp h))
  replace h_inQ := fun a ha => (h_inQ a ha).1
  simp [List.mem_flatten] at h_inQ h_fps h_in_pfx

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
        have h_unfinished : ∀ lctx ∈ lctxs', lctx.base.finished = none := by
          simp only [h_base_desc, List.find?_map, Option.bind_map, Function.comp_def] at h_not_finished_mbase
          cases h_find : lctxs'.find? (fun lctx => lctx.base.hasFinished) <;>
            grind only [Option.bind_none, Option.bind_some, List.find?_eq_none, List.find?_some,
              BaseSearchContext.hasFinished, Option.isSome_iff_ne_none]
        rcases h_local_invs with ⟨_, _, h_dj, h_same_dom, h_succ_coll⟩
        specialize h_succ_coll (h_unfinished _ (List.getElem_mem _))
          (fp.view u) u ent (h_getElem_chunk ▸ h_in_chunk)
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
  obtain ⟨h_base', -, ⟨pfx, h_pfx, h_nodup, -, h_inQ, h_content⟩⟩ :=
    mergeLayer_description ⟨workers.foldl BaseSearchContext.mergeWorker ctx', 0, [], mctx.globalSeen⟩
      (workers.map (·.queue))
  dsimp only [mergeWithLocalOnes]
  generalize mergeLayer ⟨workers.foldl BaseSearchContext.mergeWorker ctx', 0, [], mctx.globalSeen⟩
    (workers.map (·.queue)) = res at *
  rcases res with ⟨base', len', tovisit', seen'⟩
  dsimp only at h_base' h_pfx h_content h_inQ
  subst h_base' ; simp only [List.map_id, List.append_nil] at h_pfx ; subst tovisit'
  simp only [List.mem_flatten, List.mem_map] at h_inQ
  -- each kept item is new, is a transition from the old frontier, and has its fingerprint
  have h_items : ∀ item ∈ pfx, mctx.globalSeen.get? item.fingerprint = none ∧
      fp.view item.state = item.fingerprint ∧ ∃ p l i sp,
      item.entry = .step p l i ∧ rep p = some sp ∧ (sys.tr th sp).successes[i]? = some (l, item.state) := by
    intro item hitem
    obtain ⟨⟨_, ⟨lctx, h_in, rfl⟩, h_q⟩, h_new⟩ := h_inQ item hitem
    obtain ⟨⟨_, h_inv⟩, h_sound⟩ := h_workers lctx h_in
    exact ⟨h_new, (h_inv.queue_sound _ _ ⟨item.entry, h_q⟩).2.2.symm, h_sound.entries_sound item h_q⟩
  obtain ⟨rep', dep', hinv, hitems, hmono⟩ := hls.log_invs.update_layer sys pfx h_nodup
    (fun item hi => (h_items item hi).1) (fun item hi => (h_items item hi).2.1)
    (fun item hi => (h_items item hi).2.2)
    (look' := ShardedMapUSize.get? seen')
    (fun item hi => (h_content _ _).mpr (.inr (List.mem_map_of_mem hi)))
    (fun x hx => by
      apply Option.ext ; intro v
      rw [h_content] ; simp only [List.mem_map, Prod.mk.injEq, or_iff_left_iff_imp]
      rintro ⟨item, hitem, rfl, -⟩ ; exact absurd rfl (hx item hitem))
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

/-- `mctx` marked as cancelled, which finishes it. -/
def LawfulMapReduceSearchContextMain.setCancelled {params : SearchParameters ρ σ} {th : ρ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}
  (mctx : LawfulMapReduceSearchContextMain (fp := fp) (Shard := Shard) (numShards := numShards) sys params) :
  { mctx : LawfulMapReduceSearchContextMain (fp := fp) (Shard := Shard) (numShards := numShards) sys params //
    mctx.val.base.finished.isSome } :=
  ⟨⟨{ mctx.val with base := { mctx.val.base with finished := some (.earlyTermination .cancelled) } },
    ⟨mctx.property.1.setCancelled, mctx.property.2.elim fun rep h => h.elim fun dep h => ⟨rep, dep, h.setCancelled⟩⟩⟩,
    rfl⟩

/-- The search loop of `breadthFirstSearchParallel`, from `mctx`. It returns only once the search
has finished, so the context it returns records why. -/
def breadthFirstSearchParallel.loop {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
  (params : SearchParameters ρ σ)
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (parallelCfg : ParallelConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken)
  (mctx : LawfulMapReduceSearchContextMain (fp := fp) (Shard := Shard) (numShards := parallelCfg.numShards) sys params)
  (lastUpdateTime : Nat) :
  m { mctx : LawfulMapReduceSearchContextMain (fp := fp) (Shard := Shard) (numShards := parallelCfg.numShards)
        sys params // mctx.val.base.finished.isSome } := do
  if h_finished : mctx.val.base.finished.isSome then
    return ⟨mctx, h_finished⟩
  else
    let mctxVal := mctx.val
    have h_not_finished_val : mctxVal.base.hasFinished = false := by
      simpa [BaseSearchContext.hasFinished] using h_finished
    have h_mctx : MapReduceSearchContextMainInvariants sys params mctxVal := mctx.property.1
    have h_ls : ∃ rep dep, mctxVal.LogSound sys params rep dep := mctx.property.2
    let base := mctxVal.base
    let tovisitLen := mctxVal.tovisitLen
    let tovisit := mctxVal.tovisit
    let globalSeen := mctxVal.globalSeen
    -- Check if the frontier is empty
    if h_empty : tovisit.isEmpty then
      return ⟨Subtype.mk ⟨{ base with finished := some (.exploredAllReachableStates) }, tovisitLen, tovisit, globalSeen⟩
        ⟨h_mctx.setExploredAll_preserves_invs h_not_finished_val h_empty,
          h_ls.elim fun rep h => h.elim fun dep h => ⟨rep, dep, h.setExploredAll⟩⟩, rfl⟩
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
        let mctx : LawfulMapReduceSearchContextMain (fp := fp) (Shard := Shard) (numShards := parallelCfg.numShards)
            sys params := Subtype.mk ⟨base', tovisitLen', tovisit', globalSeen'⟩ (heq.symm ▸ h_mctx')
        -- Check for cancellation/handoff at most once per second
        let newtime? ← checkCancellationWithoutPeriodicUpdate progressInstanceId lastUpdateTime 1000 cancelToken
        match newtime? with
        | .updateTime t => breadthFirstSearchParallel.loop params sys parallelCfg progressInstanceId cancelToken mctx t
        | .searchCancelled => return mctx.setCancelled
        | .noUpdate => breadthFirstSearchParallel.loop params sys parallelCfg progressInstanceId cancelToken mctx lastUpdateTime
partial_fixpoint

def breadthFirstSearchParallel {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
  (params : SearchParameters ρ σ)
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (parallelCfg : ParallelConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken) :
  m { mctx : LawfulMapReduceSearchContextMain (fp := fp) (Shard := Shard) (numShards := parallelCfg.numShards)
        sys params // mctx.val.base.finished.isSome } := do
  let res ← breadthFirstSearchParallel.loop (fp := fp) params sys parallelCfg progressInstanceId cancelToken
    (Subtype.mk (MapReduceSearchContextMain.initial sys.initStates)
      ⟨MapReduceSearchContextMainInvariants.initial sys params, MapReduceSearchContextMain.LogSound.initial sys params⟩) 0
  -- Final update to ensure stats reflect finished state, with the depth of the last frontier
  -- explored rather than of the next one. Only the display shows that depth: setting it as the
  -- frontier depth of the context would change its `completedDepth` too.
  let mctxVal := res.val.val
  let displayBase : BaseSearchContext σ κ σₕ asm :=
    { mctxVal.base with currentFrontierDepth := mctxVal.base.completedDepth }
  updateProgressDuringBFS progressInstanceId displayBase mctxVal.tovisitLen mctxVal.globalSeen.size
  return res

end Veil.ModelChecker.Concrete
