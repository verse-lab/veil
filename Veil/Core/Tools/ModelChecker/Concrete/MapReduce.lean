import Veil.Core.Tools.ModelChecker.Concrete.MapReduceLemmas
import Veil.Core.Tools.ModelChecker.Concrete.Progress
import Veil.Core.Tools.ModelChecker.Concrete.Subtypes
import Veil.Util.ListSplit

namespace Veil.ModelChecker.Concrete
open Veil

attribute [local grind =] ShardedTreeSetUSize.contains_iff_mem ShardedHashSetUSize.contains_iff_mem
attribute [local simp] ShardedTreeSetUSize.contains_iff_mem ShardedHashSetUSize.contains_iff_mem
  ShardedHashSetUSize.not_mem_emptyUSize

variable {ρ σ κ σₕ asm : Type} [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm] [Ord σₕ]

@[inline]
def MapReduceSearchContextLocal.hasFinished (lctx : MapReduceSearchContextLocal σ κ σₕ asm) : Bool :=
  lctx.1.hasFinished

section

variable (globalSeen : ShardedTreeSetUSize σₕ)

-- FIXME: The logic of `tryExploreNeighbor`, `processSuccessors`, and `processState`
-- seems very similar to the sequential processing logic. We should try to unify them

/-- Process a single neighbor in the local context.
    `globalSeen` is the main context's log, used to check if a state is already globally seen. -/
@[inline]
def MapReduceSearchContextLocal.tryExploreNeighbor
  (fpSt : σₕ)
  (lctx : MapReduceSearchContextLocal σ κ σₕ asm)
  (label : κ) (succ : σ) : MapReduceSearchContextLocal σ κ σₕ asm :=
  let (ctx, q) := lctx
  let fingerprint := fp.view succ
  if globalSeen.contains fingerprint || ctx.log.contains fingerprint then
    ({ ctx with actionStatsMap := ActionStatUpdate.increment label false ctx.actionStatsMap }, q)
  else
    ({ ctx with
      log := ctx.log.insert fingerprint (Option.some (fpSt, label)),
      actionStatsMap := ActionStatUpdate.increment label true ctx.actionStatsMap
    }, ⟨fingerprint, succ⟩ :: q)

/-- Process all successors of a state in the local context. -/
def MapReduceSearchContextLocal.processSuccessors
  (fpSt : σₕ)
  (successors : List (κ × σ))
  (lctx : MapReduceSearchContextLocal σ κ σₕ asm) : MapReduceSearchContextLocal σ κ σₕ asm :=
  successors.foldl (init := lctx) fun current_lctx (label, postState) =>
    MapReduceSearchContextLocal.tryExploreNeighbor globalSeen fpSt current_lctx label postState

/-- Process a single state: check violations via BaseSearchContext.processState,
    then process successors if no early termination. -/
def MapReduceSearchContextLocal.processState
  (params : SearchParameters ρ σ) (th : ρ)
  (fpSt : σₕ) (curr : σ)
  (outcomes : List (κ × ExecutionOutcome ℤ σ))
  (lctx : MapReduceSearchContextLocal σ κ σₕ asm) : MapReduceSearchContextLocal σ κ σₕ asm :=
  let (ctx, q) := lctx
  let (ctx', outcomesOpt) := ctx.processState params th fpSt curr outcomes
  match outcomesOpt with
  | none => (ctx', q)
  | some successfulTransitions =>
    -- CHECK Is it useful/possible to remove the call to `successfulTransitions.length`?
    let ctx'' := { ctx' with statesFound := ctx'.statesFound + successfulTransitions.length }
    MapReduceSearchContextLocal.processSuccessors globalSeen fpSt successfulTransitions (ctx'', q)

end

section

-- FIXME: The proofs are also very similar to the sequential one

variable {params : SearchParameters ρ σ} {th : ρ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) ℤ κ (List (κ × ExecutionOutcome ℤ σ)) th}
  {lctx : MapReduceSearchContextLocal σ κ σₕ asm}
  {globalSeen : ShardedTreeSetUSize σₕ}

theorem MapReduceSearchContextLocalInvariants.processSuccessors_preserves_invs
  {p : MapReduceQueueItem σₕ σ → Prop}
  {fpSt} (curr : σ) {succs}
  (h_not_finished : lctx.1.finished = .none)
  (h_reachable : sys.reachable curr)
  (h_succs : ∀ (label : κ) (st : σ),
    (label, st) ∈ succs ↔ (label, ExecutionOutcome.success st) ∈ sys.tr th curr)
  (lctx_invs : MapReduceSearchContextLocalInvariants sys params globalSeen p lctx) :
  MapReduceSearchContextLocalInvariants sys params globalSeen p (lctx.processSuccessors globalSeen fpSt succs) := by
  unfold MapReduceSearchContextLocal.processSuccessors ; dsimp
  -- need to attach some proofs
  have htmp := List.unattach_attachWith (p := fun a => (a.1, ExecutionOutcome.success a.2) ∈ sys.tr th curr)
    (l := succs) (H := by simp [← h_succs])
  generalize succs.attachWith _ _ = succs' at htmp
  rw [← htmp] ; clear htmp h_succs
  induction succs' generalizing lctx with
  | nil => simp ; assumption
  | cons x succs ih =>
    rcases x with ⟨⟨label, postState⟩, h⟩ ; dsimp [List.foldl] ; apply ih
    · fun_cases MapReduceSearchContextLocal.tryExploreNeighbor <;> dsimp at h_not_finished <;> simp [h_not_finished]
    · clear ih
      fun_cases MapReduceSearchContextLocal.tryExploreNeighbor
      on_goal 1=> cases lctx_invs ; constructor <;> assumption
      -- enqueue case
      rename_i ctx sq fingerprint h_not_seen ; subst fingerprint
      simp at h_not_seen h_not_finished
      rcases lctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_not_explored_all, h_dj, h_same_dom, h_succ_coll⟩ ; dsimp only at *
      constructor ; on_goal 1=> constructor
      all_goals dsimp only at * ; try grind
      simp ; grind

omit params th sys in
theorem MapReduceSearchContextLocalInvariants.processSuccessors_successors_collected
  {fpSt succs} :
  letI res := lctx.processSuccessors globalSeen fpSt succs
  ∀ l v, (l, v) ∈ succs.reverse → ((fp.view v) ∈ globalSeen ∨ (fp.view v) ∈ res.1.log) := by
  unfold MapReduceSearchContextLocal.processSuccessors ; dsimp
  -- use `foldr` to make induction easier
  rw [List.foldl_eq_foldr_reverse]
  generalize succs.reverse = succs
  induction succs with
  | nil => simp
  | cons x succs ih =>
    rcases x with ⟨label, postState⟩ ; dsimp [List.foldr]
    simp only [List.mem_cons] ; introv ; intro h1 ; rcases h1 with h1 | h1
    · injection h1 with h1 h2 ; subst l v
      fun_cases MapReduceSearchContextLocal.tryExploreNeighbor globalSeen fpSt (List.foldr _ lctx succs) label postState <;> grind
    · rewrite (occs := .pos [1]) [MapReduceSearchContextLocal.tryExploreNeighbor]
      split_ifs with h <;> dsimp <;> grind

theorem MapReduceSearchContextLocalInvariants.processState_progress
  {p : MapReduceQueueItem σₕ σ → Prop}
  (fpSt : σₕ) (curr : σ)
  (h_reachable : sys.reachable curr)
  (h_not_finished : lctx.1.finished = .none)
  (lctx_invs : MapReduceSearchContextLocalInvariants sys params globalSeen p lctx) :
  MapReduceSearchContextLocalInvariants sys params globalSeen (fun x => p x ∨ x = ⟨fpSt, curr⟩)
    (MapReduceSearchContextLocal.processState globalSeen params th fpSt curr (sys.tr th curr) lctx) := by
  rcases lctx with ⟨ctx, q⟩ ; rcases lctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_not_explored_all, h_dj, h_succ_coll⟩ ; dsimp only at *

  dsimp [MapReduceSearchContextLocal.processState]
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
  -- normal case
  apply MapReduceSearchContextLocalInvariants.progress_by_one_state (p := p) (curr := curr) (fpSt := fpSt)
  · apply MapReduceSearchContextLocalInvariants.processSuccessors_preserves_invs
    · rfl
    · exact h_reachable
    · introv ; rw [← partitionExecutionOutcome.fst_spec, h_eq_part]
    · constructor ; on_goal 1=> constructor
      all_goals dsimp only at * ; try grind
  · introv ; intro h1
    apply MapReduceSearchContextLocalInvariants.processSuccessors_successors_collected l v
    simp ; rw [← partitionExecutionOutcome.fst_spec, h_eq_part] at h1 ; exact h1
  · simp

end

namespace LawfulMapReduceSearchContextLocal

-- CHECK For now, separate proofs out to reduce the risk of having weird performance
private theorem processWorkQueue.subproof1 {α : Type u}
  -- (p : α → Prop) : p = (fun x => p x ∨ x ∈ ([] : List α)) := by simp
  {p q : α → Prop} (h : ∀ x, q x ↔ p x ∨ x ∈ ([] : List α)) : p = q := by simp at h ; grind

private theorem processWorkQueue.subproof2 {α : Type u}
  {p q : α → Prop} {a : α} {l : List α}
  (h : ∀ x, q x ↔ p x ∨ x ∈ a :: l) : ∀ x, q x ↔ (p x ∨ x = a) ∨ x ∈ l := by grind

omit [Ord σₕ] in
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
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) ℤ κ (List (κ × ExecutionOutcome ℤ σ)) th}
  {globalSeen : ShardedTreeSetUSize σₕ}
  (queue : List (MapReduceQueueItem σₕ σ))
  {p q : MapReduceQueueItem σₕ σ → Prop} (h : ∀ x, q x ↔ p x ∨ x ∈ queue)
  (h_inqueue_reachable : ∀ item ∈ queue, sys.reachable item.state)
  (lctx : LawfulMapReduceSearchContextLocal (κ := κ) sys params globalSeen p) :
    LawfulMapReduceSearchContextLocal (κ := κ) sys params globalSeen q :=
  let ⟨v, hl⟩ := lctx
  match queue with
  | [] => ⟨v, (processWorkQueue.subproof1 h) ▸ hl⟩
  | item :: rest =>
    if h_finished : v.hasFinished
    then ⟨v, hl.finished_change_visited_pred_in_invs h_finished⟩
    else
      let ⟨fpSt, curr⟩ := item
      let v' := v.processState globalSeen params th fpSt curr (sys.tr th curr)
      -- CHECK Is this proper tail-recursive?
      processWorkQueue rest
        (processWorkQueue.subproof2 h)
        (processWorkQueue.subproof4 h_inqueue_reachable)
        <| Subtype.mk v' <| hl.processState_progress fpSt curr
          (processWorkQueue.subproof5 (α := MapReduceQueueItem σₕ σ) h_inqueue_reachable)
          (processWorkQueue.subproof3 h_finished)

/-- Main worker entry point. Creates a neutral context and processes the work queue.
    This function is called by each parallel task. -/
def bfsBigStep
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  (params : SearchParameters ρ σ) {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) ℤ κ (List (κ × ExecutionOutcome ℤ σ)) th)
  (globalSeen : ShardedTreeSetUSize σₕ)
  (completedDepth : Nat)
  (queue : List (MapReduceQueueItem σₕ σ))
  (h_inqueue_reachable : ∀ item ∈ queue, sys.reachable item.state) :
  m (LawfulMapReduceSearchContextLocal (κ := κ) sys params globalSeen (· ∈ queue)) :=
  let lctx : LawfulMapReduceSearchContextLocal sys params globalSeen (fun _ => False) :=
    ⟨MapReduceSearchContextLocal.initial completedDepth, MapReduceSearchContextLocalInvariants.initial sys params globalSeen completedDepth⟩
  let res := lctx.processWorkQueue queue processWorkQueue.subproof6 h_inqueue_reachable
  pure res

end LawfulMapReduceSearchContextLocal

@[inline]
def MapReduceSearchContextTemp.mergeOne.innerMerge {numShards : USize}
  (acc : List (MapReduceQueueItem σₕ σ) × ShardedHashSetUSize σₕ numShards) (item : MapReduceQueueItem σₕ σ) :
  List (MapReduceQueueItem σₕ σ) × ShardedHashSetUSize σₕ numShards :=
  let (mq_acc, st_acc) := acc
  if !st_acc.contains item.fingerprint then
    (item :: mq_acc, st_acc.insert item.fingerprint)
  else
    (mq_acc, st_acc)

def MapReduceSearchContextTemp.mergeOne.innerMergeDescription {numShards : USize}
  (acc res : List (MapReduceQueueItem σₕ σ) × ShardedHashSetUSize σₕ numShards) (inQ : MapReduceQueueItem σₕ σ → Prop) : Prop :=
  ∃ pfx, res.1 = pfx ++ acc.1 ∧
    (pfx.map MapReduceQueueItem.fingerprint).Nodup ∧
    (∀ fp, (∃ item, inQ item ∧ item.fingerprint = fp) → fp ∉ acc.2 →
      fp ∈ (pfx.map MapReduceQueueItem.fingerprint)) ∧
    (∀ item ∈ pfx, inQ item ∧ item.fingerprint ∉ acc.2) ∧
    (∀ fp, fp ∈ res.2 ↔ fp ∈ acc.2 ∨ fp ∈ (pfx.map MapReduceQueueItem.fingerprint))

omit [Ord σₕ] in
theorem MapReduceSearchContextTemp.mergeOne.innerMergeDescription.concat
  {numShards : USize} {p q : MapReduceQueueItem σₕ σ → Prop}
  {a1 a2 a3 : List (MapReduceQueueItem σₕ σ) × ShardedHashSetUSize σₕ numShards}
  (h1 : mergeOne.innerMergeDescription a1 a2 p) (h2 : mergeOne.innerMergeDescription a2 a3 q) :
  mergeOne.innerMergeDescription a1 a3 fun x => p x ∨ q x := by
  rcases h1 with ⟨pfx1, h_pfx1, h_nodup1, h_inQ1, h_fps1, h_mem_iff1⟩
  rcases h2 with ⟨pfx2, h_pfx2, h_nodup2, h_inQ2, h_fps2, h_mem_iff2⟩
  exists (pfx2 ++ pfx1) ; grind

omit [Ord σₕ] in
theorem MapReduceSearchContextTemp.mergeOne.innerMerge_foldl_descriptive {numShards : USize}
  (acc : List (MapReduceQueueItem σₕ σ) × ShardedHashSetUSize σₕ numShards) (lq : List (MapReduceQueueItem σₕ σ)) :
  let res := lq.foldl (init := acc) mergeOne.innerMerge
  mergeOne.innerMergeDescription acc res (· ∈ lq) := by
  dsimp only [innerMergeDescription]
  induction lq generalizing acc with
  | nil => exists [] ; simp [List.foldl]
  | cons item lq' ih =>
    dsimp [List.foldl]
    specialize ih (mergeOne.innerMerge acc item)
    revert ih ; fun_cases mergeOne.innerMerge acc item
    · intro ih ; rcases ih with ⟨pfx, h_pfx, h_nodup, h_subseq, h_fps, h_mem_iff⟩
      rename_i mq_acc st_acc hh ; simp at *
      exists (pfx ++ [item]) ; simp ; split_ands <;> try grind
    · intro ih ; rcases ih with ⟨pfx, h_pfx, h_nodup, h_subseq, h_fps, h_mem_iff⟩
      exists pfx ; split_ands <;> grind

omit [Ord σₕ] in
@[inline]
def MapReduceSearchContextTemp.mergeOne {numShards : USize}
  (acc : MapReduceSearchContextTemp σ κ σₕ asm numShards) (lctx : MapReduceSearchContextLocal σ κ σₕ asm) :
  MapReduceSearchContextTemp σ κ σₕ asm numShards :=
  let ⟨mbase, mq, st⟩ := acc
  let (lbase, lq) := lctx
  let (mq', st') := lq.foldl (init := (mq, st)) mergeOne.innerMerge
  ⟨mbase.mergeWithoutDepthChangeNoLog lbase, mq', st'⟩

omit [Ord σₕ] in
theorem MapReduceSearchContextTemp.mergeOne_foldl_descriptive {numShards : USize}
  (acc : MapReduceSearchContextTemp σ κ σₕ asm numShards) (lctxs : List (MapReduceSearchContextLocal σ κ σₕ asm)) :
  let res := lctxs.foldl (init := acc) MapReduceSearchContextTemp.mergeOne
  res.base = (lctxs.map Prod.fst).foldl (init := acc.base) BaseSearchContext.mergeWithoutDepthChangeNoLog ∧
  mergeOne.innerMergeDescription (acc.tovisit, acc.tempSeen) (res.tovisit, res.tempSeen)
    (∃ lctx ∈ lctxs, · ∈ lctx.2) := by
  dsimp only
  induction lctxs generalizing acc with
  | nil =>
    constructor
    · rfl
    · exists [] ; simp [List.foldl]
  | cons lctx lctxs ih =>
    dsimp [List.foldl]
    specialize ih (mergeOne acc lctx) ; rcases ih with ⟨ih1, ih2⟩
    constructor
    · rw [ih1] ; rfl
    · have hh := mergeOne.innerMerge_foldl_descriptive (acc.tovisit, acc.tempSeen) lctx.2
      rewrite (occs := .pos [1, 2]) [mergeOne] at ih2
      set e := lctx.2.foldl mergeOne.innerMerge (acc.tovisit, acc.tempSeen)
      rcases e with ⟨mq_acc, st_acc⟩ ; dsimp at hh ih2
      have htmp := mergeOne.innerMergeDescription.concat hh ih2
      simp only [List.mem_cons, exists_eq_or_imp] ; exact htmp

omit [Ord σₕ] in
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

omit [Ord σₕ] in
theorem BaseSearchContext.mergeWithoutDepthChangeNoLog_foldl_description
  (acc : BaseSearchContext σ κ σₕ asm) (ctxs : List (BaseSearchContext σ κ σₕ asm)) :
  let res := ctxs.foldl (init := acc) BaseSearchContext.mergeWithoutDepthChangeNoLog
  res.finished = acc.finished.or ((ctxs.find? (·.hasFinished)).bind (fun x => x.finished)) := by
  dsimp only
  induction ctxs generalizing acc with
  | nil => simp [List.foldl]
  | cons ctx ctxs ih =>
    dsimp [List.foldl, List.find?, BaseSearchContext.hasFinished]
    rw [ih] ; clear ih
    unfold mergeWithoutDepthChangeNoLog ; dsimp
    rcases acc.finished with _ | _
    on_goal 2=> rfl
    dsimp ; rcases h : ctx.finished with _ | _
    on_goal 2=> grind
    dsimp ; rfl

def MapReduceSearchContextMain.mergeWithLocalOnes
  {params : SearchParameters ρ σ} {th : ρ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th}
  (mctx : MapReduceSearchContextMain σ κ σₕ asm)
  {splitLists : List (List (MapReduceQueueItem σₕ σ))}
  {globalSeen : ShardedTreeSetUSize σₕ}
  (lctxs : IteratedProd (splitLists.map fun a => LawfulMapReduceSearchContextLocal (κ := κ) sys params globalSeen (· ∈ a))) :
  MapReduceSearchContextMain σ κ σₕ asm :=
  let ⟨ctx, len, q, globalSeen, accLogs⟩ := mctx
  let ⟨mbase, mq, st⟩ := IteratedProd.foldl (β := MapReduceSearchContextTemp σ κ σₕ asm globalSeen.numShards) (elements := lctxs)
    (init := ⟨ctx, q, ShardedHashSetUSize.emptyUSize globalSeen.numShards globalSeen.h_numShards_pos⟩)
      fun acc lctx => acc.mergeOne lctx.val
  -- Collect local logs from this round as one entry (O(1) cons, deferred merging)
  let newLogs := IteratedProd.foldl (β := List _) (elements := lctxs) (init := [])
    fun acc lctx => lctx.val.1.log :: acc
  ⟨mbase, len + st.size, mq, globalSeen.insertManyFastSHS st, newLogs :: accLogs⟩

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

attribute [local simp] ShardedTreeSetUSize.mem_insertManyFastSHS in
theorem MapReduceSearchContextMain.mergeWithLocalOnes_preserves_invs
  [Std.TransOrd σₕ] [Std.LawfulBEqOrd σₕ]
  {params : SearchParameters ρ σ} {th : ρ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th}
  {mctx : MapReduceSearchContextMain σ κ σₕ asm}
  (h_not_finished : mctx.base.hasFinished = false)
  (h_mctx : MapReduceSearchContextMainInvariants sys params mctx)
  {numSplits chunkSize numLarge : Nat}
  (lctxs :
    let splitLists := ListSplit.splitList numSplits chunkSize numLarge mctx.tovisit
    IteratedProd (splitLists.map fun a => LawfulMapReduceSearchContextLocal (κ := κ) sys params mctx.globalSeen (· ∈ a))) :
  let mctx' := MapReduceSearchContextMain.mergeWithLocalOnes
    ⟨{ mctx.base with completedDepth := mctx.base.currentFrontierDepth, currentFrontierDepth := mctx.base.currentFrontierDepth + 1 }, 0, [], mctx.globalSeen, mctx.accumulatedLogs⟩ lctxs
  MapReduceSearchContextMainInvariants sys params mctx' := by
  rcases mctx with ⟨ctx, mlen_orig, tovisit, gs, accLogs⟩
  let ctx' := { ctx with completedDepth := ctx.currentFrontierDepth, currentFrontierDepth := ctx.currentFrontierDepth + 1 }
  dsimp ; unfold mergeWithLocalOnes
  simp only [IteratedProd.subtypesToList_foldl_eq_list_foldl]
  have h_local_invs := IteratedProd.externalize_proofs lctxs ; dsimp at h_local_invs
  rcases h_local_invs with ⟨h_length_eq, h_local_invs⟩
  generalize IteratedProd.subtypesToList lctxs = lctxs' at *
  set merged := lctxs'.foldl _ _ with heq
  have htmp2 := ({ base := ctx', tovisit := [], tempSeen := ShardedHashSetUSize.emptyUSize gs.numShards gs.h_numShards_pos : MapReduceSearchContextTemp σ κ σₕ asm gs.numShards }).mergeOne_foldl_descriptive lctxs'
  dsimp at htmp2 ; rw [← heq] at htmp2 ; rcases htmp2 with ⟨h_base, h_merge_desc⟩
  have h_base_desc := BaseSearchContext.mergeWithoutDepthChangeNoLog_foldl_description ctx' (lctxs'.map Prod.fst)
  simp [BaseSearchContext.hasFinished] at h_not_finished
  dsimp at h_base_desc ; rw [← h_base, h_not_finished] at h_base_desc ; dsimp at h_base_desc
  clear heq h_base ; clear_value merged

  rcases merged with ⟨mbase, mq, st⟩
  rcases h_merge_desc with ⟨pfx, h_pfx, h_nodup, h_in_pfx, h_inQ, h_fps⟩
  dsimp only at * ; subst mq
  simp at h_inQ h_fps h_in_pfx ; simp at h_local_invs

  rcases h_mctx with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed, h_orig_len⟩
  whnf at h_closed ; dsimp only at *
  clear h_q_emp

  -- prove a lemma first, since it will be used in both `terminate_empty_queue` and `stable_closed`
  have h_not_explored_all : mbase.finished ≠ Option.some (TerminationReason.exploredAllReachableStates) := by
    intro h ; rw [h_base_desc, Option.bind_eq_some_iff] at h ; simp +unfoldPartialApp [Function.comp] at h
    rcases h with ⟨lbctx, ⟨⟨lq, h_find⟩, h_finished⟩⟩
    -- deriving false here
    rw [List.find?_eq_some_iff_getElem] at h_find
    rcases h_find with ⟨_, i, h_i, h_getElem, _⟩
    -- NOTE: This is repeating
    have h_in_zip := List.zip_mem (by apply Nat.le_of_eq ; symm ; apply h_length_eq) (by rw [← h_length_eq] ; apply h_i)
    rw [h_getElem] at h_in_zip
    specialize h_local_invs _ _ _ h_in_zip
    have := h_local_invs.not_explored_all ; grind

  constructor ; on_goal 1=> constructor
  · simp
    intro fpSt curr hh
    specialize h_inQ _ hh
    rcases h_inQ with ⟨lbctx, lq, h_in_lctxs', h_in_q⟩
    -- This is annoying ...
    rw [List.mem_iff_getElem] at h_in_lctxs'
    rcases h_in_lctxs' with ⟨i, h_i, h_getElem⟩
    have h_in_zip := List.zip_mem (by apply Nat.le_of_eq ; symm ; apply h_length_eq) (by rw [← h_length_eq] ; apply h_i)
    rw [h_getElem] at h_in_zip
    specialize h_local_invs _ _ _ h_in_zip
    rcases h_local_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_not_explored_all, h_dj, h_same_dom, h_succ_coll⟩ ; dsimp only at *
    grind
  · simp
    intro hinj x hh ; rcases hh with hh | hh
    · grind
    · rw [h_fps] at hh ; rcases hh with ⟨⟨fpSt, curr⟩, hh, heq⟩ ; dsimp at heq ; subst fpSt
      -- NOTE: This is repeating
      specialize h_inQ _ hh
      rcases h_inQ with ⟨lbctx, lq, h_in_lctxs', h_in_q⟩
      rw [List.mem_iff_getElem] at h_in_lctxs'
      rcases h_in_lctxs' with ⟨i, h_i, h_getElem⟩
      have h_in_zip := List.zip_mem (by apply Nat.le_of_eq ; symm ; apply h_length_eq) (by rw [← h_length_eq] ; apply h_i)
      rw [h_getElem] at h_in_zip
      specialize h_local_invs _ _ _ h_in_zip
      rcases h_local_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_not_explored_all, h_dj, h_same_dom, h_succ_coll⟩ ; dsimp only at *
      grind
  · simp ; grind
  · simp ; grind
  · whnf ; simp
    intro hinj hor u hh h_not_in_pfx
    rcases hor with _ | h_not_finished_mbase
    on_goal 1=> grind
    rcases hh with hh | hh
    · by_cases h_in_tovisit? : (∀ item ∈ tovisit, item.fingerprint ≠ StateView.view u)
      · grind  -- easy case
      · clear h_closed
        simp at h_in_tovisit? ; rcases h_in_tovisit? with ⟨⟨fpSt, curr⟩, h_in_tovisit, heq⟩
        dsimp at heq ; subst fpSt
        have := hinj (h_q_sound _ _ h_in_tovisit |>.right.right) ; subst curr -- unify `curr` with `u`
        -- here, need the split covering theorem
        obtain ⟨chunk, h_chunk_in, h_in_chunk⟩ := ListSplit.splitList_mem numSplits chunkSize numLarge tovisit ⟨fp.view u, u⟩ h_in_tovisit
        rw [List.mem_iff_getElem] at h_chunk_in
        rcases h_chunk_in with ⟨j, h_j, h_getElem_chunk⟩
        have h_in_zip := List.zip_mem (by apply Nat.le_of_eq ; symm ; apply h_length_eq) (by exact h_j)
        simp [h_getElem_chunk] at h_in_zip
        specialize h_local_invs _ _ _ h_in_zip ; simp at h_local_invs
        -- show that no `lctx` has finished
        rw [h_base_desc] at h_not_finished_mbase
        revert h_not_finished_mbase ; rcases heq : List.find? _ _ with _ | lctx
        on_goal 2=>
          dsimp ; intro heq' ; rw [List.find?_eq_some_iff_getElem, BaseSearchContext.hasFinished] at heq ; grind
        intro _ ; simp at heq
        -- NOTE: Here Lean has some trouble proving the index validity of `j` from the scratch, so use some trick
        set e := getElem lctxs' j _
        specialize heq e.1 e.2 (by simp [e]) ; simp [BaseSearchContext.hasFinished] at heq
        rcases h_local_invs with ⟨_, _, h_dj, h_same_dom, h_succ_coll⟩
        specialize h_succ_coll heq (fp.view u) u (h_getElem_chunk ▸ h_in_chunk)
        grind
    · grind
  · simp
    -- use the disjointness
    rw [ShardedHashSetUSize.length_toList, ← List.length_map MapReduceQueueItem.fingerprint]
    apply List.Perm.length_eq ; rw [List.perm_ext_iff_of_nodup]
    · simp [ShardedHashSetUSize.toList]
      simp [ShardedHashSetUSize.mem_iff_exists_shard] at h_fps
      exact h_fps
    · apply ShardedHashSetUSize.nodup_elements
    · exact h_nodup

omit [ActionStatUpdate κ asm] in
private theorem breadthFirstSearchParallel.subproof1 {ρ σₕ σ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th}
  {seen : σₕ → Prop}
  {tovisit : List (MapReduceQueueItem σₕ σ)}
  (h : ∀ x st, ⟨x, st⟩ ∈ tovisit → sys.reachable st ∧ seen x ∧ x = fp.view st)
  (splitLists : List (List (MapReduceQueueItem σₕ σ)))
  (h_mem_inv : ∀ item, (∃ l ∈ splitLists, item ∈ l) → item ∈ tovisit) :
  ∀ sublist ∈ splitLists,
    ∀ item ∈ sublist, sys.reachable item.state := by
  intro sublist h_sublist_in item h_item_in
  have : (⟨item.fingerprint, item.state⟩ : MapReduceQueueItem σₕ σ) = item := rfl
  exact (h item.fingerprint item.state (this ▸ h_mem_inv _ ⟨sublist, h_sublist_in, h_item_in⟩)).1

private theorem not_too_small_not_too_large (n : Nat) :
  let t := max 1 (min n 4294967295)
  0 < USize.ofNat t ∧ t < USize.size := by
  apply (fun (p : _ → _) q => And.intro (p q) q)
  · intro h ; simp [USize.lt_ofNat_iff h]
  · cases USize.size_eq <;> rename_i h <;> rw [h] <;> omega

def breadthFirstSearchParallel {m : Type → Type}
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [Std.TransOrd σₕ] [Std.LawfulBEqOrd σₕ]
  (params : SearchParameters ρ σ)
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (parallelCfg : ParallelConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken) :
  m (MapReduceSearchContextMain σ κ σₕ asm) := do
  let numShards := max 1 <| min parallelCfg.numSubTasks 4294967295
  have ⟨h_pos, h_small⟩ := not_too_small_not_too_large parallelCfg.numSubTasks
  let mut mctx : LawfulMapReduceSearchContextMain (fp := fp) sys params :=
    Subtype.mk (MapReduceSearchContextMain.initial sys.initStates numShards h_pos h_small)
      (MapReduceSearchContextMainInvariants.initial sys params numShards)
  let mut lastUpdateTime : Nat := 0
  let mut cancelled := false
  while h_not_finished : mctx.val.base.hasFinished = false do
    match mctx with
    | ⟨⟨base, tovisitLen, tovisit, globalSeen, accLogs⟩, h_mctx⟩ =>
      -- Check if the frontier is empty
      if h_empty : tovisit.isEmpty then
        mctx := Subtype.mk ⟨{ base with finished := some (.exploredAllReachableStates) }, tovisitLen, tovisit, globalSeen, accLogs⟩
          (h_mctx.setExploredAll_preserves_invs h_not_finished h_empty)
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
            (breadthFirstSearchParallel.subproof1 h_mctx.queue_sound splitLists
              (fun item hm => (ListSplit.splitList_mem_iff numSplits chunkSize numLarge tovisit item).mp hm) _ h_sublist_in)
        let results ← IteratedProd.mapM
          (T₂ := (fun a => LawfulMapReduceSearchContextLocal sys params globalSeen (· ∈ a)))
          (fun task => IO.ofExcept task.get) tasks
        -- CHECK Ideally, `tovisit` should not be involved in any computational part from this point on
        -- Reduce step
        let mctxValForMerge : MapReduceSearchContextMain σ κ σₕ asm :=
          { base := { base with completedDepth := base.currentFrontierDepth, currentFrontierDepth := base.currentFrontierDepth + 1 } , tovisitLen := 0, tovisit := [], globalSeen := globalSeen, accumulatedLogs := accLogs }
        let mctxVal' := mctxValForMerge.mergeWithLocalOnes results
        have h_mctx' : MapReduceSearchContextMainInvariants sys params mctxVal' :=
          MapReduceSearchContextMain.mergeWithLocalOnes_preserves_invs h_not_finished h_mctx results
        match heq : mctxVal' with
        | ⟨base', tovisitLen', tovisit', globalSeen', accLogs'⟩ =>
          trySetViolationFound progressInstanceId base'
          -- Update progress on every diameter change
          updateProgressDuringBFS progressInstanceId base' tovisitLen' globalSeen'.size
          -- Prove invariants are preserved using local invariants from `lawfulResults`
          mctx := Subtype.mk ⟨base', tovisitLen', tovisit', globalSeen', accLogs'⟩ (heq.symm ▸ h_mctx')
          -- Check for cancellation/handoff at most once per second
          let newtime? ← checkCancellationWithoutPeriodicUpdate progressInstanceId lastUpdateTime 1000 cancelToken
          match newtime? with
          | .updateTime t => lastUpdateTime := t
          | .searchCancelled => cancelled := true ; break
          | .noUpdate => pure ()
  -- Final update to ensure stats reflect finished state
  let ⟨mctxVal, _⟩ := mctx
  let mctxVal := { mctxVal with base := { mctxVal.base with currentFrontierDepth := mctxVal.base.completedDepth } }
  updateProgressDuringBFS progressInstanceId mctxVal.base mctxVal.tovisitLen mctxVal.globalSeen.size
  -- Merge accumulated logs only if violations were found (needed for recoverTrace)
  let needsLog := !mctxVal.base.violatingStates.isEmpty ||
    (match mctxVal.base.finished with
     | some (.earlyTermination (.foundViolatingState ..)) => true
     | some (.earlyTermination (.deadlockOccurred ..)) => true
     | some (.earlyTermination (.assertionFailed ..)) => true
     | _ => false)
  let mctxVal := if needsLog then
    { mctxVal with base := { mctxVal.base with
        log := (mctxVal.accumulatedLogs.flatten).foldl (fun acc m => acc.union m) mctxVal.base.log } }
  else mctxVal
  if cancelled then
    return { mctxVal with base := { mctxVal.base with finished := some (.earlyTermination .cancelled) } }
  else
    return mctxVal

end Veil.ModelChecker.Concrete
