module

public import Veil.Core.Tools.ModelChecker.Concrete.SequentialLemmas

public section
namespace Veil.ModelChecker.Concrete

variable {ρ σ κ σₕ asm : Type} [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm]
  {Shard : Type} [Membership σₕ Shard] {th : ρ}

@[expose] def MapReduceSearchContextMain.initial [SetShard σₕ Shard] (initStates : List σ) (numShards : Nat)
  (h_pos : 0 < USize.ofNat numShards := by native_decide)
  (h_small : numShards < USize.size := by native_decide) : MapReduceSearchContextMain σ κ σₕ asm Shard :=
  let fps := initStates.map fp.view
  let tovisit := fps.zipWith (fun fp s => ⟨fp, s⟩) initStates
  { base := BaseSearchContext.initial initStates,
    tovisitLen := tovisit.length,
    tovisit := tovisit,
    globalSeen := ShardedSetUSize.ofListByHash fps numShards h_pos h_small }

/-- Create an empty local context with the given `completedDepth`. -/
@[expose] def MapReduceSearchContextLocal.initial (completedDepth : Nat) : MapReduceSearchContextLocal σ κ σₕ asm :=
  ({ log := Std.HashMap.emptyWithCapacity,
     violatingStates := [],
     finished := none,
     completedDepth := completedDepth,
     currentFrontierDepth := completedDepth + 1,
     statesFound := 0,
     actionStatsMap := ActionStatUpdate.empty (κ := κ) }, [])

theorem MapReduceSearchContextMainInvariants.initial [SetShard σₕ Shard]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (params : SearchParameters ρ σ) (numShards : Nat) {h_pos} {h_small} :
  MapReduceSearchContextMainInvariants sys params (MapReduceSearchContextMain.initial (fp := fp) (Shard := Shard) sys.initStates numShards h_pos h_small) := by
  simp [MapReduceSearchContextMain.initial, BaseSearchContext.initial]
  constructor ; on_goal 1=> constructor
  all_goals simp [MapReduceSearchContextMain.isStableClosed,
    ← List.map_uncurry_zip_eq_zipWith, ← List.map_prod_right_eq_zip, ShardedSetUSize.mem_ofListByHash] ; (try solve | intros ; grind)

theorem MapReduceSearchContextLocalInvariants.initial
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (params : SearchParameters ρ σ)
  (globalSeen : ShardedSetUSize σₕ Shard) (completedDepth : Nat) :
  MapReduceSearchContextLocalInvariants sys params globalSeen (fun _ => False)
    (MapReduceSearchContextLocal.initial (fp := fp) completedDepth) := by
  simp [MapReduceSearchContextLocal.initial]
  constructor ; on_goal 1=> constructor
  all_goals (try solve | intros ; grind)

variable {params : SearchParameters ρ σ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}

theorem MapReduceSearchContextMainInvariants.setExploredAll_preserves_invs
  {mctx : MapReduceSearchContextMain σ κ σₕ asm Shard}
  (h_not_finished : mctx.base.hasFinished = false)
  (h_empty : mctx.tovisit.isEmpty)
  (mctx_invs : MapReduceSearchContextMainInvariants sys params mctx) :
  MapReduceSearchContextMainInvariants sys params
    { mctx with base := { mctx.base with finished := some (.exploredAllReachableStates) } } := by
  rcases mctx with ⟨ctx, mlen, q, gs⟩ ; rcases mctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed, h_len⟩ ; dsimp only at *
  simp [BaseSearchContext.hasFinished] at h_not_finished
  constructor ; on_goal 1=> constructor
  all_goals (try dsimp only) ; try solve | assumption | grind

theorem MapReduceSearchContextMainInvariants.bfs_completeness
  {mctx : MapReduceSearchContextMain σ κ σₕ asm Shard}
  (mctx_invs : MapReduceSearchContextMainInvariants sys params mctx)
  (h_explore_all : mctx.base.finished = some (.exploredAllReachableStates))
  (h_view_inj : Function.Injective fp.view) :
  ∀ s : σ, sys.reachable s → (fp.view s) ∈ mctx.globalSeen := by
  rcases mctx with ⟨ctx, mlen, q, gs⟩ ; rcases mctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed, h_len⟩ ; dsimp only at *
  intro s h_reachable
  induction h_reachable <;> grind

theorem MapReduceSearchContextLocalInvariants.finished_change_visited_pred_in_invs
  {globalSeen : ShardedSetUSize σₕ Shard}
  {p q : MapReduceQueueItem σₕ σ → Prop}
  {lctx : MapReduceSearchContextLocal σ κ σₕ asm}
  (h_finished : lctx.1.hasFinished = true)
  (lctx_invs : MapReduceSearchContextLocalInvariants sys params globalSeen p lctx) :
  MapReduceSearchContextLocalInvariants sys params globalSeen q lctx := by
  rcases lctx with ⟨ctx, q⟩ ; rcases lctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_not_explored_all, h_dj, h_same_dom, h_succ_coll⟩ ; dsimp only at *
  simp [BaseSearchContext.hasFinished] at h_finished
  constructor ; on_goal 1=> constructor
  all_goals dsimp only ; try solve | assumption | grind

theorem MapReduceSearchContextLocalInvariants.progress_by_one_state
  {globalSeen : ShardedSetUSize σₕ Shard}
  {p q : MapReduceQueueItem σₕ σ → Prop}
  {lctx : MapReduceSearchContextLocal σ κ σₕ asm}
  (lctx_invs : MapReduceSearchContextLocalInvariants sys params globalSeen p lctx)
  (h : ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th curr → ((fp.view v) ∈ globalSeen ∨ (fp.view v) ∈ lctx.1.log))
  (hpq : ∀ item, q item ↔ p item ∨ item = ⟨fpSt, curr⟩) :
  MapReduceSearchContextLocalInvariants sys params globalSeen q lctx := by
  rcases lctx with ⟨ctx, q⟩ ; rcases lctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_not_explored_all, h_dj, h_same_dom, h_succ_coll⟩ ; dsimp only at *
  constructor ; on_goal 1=> constructor
  all_goals dsimp only ; try solve | assumption | grind

end Veil.ModelChecker.Concrete
