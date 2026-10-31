module

public import Veil.Core.Tools.ModelChecker.Concrete.SequentialLemmas

public section
namespace Veil.ModelChecker.Concrete

variable {ρ σ κ σₕ : Type} {T : Type → Type} [fp : StateFingerprint σ σₕ] [LabelTable κ T]
  {Shard : Type} [Membership σₕ Shard] {numShards : PosUSize} {th : ρ}

/-- Create an empty local context with the given `completedDepth`. -/
@[expose] def MapReduceSearchContextLocal.initial (completedDepth : Nat) : MapReduceSearchContextLocal σ κ σₕ T :=
  ⟨{ violatingStates := [],
     finished := none,
     currentFrontierDepth := completedDepth + 1,
     statesFound := 0 }, LabelTable.replicate (κ := κ) 0, Std.HashSet.emptyWithCapacity, []⟩

theorem MapReduceSearchContextLocalInvariants.initial
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (params : SearchParameters ρ σ)
  (globalSeen : MapReduceGlobalSeen σₕ κ Shard numShards) (completedDepth : Nat) :
  MapReduceSearchContextLocalInvariants sys params globalSeen (fun _ => False)
    (MapReduceSearchContextLocal.initial (fp := fp) completedDepth) := by
  simp [MapReduceSearchContextLocal.initial]
  constructor ; on_goal 1=> constructor
  all_goals (try solve | intros ; grind)

theorem MapReduceSearchContextLocal.LogSound.initial
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (params : SearchParameters ρ σ) (completedDepth : Nat) (rep : σₕ → Option σ) :
  (MapReduceSearchContextLocal.initial (fp := fp) (κ := κ) (T := T) completedDepth).LogSound sys params rep := by
  constructor ; on_goal 1=> constructor
  all_goals simp [MapReduceSearchContextLocal.initial, TerminationSound]

variable {params : SearchParameters ρ σ}
  {sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th}

theorem MapReduceSearchContextMainInvariants.setExploredAll_preserves_invs
  {mctx : MapReduceSearchContextMain σ κ σₕ T Shard numShards}
  (h_not_finished : mctx.base.hasFinished = false)
  (h_empty : mctx.tovisit.isEmpty)
  (mctx_invs : MapReduceSearchContextMainInvariants sys params mctx) :
  MapReduceSearchContextMainInvariants sys params
    { mctx with base := { mctx.base with finished := some (.exploredAllReachableStates) } } := by
  rcases mctx with ⟨ctx, gen, dist, mlen, q, gs⟩ ; rcases mctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed, h_len⟩ ; dsimp only at *
  simp [BaseSearchContext.hasFinished] at h_not_finished
  constructor ; on_goal 1=> constructor
  all_goals (try dsimp only) ; try solve | assumption | grind

theorem MapReduceSearchContextMainInvariants.setCancelled
  {mctx : MapReduceSearchContextMain σ κ σₕ T Shard numShards}
  (mctx_invs : MapReduceSearchContextMainInvariants sys params mctx) :
  MapReduceSearchContextMainInvariants sys params
    { mctx with base := { mctx.base with finished := some (.earlyTermination .cancelled) } } := by
  rcases mctx with ⟨ctx, gen, dist, mlen, q, gs⟩ ; rcases mctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed, h_len⟩ ; dsimp only at *
  constructor ; on_goal 1=> constructor
  all_goals (try dsimp only) ; try solve | assumption | grind

theorem MapReduceSearchContextMain.LogSound.setExploredAll [MapShard σₕ (LogEntry σₕ κ) Shard]
  {mctx : MapReduceSearchContextMain σ κ σₕ T Shard numShards} {rep : σₕ → Option σ} {dep : σₕ → Nat}
  (h : mctx.LogSound sys params rep dep) :
  MapReduceSearchContextMain.LogSound sys params
    { mctx with base := { mctx.base with finished := some (.exploredAllReachableStates) } } rep dep := by
  rcases h with ⟨⟨hv, _⟩, hlog, hq⟩ ; exact ⟨⟨hv, by simp [TerminationSound]⟩, hlog, hq⟩

theorem MapReduceSearchContextMain.LogSound.setCancelled [MapShard σₕ (LogEntry σₕ κ) Shard]
  {mctx : MapReduceSearchContextMain σ κ σₕ T Shard numShards} {rep : σₕ → Option σ} {dep : σₕ → Nat}
  (h : mctx.LogSound sys params rep dep) :
  MapReduceSearchContextMain.LogSound sys params
    { mctx with base := { mctx.base with finished := some (.earlyTermination .cancelled) } } rep dep := by
  rcases h with ⟨⟨hv, _⟩, hlog, hq⟩ ; exact ⟨⟨hv, by simp [TerminationSound]⟩, hlog, hq⟩

theorem MapReduceSearchContextMainInvariants.bfs_completeness
  {mctx : MapReduceSearchContextMain σ κ σₕ T Shard numShards}
  (mctx_invs : MapReduceSearchContextMainInvariants sys params mctx)
  (h_explore_all : mctx.base.finished = some (.exploredAllReachableStates))
  (h_view_inj : Function.InjectiveOn fp.view sys.reachable) :
  ∀ s : σ, sys.reachable s → (fp.view s) ∈ mctx.globalSeen := by
  rcases mctx with ⟨ctx, gen, dist, mlen, q, gs⟩ ; rcases mctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed, h_len⟩ ; dsimp only at *
  intro s h_reachable
  induction h_reachable <;> grind

theorem MapReduceSearchContextLocalInvariants.finished_change_visited_pred_in_invs
  {globalSeen : MapReduceGlobalSeen σₕ κ Shard numShards}
  {p q : MapReduceQueueItem σₕ σ κ → Prop}
  {lctx : MapReduceSearchContextLocal σ κ σₕ T}
  (h_finished : lctx.base.hasFinished = true)
  (lctx_invs : MapReduceSearchContextLocalInvariants sys params globalSeen p lctx) :
  MapReduceSearchContextLocalInvariants sys params globalSeen q lctx := by
  rcases lctx with ⟨ctx, gen, seen, q⟩ ; rcases lctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_not_explored_all, h_dj, h_same_dom, h_succ_coll⟩ ; dsimp only at *
  simp [BaseSearchContext.hasFinished] at h_finished
  constructor ; on_goal 1=> constructor
  all_goals dsimp only ; try solve | assumption | grind

theorem MapReduceSearchContextLocalInvariants.progress_by_one_state
  {globalSeen : MapReduceGlobalSeen σₕ κ Shard numShards}
  {p q : MapReduceQueueItem σₕ σ κ → Prop}
  {lctx : MapReduceSearchContextLocal σ κ σₕ T} {e : LogEntry σₕ κ}
  (lctx_invs : MapReduceSearchContextLocalInvariants sys params globalSeen p lctx)
  (h : ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th curr → ((fp.view v) ∈ globalSeen ∨ (fp.view v) ∈ lctx.seen))
  (hpq : ∀ item, q item ↔ p item ∨ item = ⟨fpSt, curr, e⟩) :
  MapReduceSearchContextLocalInvariants sys params globalSeen q lctx := by
  rcases lctx with ⟨ctx, gen, seen, q⟩ ; rcases lctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_not_explored_all, h_dj, h_same_dom, h_succ_coll⟩ ; dsimp only at *
  constructor ; on_goal 1=> constructor
  all_goals dsimp only ; try solve | assumption | grind

end Veil.ModelChecker.Concrete
