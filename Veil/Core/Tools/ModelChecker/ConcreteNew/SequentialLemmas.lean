import Veil.Core.Tools.ModelChecker.ConcreteNew.SearchContext

namespace Veil.ModelChecker.Concrete

variable {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)

def SequentialSearchContext.initial : SequentialSearchContext σ κ σₕ :=
  (BaseSearchContext.initial sys.initStates, fQueue.ofList (sys.initStates.map (fun s => ⟨fp.view s, s, 0⟩)))

theorem SequentialSearchContextInvariants.initial :
  SequentialSearchContextInvariants sys params .none (SequentialSearchContext.initial (fp := fp) sys) := by
  constructor ; on_goal 1=> constructor
  all_goals simp [SequentialSearchContext.isStableClosed, SequentialSearchContext.initial, BaseSearchContext.initial, ← fQueue.mem_ofList] ; (try solve | intros ; grind)
  · intro hinj s s' hinit h ; have := hinj h ; grind
  · intro hinj s s' hinit h ; have := hinj h ; grind

theorem SequentialSearchContext.bfs_completeness
  {sctx : SequentialSearchContext σ κ σₕ}
  (sctx_invs : SequentialSearchContextInvariants sys params .none sctx)
  (h_explore_all : sctx.1.finished = some (.exploredAllReachableStates))
  (h_view_inj : Function.Injective fp.view) :
  ∀ s : σ, sys.reachable s → (fp.view s) ∈ sctx.1.seen := by
  rcases sctx with ⟨ctx, sq⟩ ; rcases sctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed⟩ ; dsimp only at *
  intro s h_reachable
  induction h_reachable with
  | init s h_s_in_initStates => grind   -- using the initial seen set
  | step u v h_u_reach h_transition ih =>
    -- The key is to apply `stable_closed`, but `grind` is too powerful
    simp [fQueue.not_mem_iff_isEmpty] at h_q_emp ; grind

end Veil.ModelChecker.Concrete
