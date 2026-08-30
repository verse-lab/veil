import Veil.Core.Tools.ModelChecker.Concrete.SearchContext

namespace Veil.ModelChecker.Concrete

variable {ρ σ κ σₕ asm : Type}
  [fp : StateFingerprint σ σₕ]
  [ActionStatUpdate κ asm]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Veil.ExId0 κ (List (κ × ExecutionOutcome Veil.ExId0 σ)) th)
  (params : SearchParameters ρ σ)

def SequentialSearchContext.initial : SequentialSearchContext σ κ σₕ asm :=
  let iss := sys.initStates
  (BaseSearchContext.initial iss, fQueue.ofList (iss.map (fun s => ⟨fp.view s, s, 0⟩)))

theorem SequentialSearchContextInvariants.initial :
  SequentialSearchContextInvariants sys params .none (SequentialSearchContext.initial (fp := fp) sys) := by
  constructor ; on_goal 1=> constructor
  all_goals simp [SequentialSearchContext.isStableClosed, SequentialSearchContext.initial, BaseSearchContext.initial, ← fQueue.mem_ofList] ; (try solve | intros ; grind)

/-- When finishing processing a state, we move from having that state `curr`
in transit to having no state in transit, provided that all successfully
reachable neighbors of `curr` in transit have been seen. -/
theorem SequentialSearchContextInvariants.finish_stateInTransit
  {sctx : SequentialSearchContext σ κ σₕ asm}
  {curr : σ}
  (sctx_invs : SequentialSearchContextInvariants sys params (.some curr) sctx)
  (h_neighbors_seen : ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th curr →
    (fp.view v) ∈ sctx.1.log) :
  SequentialSearchContextInvariants sys params .none sctx := by
  rcases sctx with ⟨ctx, sq⟩ ; rcases sctx_invs with ⟨h1, h2, h3, h_closed⟩ ; dsimp only at *
  constructor <;> try assumption
  simp [SequentialSearchContext.isStableClosed] at h_closed ⊢
  intro ha hb u hc hd l v hin
  by_cases heq : curr = u
  on_goal 2=> grind
  subst u ; eapply h_neighbors_seen ; assumption

theorem SequentialSearchContext.bfs_completeness
  {sctx : SequentialSearchContext σ κ σₕ asm}
  (sctx_invs : SequentialSearchContextInvariants sys params .none sctx)
  (h_explore_all : sctx.1.finished = some (.exploredAllReachableStates))
  (h_view_inj : Function.Injective fp.view) :
  ∀ s : σ, sys.reachable s → (fp.view s) ∈ sctx.1.log := by
  rcases sctx with ⟨ctx, sq⟩ ; rcases sctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed⟩ ; dsimp only at *
  intro s h_reachable
  induction h_reachable with
  | init s h_s_in_initStates => grind   -- using the initial seen set
  | step u v h_u_reach h_transition ih =>
    -- The key is to apply `stable_closed`, but `grind` is too powerful
    simp [fQueue.not_mem_iff_isEmpty] at h_q_emp ; grind

end Veil.ModelChecker.Concrete
