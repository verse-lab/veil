module

public import Veil.Core.Tools.ModelChecker.Concrete.SearchContext

public section

namespace Veil.ModelChecker.Concrete

variable {ρ σ κ σₕ asm : Type}
  [fp : StateFingerprint σ σₕ]
  [ActionStatUpdate κ asm]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (params : SearchParameters ρ σ)

/-- Sequential initialization keeps the initial-state indices only in the log. -/
@[expose] def SequentialSearchContext.initial : SequentialSearchContext σ κ σₕ asm :=
  let (reps, log) := initialLogAndRepresentatives (κ := κ) sys.initStates
  ⟨BaseSearchContext.initial sys.initStates.length, log, fQueue.ofList (reps.map fun s => ⟨fp.view s, s, 0⟩)⟩

theorem SequentialSearchContext.initial_invs :
  SequentialSearchContextInvariants sys params .none (SequentialSearchContext.initial (fp := fp) sys) ∧
    ∃ rep dep, (SequentialSearchContext.initial (fp := fp) sys).LogSound sys params rep dep := by
  unfold SequentialSearchContext.initial BaseSearchContext.initial
  have h := initialLogAndRepresentatives_description (κ := κ) (fp := fp) sys.initStates
  generalize (initialLogAndRepresentatives (κ := κ) (fp := fp) sys.initStates) = res at h ⊢
  rcases h with ⟨reps, h0, h1, h2, h3, h4⟩ ; rcases res with ⟨states, log⟩
  dsimp only at * ; subst h0 ; simp only [List.map_map] ; simp at h3 h4
  constructor ; on_goal 1=> constructor ; on_goal 1=> constructor
  -- CHECK Hoist the use of `[Std.HashMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]` to `initialLogAndRepresentatives_description`?
  all_goals (try simp [SequentialSearchContext.isStableClosed, ← fQueue.mem_ofList]) ; (try solve | intros ; grind)
  · intros ; subst_vars ; simp
    rename_i hh ; obtain ⟨h31, h32⟩ := h3 _ _ hh ; constructor ; grind
    simp only [Std.HashMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists, h4]
    grind
  · grind [Std.HashMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]
  · intros s hin ; simp only [Std.HashMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists, h4]
    simp at h2
    specialize h2 _ hin ; aesop
  · simp only [Std.HashMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists, h4]
    grind
  · let rep (a : σₕ) := (log[a]?).bind fun
      | .init j => sys.initStates[j]?
      | .step .. => none
    exists rep, fun _ => 0 ; dsimp [rep]
    constructor ; on_goal 1=> constructor
    all_goals (try simp [← fQueue.mem_ofList, Option.bind_eq_some_iff]) ; try grind
    · intros ; subst_vars ; simp [h4] ; grind
    · constructor

theorem SequentialSearchContextInvariants.setCancelled
  {ctx : BaseSearchContext σ κ σₕ asm} {log : Std.HashMap σₕ (LogEntry σₕ κ)} {sq : fQueue (QueueItem σₕ σ)}
  (h : SequentialSearchContextInvariants sys params .none ⟨ctx, log, sq⟩) :
  SequentialSearchContextInvariants sys params .none ⟨{ ctx with finished := some (.earlyTermination .cancelled) }, log, sq⟩ := by
  rcases h with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed⟩
  constructor ; on_goal 1 => constructor
  all_goals dsimp only at * ; try solve | assumption | grind

theorem SequentialSearchContext.LogSound.setCancelled
  {ctx : BaseSearchContext σ κ σₕ asm} {log : Std.HashMap σₕ (LogEntry σₕ κ)} {sq : fQueue (QueueItem σₕ σ)}
  {rep : σₕ → Option σ} {dep : σₕ → Nat}
  (h : SequentialSearchContext.LogSound sys params ⟨ctx, log, sq⟩ rep dep) :
  SequentialSearchContext.LogSound sys params ⟨{ ctx with finished := some (.earlyTermination .cancelled) }, log, sq⟩ rep dep := by
  rcases h with ⟨h1, h2, h3, _⟩ ; exact ⟨h1, h2, h3, by simp [TerminationSound]⟩

/-- When finishing processing a state, we move from having that state `curr`
in transit to having no state in transit, provided that all successfully
reachable neighbors of `curr` in transit have been seen. -/
theorem SequentialSearchContextInvariants.finish_stateInTransit
  {sctx : SequentialSearchContext σ κ σₕ asm}
  {curr : σ}
  (sctx_invs : SequentialSearchContextInvariants sys params (.some curr) sctx)
  (h_neighbors_seen : ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th curr →
    (fp.view v) ∈ sctx.log) :
  SequentialSearchContextInvariants sys params .none sctx := by
  rcases sctx with ⟨ctx, log, sq⟩ ; rcases sctx_invs with ⟨h1, h2, h3, h_closed⟩ ; dsimp only at *
  constructor <;> try assumption
  simp [SequentialSearchContext.isStableClosed] at h_closed ⊢
  intro ha hb u h_reachable hc hd l v hin
  by_cases heq : curr = u
  on_goal 2=> grind
  subst u ; eapply h_neighbors_seen ; assumption

theorem SequentialSearchContext.bfs_completeness
  {sctx : SequentialSearchContext σ κ σₕ asm}
  (sctx_invs : SequentialSearchContextInvariants sys params .none sctx)
  (h_explore_all : sctx.base.finished = some (.exploredAllReachableStates))
  (h_view_inj : Function.InjectiveOn fp.view sys.reachable) :
  ∀ s : σ, sys.reachable s → (fp.view s) ∈ sctx.log := by
  rcases sctx with ⟨ctx, log, sq⟩ ; rcases sctx_invs with ⟨⟨h_q_sound, h_vis_sound⟩, h_init_incl, h_q_emp, h_closed⟩ ; dsimp only at *
  intro s h_reachable
  induction h_reachable with
  | init s h_s_in_initStates => grind   -- using the initial seen set
  | step u v h_u_reach h_transition ih =>
    -- The key is to apply `stable_closed`, but `grind` is too powerful
    simp [fQueue.not_mem_iff_isEmpty] at h_q_emp ; grind

end Veil.ModelChecker.Concrete
