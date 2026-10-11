module

public import Veil.Core.Tools.ModelChecker.Concrete.SearchContext
public import Veil.Util.List

public section

namespace Veil.ModelChecker.Concrete

variable {ρ σ κ σₕ asm : Type}
  [fp : StateFingerprint σ σₕ]
  [ActionStatUpdate κ asm]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)
  (params : SearchParameters ρ σ)

@[expose, inline]
def initialLogAndRepresentativesCoreSequential (i : Nat)
    (acc : (List (QueueItem σₕ σ)) × Std.HashMap σₕ (LogEntry σₕ κ)) (s : σ) :=
  let (a, l) := acc
  let x := fp.view s
  if l.contains x then (a, l) else (⟨x, s, 0⟩ :: a, l.insert x (.init i))

@[expose, inline]
def initialLogAndRepresentativesSequential (initialStates : List σ) :
    Nat × (List (QueueItem σₕ σ)) × Std.HashMap σₕ (LogEntry σₕ κ) :=
  Veil.List.foldlIdxWithLengthReturned
    (f := initialLogAndRepresentativesCoreSequential)
    (init := ([], ∅)) (final := Prod.mk) initialStates

theorem initialLogAndRepresentativesSequential_eq_dedupFold (initialStates : List σ) :
    initialLogAndRepresentativesSequential (κ := κ) initialStates =
      (initialStates.length,
        dedupFold (fun x : σ × Nat => fp.view x.1) (fun x => .init x.2)
          (fun x => (⟨fp.view x.1, x.1, 0⟩ : QueueItem σₕ σ)) initialStates.zipIdx) := by
  rw [initialLogAndRepresentativesSequential, Veil.List.foldlIdxWithLengthReturned_eq_foldlIdx,
    List.foldlIdx_eq_foldl_zipIdx] ; simp only [Nat.zero_add] ; rfl

/-- Sequential initialization keeps the initial-state indices only in the log. -/
@[expose] def SequentialSearchContext.initial : SequentialSearchContext σ κ σₕ asm :=
  let (eq := hres) (len, reps, log) := initialLogAndRepresentativesSequential (κ := κ) sys.initStates
  ⟨BaseSearchContext.initial len, log, fQueue.ofListWithKnownLength reps
    ⟨log.size, by
      rw [initialLogAndRepresentativesSequential_eq_dedupFold] at hres
      simp [Prod.ext_iff] at hres
      rcases hres with ⟨-, h1, h2⟩ ; subst_vars
      rw [← Std.HashMap.length_keys]
      refine (DedupFoldDescription.extra (key' := QueueItem.fingerprint)
        (dedupFold_description (fun x : σ × Nat => fp.view x.1)
          (fun x => (LogEntry.init x.2 : LogEntry σₕ κ))
          (fun x => (⟨fp.view x.1, x.1, 0⟩ : QueueItem σₕ σ)) sys.initStates.zipIdx)
        (fun _ _ => rfl) Std.HashMap.nodup_keys ?_).2
      intro k ; rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_isSome_getElem?]⟩⟩

theorem SequentialSearchContext.initial_invs :
  SequentialSearchContextInvariants sys params .none (SequentialSearchContext.initial (fp := fp) sys) ∧
    ∃ rep dep, (SequentialSearchContext.initial (fp := fp) sys).LogSound sys params rep dep := by
  have h : DedupFoldDescription
      (key := fun x : σ × Nat => fp.view x.1)
      (val := fun x => (LogEntry.init x.2 : LogEntry σₕ κ))
      (proj := fun x => (⟨fp.view x.1, x.1, 0⟩ : QueueItem σₕ σ))
      (lst := Prod.fst) (look := fun acc y => acc.2[y]?)
      sys.initStates.zipIdx (initialLogAndRepresentativesSequential (κ := κ) sys.initStates).2 := by
    rw [initialLogAndRepresentativesSequential_eq_dedupFold] ; apply dedupFold_description
  simp only [SequentialSearchContext.initial, fQueue.ofListWithKnownLength_eq_ofList,
    BaseSearchContext.initial]
  generalize (initialLogAndRepresentativesSequential (κ := κ) (fp := fp) sys.initStates) = res at h ⊢
  rcases h with ⟨reps, h0, h1, h2, h3, h4⟩ ; rcases res with ⟨len, states, log⟩
  dsimp only at * ; subst h0 ; simp at h3 h4
  constructor ; on_goal 1=> constructor ; on_goal 1=> constructor
  all_goals (try simp [SequentialSearchContext.isStableClosed, ← fQueue.mem_ofList]) ; (try solve | intros ; grind)
  · intros ; subst_vars ; simp
    simp only [Std.HashMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists, h4]
    grind
  · grind [Std.HashMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]
  · intros s hin ; simp only [Std.HashMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists, h4]
    simp [List.mk_mem_zipIdx_iff_getElem?] at h2
    replace ⟨i, hi⟩ := List.getElem?_of_mem hin
    specialize h2 _ _ hi ; aesop
  · simp only [Std.HashMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists, h4]
    grind
  · let rep (a : σₕ) := (log[a]?).bind fun
      | .init j => sys.initStates[j]?
      | .step .. => none
    exists rep, fun _ => 0 ; dsimp [rep]
    refine ⟨⟨by simp, by simp [TerminationSound]⟩, ?_, ?_⟩    -- nothing recorded yet
    on_goal 1=> constructor
    all_goals (try simp [← fQueue.mem_ofList, Option.bind_eq_some_iff]) ; try grind
    · intros ; subst_vars ; simp [h4] ; grind

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
  rcases h with ⟨⟨hv, _⟩, hlog, hq⟩ ; exact ⟨⟨hv, by simp [TerminationSound]⟩, hlog, hq⟩

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
