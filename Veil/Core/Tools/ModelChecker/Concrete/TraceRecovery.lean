module

public import Veil.Core.Tools.ModelChecker.Concrete.Core

@[expose] public section

namespace Veil.ModelChecker.Concrete

/-! ## Trace recovery

The search records, for each fingerprint it sees, how it first reached a state of that
fingerprint (`LogEntry`). Recovery reads the log as a function from fingerprints to entries
(`LogLookup`), so it does not depend on how a search stores its log. `retrace` walks the entries
back to an initial state, and `rebuild` re-executes the system along the positions they record.
`LogInvariants` is what the search guarantees about its log, stated in terms of the
representative state `rep x` it explored for each fingerprint `x` and a depth `dep x` that
decreases along parent links (*the search never stores either; they exist only in the proofs*):
it makes recovery total, and the recovered trace end at `rep x`. None of this assumes `fp.view`
to be injective; a collision costs the search completeness (it drops a state), never the
soundness of the trace it reports. -/

section Helpers

variable {σ κ σₕ : Type}

/-- A log as recovery reads it: what was recorded for a fingerprint, if anything. -/
abbrev LogLookup (σₕ κ : Type) := σₕ → Option (LogEntry σₕ κ)

/-- The log held in a hash map. -/
def logLookup [BEq σₕ] [Hashable σₕ] (m : Std.HashMap σₕ (LogEntry σₕ κ)) : LogLookup σₕ κ :=
  fun y => m[y]?

@[simp, grind =] theorem logLookup_apply [BEq σₕ] [Hashable σₕ]
    {m : Std.HashMap σₕ (LogEntry σₕ κ)} {y : σₕ} : logLookup m y = m[y]? := rfl

/-- `look` with `x` mapped to `e`. -/
def lookUpdate [BEq σₕ] (look : LogLookup σₕ κ) (x : σₕ) (e : LogEntry σₕ κ) : LogLookup σₕ κ :=
  fun y => if x == y then some e else look y

theorem logLookup_insert [BEq σₕ] [Hashable σₕ] [LawfulBEq σₕ] [LawfulHashable σₕ]
    {m : Std.HashMap σₕ (LogEntry σₕ κ)} {x : σₕ} {e : LogEntry σₕ κ} :
    logLookup (m.insert x e) = lookUpdate (logLookup m) x e := by
  funext y ; simp [logLookup, lookUpdate, Std.HashMap.getElem?_insert]

/-- `rep` with `x` mapped to `s`. -/
def repUpdate [BEq σₕ] (rep : σₕ → Option σ) (x : σₕ) (s : σ) : σₕ → Option σ :=
  fun y => if y == x then some s else rep y

/-- `dep` with `x` mapped to `n`. -/
def depUpdate [BEq σₕ] (dep : σₕ → Nat) (x : σₕ) (n : Nat) : σₕ → Nat :=
  fun y => if y == x then n else dep y

end Helpers

variable {ρ σ κ σₕ : Type} [fp : StateFingerprint σ σₕ] {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (Transitions κ Int σ) th)

-- CHECK This seems to be exactly the second branch of `LogEntry`
/-- One step of a retraced path: the fingerprint of the post-state, the label of the transition
and its position among the successes of the pre-state. -/
structure RetracedStep (σₕ κ : Type) where
  fingerprint : σₕ
  label : κ
  idx : Nat
deriving Repr

/-- The path recorded in the log from `x` back to an initial state: the position of that
initial state in `sys.initStates`, then one step per transition, in path order. Looks only at
the log, and needs no bound on the length of the path: `retrace_rebuild` shows it terminates on
a log that satisfies the invariant. -/
def retrace (look : LogLookup σₕ κ) (x : σₕ) (acc : List (RetracedStep σₕ κ)) :
    Option (Nat × List (RetracedStep σₕ κ)) :=
  match look x with
  | some (.init i) => some (i, acc)
  | some (.step p l i) => retrace look p (⟨x, l, i⟩ :: acc)
  | none => none
partial_fixpoint

/-- Extend `t` by re-executing the system along `path`. -/
def rebuildFrom (path : List (RetracedStep σₕ κ)) (t : Trace ρ σ κ) : Option (Trace ρ σ κ) :=
  path.foldlM (init := t) fun t step => do
    let (l, s) ← (sys.tr th t.lastState).successes[step.idx]?
    return t.push { transitionLabel := l, nextState := s }

/-- The trace that starts at `sys.initStates[initIdx]` and follows `path`. -/
def rebuild (initIdx : Nat) (path : List (RetracedStep σₕ κ)) : Option (Trace ρ σ κ) := do
  let s ← sys.initStates[initIdx]?
  rebuildFrom sys path { theory := th, initialState := s, steps := #[] }

/-- The trace from an initial state to the state the search explored for `x`, as the log
records it. Pure; `recoverTrace` is the version that cannot fail. -/
def recoverTrace? (look : LogLookup σₕ κ) (x : σₕ) : Option (Trace ρ σ κ) :=
  (retrace look x []).bind fun (i, path) => rebuild sys i path

/-! ### Validity of rebuilt traces, unconditionally -/

omit fp in
theorem rebuildFrom_isValid : ∀ (path : List (RetracedStep σₕ κ)) (t t' : Trace ρ σ κ),
    t.theory = th → t.isValid sys.toRelational →
    rebuildFrom sys path t = some t' → t'.isValid sys.toRelational ∧ t'.theory = th := by
  intro path
  induction path with
  | nil => intro t t' hth hv h ; simp [rebuildFrom] at h ; subst h ; exact ⟨hv, hth⟩
  | cons step path ih =>
    intro t t' hth hv h
    simp only [rebuildFrom, List.foldlM_cons, bind_assoc, pure_bind] at h
    obtain ⟨⟨l, s⟩, hget, h⟩ := Option.bind_eq_some_iff.mp h
    apply ih _ _ (by simp [Trace.push, hth]) _ h
    apply Trace.push_isValid _ _ _ hv
    simp only [EnumerableTransitionSystem.toRelational, hth]
    exact Transitions.mem_success_iff.mpr (List.mem_of_getElem? hget)

omit fp in
theorem rebuild_isValid {initIdx : Nat} {path : List (RetracedStep σₕ κ)} {t : Trace ρ σ κ}
    (h : rebuild sys initIdx path = some t) : t.isValid sys.toRelational ∧ t.theory = th := by
  unfold rebuild at h
  obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.mp h
  apply rebuildFrom_isValid sys _ _ _ rfl _ h
  apply Trace.isValid_empty <;> grind

omit fp in
theorem recoverTrace?_isValid {look : LogLookup σₕ κ} {x : σₕ} {t : Trace ρ σ κ}
    (h : recoverTrace? sys look x = some t) : t.isValid sys.toRelational ∧ t.theory = th := by
  unfold recoverTrace? at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨⟨i, path⟩, _, h⟩ := h
  exact rebuild_isValid sys h

/-! ### The log invariant -/

/-- What the search guarantees about its log, given `rep`, the state it explored for each
fingerprint (`none` for fingerprints it has not seen), and `dep`, a depth that decreases from a
state to its parent. Every entry is a true record about these representatives: the parent of a
`step` entry is in the log, nearer to an initial state, and re-executing the recorded transition
from the parent's representative yields the entry's own representative, with the recorded label. -/
structure LogInvariants (look : LogLookup σₕ κ) (rep : σₕ → Option σ) (dep : σₕ → Nat) : Prop where
  rep_fp : ∀ x s, rep x = some s → fp.view s = x
  rep_mem : ∀ x, (rep x).isSome → (look x).isSome
  init_ok : ∀ x i, look x = some (.init i) → ∃ s, rep x = some s ∧ sys.initStates[i]? = some s
  step_ok : ∀ x p l i, look x = some (.step p l i) →
    dep p < dep x ∧
    ∃ sp s, rep p = some sp ∧ rep x = some s ∧ (sys.tr th sp).successes[i]? = some (l, s)

theorem LogInvariants.rep_isSome_iff {look : LogLookup σₕ κ} {rep : σₕ → Option σ} {dep : σₕ → Nat}
    (h : LogInvariants sys look rep dep) {x : σₕ} : (look x).isSome ↔ (rep x).isSome := by
  constructor
  on_goal 2=> apply h.rep_mem
  intro hx
  rw [Option.isSome_iff_exists] at hx
  obtain ⟨e, he⟩ := hx
  cases e with
  | init i => obtain ⟨s, hs, _⟩ := h.init_ok x i he ; grind
  | step p l i => obtain ⟨_, _, s, _, hs, _⟩ := h.step_ok x p l i he ; grind

/-- For a log held in a hash map: every fingerprint with a representative is in the map. -/
theorem LogInvariants.mem_of_rep_isSome {m : Std.HashMap σₕ (LogEntry σₕ κ)} {rep : σₕ → Option σ}
    {dep : σₕ → Nat} (h : LogInvariants sys (logLookup m) rep dep) : ∀ x, (rep x).isSome → x ∈ m := by
  intro x hx ; exact Std.HashMap.mem_iff_isSome_getElem?.mpr (h.rep_mem x hx)

/-! ### Completeness of recovery under the invariant -/

/-- Under the invariant, retracing `x` succeeds, and rebuilding the path ends at the
representative of `x`. By induction on a bound on `dep x`. -/
theorem retrace_rebuild {look : LogLookup σₕ κ} {rep : σₕ → Option σ} {dep : σₕ → Nat}
    (h : LogInvariants sys look rep dep) :
    ∀ (e : LogEntry σₕ κ) (x : σₕ) (acc : List (RetracedStep σₕ κ)),
      look x = some e →
      ∃ i path t s,
        retrace look x acc = some (i, path ++ acc) ∧
        rebuild sys i path = some t ∧
        rep x = some s ∧ t.lastState = s := by
  rcases h with ⟨rep_fp, rep_mem, init_ok, step_ok⟩
  intro e x ; rcases e with i | ⟨p, l, i⟩
  on_goal 1=>
    intro acc hx
    obtain ⟨s, hs, hi⟩ := init_ok x i hx
    refine ⟨i, [], { theory := th, initialState := s, steps := #[] }, s, ?_, ?_, hs, ?_⟩
    · rw [retrace, hx] ; rfl
    · simp [rebuild, hi, rebuildFrom]
    · simp
  have (eq := hd) d := dep x
  revert x hd ; induction d using Nat.strongRecOn generalizing p l i
  rename_i d ih ; intro x hd acc hx ; subst d
  obtain ⟨hlt, sp, s, hsp, hs, hi⟩ := step_ok x p l i hx
  rcases hp : look p with _ | (i' | ⟨p', l', i'⟩)
  · grind [rep_mem p]
  · obtain ⟨sp_, hsp_, hi'⟩ := init_ok _ _ hp
    simp [hsp] at hsp_ ; subst sp_
    exists i', [⟨x, l, i⟩]
    simp [rebuild, hi', rebuildFrom, hi, hs]
    rw [retrace, hx] ; dsimp ; rw [retrace, hp]
  · specialize ih (dep p) hlt _ _ _ _ rfl (⟨x, l, i⟩ :: acc) hp
    obtain ⟨ip, pathp, tp, sp_, hret, hreb, hsp_, hlast⟩ := ih
    simp [hsp] at hsp_ ; subst sp_
    exists ip, pathp ++ [⟨x, l, i⟩], tp.push { transitionLabel := l, nextState := s }, s
    split_ands <;> try grind
    · rw [retrace, hx] ; simp [hret]
    · simp only [rebuild, Option.bind_eq_bind, Option.bind_eq_some_iff] at hreb ⊢
      obtain ⟨s0, hs0, hreb⟩ := hreb
      refine ⟨s0, hs0, ?_⟩
      unfold rebuildFrom at hreb ⊢
      rw [List.foldlM_append, hreb]
      grind

theorem recoverTrace?_complete {look : LogLookup σₕ κ} {rep : σₕ → Option σ} {dep : σₕ → Nat}
    (h : LogInvariants sys look rep dep) {x : σₕ} (hx : (look x).isSome) :
    ∃ t s, recoverTrace? sys look x = some t ∧ rep x = some s ∧ t.lastState = s := by
  rw [Option.isSome_iff_exists] at hx
  obtain ⟨e, he⟩ := hx
  obtain ⟨i, path, t, s, hret, hreb, hs, hlast⟩ := retrace_rebuild sys h e x [] he
  exact ⟨t, s, by simp [recoverTrace?, hret, hreb], hs, hlast⟩

/-- The trace from an initial state to the state the search explored for `x`. Total: the
invariant says the log records such a trace. -/
def recoverTrace (look : LogLookup σₕ κ) (x : σₕ)
    (h : ∃ rep dep, LogInvariants sys look rep dep) (hx : (look x).isSome) : Trace ρ σ κ :=
  (recoverTrace? sys look x).get (by
    obtain ⟨rep, dep, h⟩ := h
    obtain ⟨t, _, ht, _⟩ := recoverTrace?_complete sys h hx
    simp [ht])

theorem recoverTrace_isValid {look : LogLookup σₕ κ} {x : σₕ}
    {h : ∃ rep dep, LogInvariants sys look rep dep} {hx : (look x).isSome} :
    (recoverTrace sys look x h hx).isValid sys.toRelational ∧ (recoverTrace sys look x h hx).theory = th := by
  unfold recoverTrace ; exact recoverTrace?_isValid sys (Option.some_get _).symm

theorem recoverTrace_lastState {look : LogLookup σₕ κ} {rep : σₕ → Option σ} {dep : σₕ → Nat}
    (hrep : LogInvariants sys look rep dep) {x : σₕ} {s : σ} (hs : rep x = some s)
    {h : ∃ rep dep, LogInvariants sys look rep dep} {hx : (look x).isSome} :
    (recoverTrace sys look x h hx).lastState = s := by
  obtain ⟨t, s', ht, hs', hlast⟩ := recoverTrace?_complete sys hrep hx
  rw [hs] at hs' ; injection hs' with hs' ; subst hs'
  simp [recoverTrace, ht, hlast]

/-! ### Preservation of the invariant -/

/-- Recording a fresh fingerprint `x` as reached from `p`, whose representative `sp` has
`(l, s)` as its `i`-th success, where `x` is the fingerprint of `s`. -/
theorem LogInvariants.update_step {look : LogLookup σₕ κ} {rep : σₕ → Option σ} {dep : σₕ → Nat}
    (h : LogInvariants sys look rep dep) {x p : σₕ} {l : κ} {i : Nat} {sp s : σ}
    (hx : look x = none) (hrp : rep p = some sp)
    (hi : (sys.tr th sp).successes[i]? = some (l, s)) (hfp : fp.view s = x) :
    LogInvariants sys (lookUpdate look x (.step p l i)) (repUpdate rep x s) (depUpdate dep x (dep p + 1)) := by
  rcases h with ⟨rep_fp, rep_mem, init_ok, step_ok⟩
  have hpx : p ≠ x := by grind
  constructor <;> (try unfold lookUpdate) <;> unfold repUpdate <;> (try unfold depUpdate) <;> grind

/-! ### The initial log -/

theorem initialLogAndRepresentativesCore_description (initStates : List (σ × Nat)) (acc : (List σ) × Std.HashMap σₕ (LogEntry σₕ κ)) :
    letI res := initStates.foldl (init := acc) fun a (s, i) => initialLogAndRepresentativesCore i a s
    ∃ pfx : List (σ × Nat),
      letI fps := pfx.map fun x => fp.view x.1
      res.1 = pfx.map Prod.fst ++ acc.1 ∧
      fps.Nodup ∧
      (∀ a, (∃ item ∈ initStates, fp.view item.1 = a) → a ∉ acc.2 → a ∈ fps) ∧
      (∀ item ∈ pfx, item ∈ initStates ∧ fp.view item.1 ∉ acc.2) ∧
      (∀ a b, res.2[a]? = some b ↔ acc.2[a]? = some b ∨ (a, b) ∈ pfx.map fun x => (fp.view x.1, .init x.2)) := by
  induction initStates generalizing acc with
  | nil => exists [] ; simp [List.foldl]
  | cons item states ih =>
    rcases item with ⟨s, i⟩
    dsimp [List.foldl] ; dsimp only at *
    specialize ih (initialLogAndRepresentativesCore i acc s)
    revert ih ; fun_cases initialLogAndRepresentativesCore i acc s
    · intro ih ; rcases ih with ⟨pfx, h_pfx, h_nodup, h_subseq, h_fps, h_mem_iff⟩
      exists pfx ; split_ands <;> grind
    · intro ih ; dsimp only at ih ; rcases ih with ⟨pfx, h_pfx, h_nodup, h_subseq, h_fps, h_mem_iff⟩
      rename_i a b c d ; simp at *
      exists (pfx ++ [(s, i)]) ; simp ; split_ands <;> try grind
      -- `σₕ` has no `DecidableEq`, so the condition of the insertion's `if` stays a `==`
      intro a1 b1 ; open Classical in simp [h_mem_iff, Std.HashMap.getElem?_insert, beq_iff_eq]
      aesop

/-- The representatives are the first initial state of each fingerprint; `reps` pairs each one with
its position in `initStates`, which the log records. -/
theorem initialLogAndRepresentatives_description (initStates : List σ) :
    letI res := initialLogAndRepresentatives (κ := κ) (fp := fp) initStates
    ∃ reps : List (σ × Nat), res.1 = reps.map Prod.fst ∧
    letI fps := reps.map fun x => fp.view x.1
    fps.Nodup ∧
    (∀ a, (∃ item ∈ initStates, fp.view item = a) → a ∈ fps) ∧
    (∀ item ∈ reps, item.1 ∈ initStates ∧ initStates[item.2]? = some item.1) ∧
    (∀ a b, res.2[a]? = some b ↔ (a, b) ∈ reps.map fun x => (fp.view x.1, LogEntry.init x.2)) := by
  obtain ⟨pfx, h⟩ := initialLogAndRepresentativesCore_description (κ := κ) (fp := fp) (initStates.zipIdx) ([], ∅)
  have heq := List.foldlIdx_eq_foldl_zipIdx (f := initialLogAndRepresentativesCore (κ := κ) (fp := fp)) (s := 0) (i := ([], ∅)) (xs := initStates)
  rw [← initialLogAndRepresentatives.eq_def] at heq
  rw [← heq] at h
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  exists pfx
  simp at *
  split_ands <;> try assumption
  · intro a hin ; obtain ⟨i, hin⟩ := List.getElem?_of_mem hin ; rw [← List.mk_mem_zipIdx_iff_getElem?] at hin
    grind
  · grind [List.mk_mem_zipIdx_iff_getElem?]

/-! ### Violations recorded by the search -/

/-- The violation recorded against fingerprint `x` is exhibited by the representative of `x`. -/
def ViolationSound (params : SearchParameters ρ σ) (rep : σₕ → Option σ) : σₕ × ViolationKind → Prop
  | (x, .safetyFailure names) =>
    ∃ s, rep x = some s ∧ violatedInvariantNames params th s = names ∧ names ≠ []
  | (x, .deadlock) =>
    ∃ s, rep x = some s ∧ (sys.tr th s).successes = [] ∧ params.terminating.holdsOn th s = false
  | (x, .assertionFailure e) =>
    ∃ s, rep x = some s ∧ ∃ f ∈ (sys.tr th s).failures, f.error = e
  | (_, .assumptionFailure _) => False

/-- The violation that an early termination reports, if any, is exhibited by the representative
of its fingerprint. -/
def TerminationSound (params : SearchParameters ρ σ) (rep : σₕ → Option σ) :
    Option (TerminationReason σₕ) → Prop
  | some (.earlyTermination (.foundViolatingState x names)) => ViolationSound sys params rep (x, .safetyFailure names)
  | some (.earlyTermination (.deadlockOccurred x)) => ViolationSound sys params rep (x, .deadlock)
  | some (.earlyTermination (.assertionFailed x e)) => ViolationSound sys params rep (x, .assertionFailure e)
  | _ => True

omit fp in
theorem ViolationSound.mono {params : SearchParameters ρ σ} {rep rep' : σₕ → Option σ}
    (hle : ∀ x s, rep x = some s → rep' x = some s) {v : σₕ × ViolationKind}
    (h : ViolationSound sys params rep v) : ViolationSound sys params rep' v := by
  rcases v with ⟨x, v⟩
  cases v <;> simp only [ViolationSound] at h ⊢ <;> grind

omit fp in
theorem TerminationSound.mono {params : SearchParameters ρ σ} {rep rep' : σₕ → Option σ}
    (hle : ∀ x s, rep x = some s → rep' x = some s) {r : Option (TerminationReason σₕ)}
    (h : TerminationSound sys params rep r) : TerminationSound sys params rep' r := by
  rcases r with _ | ⟨_ | ⟨x, names⟩ | x | ⟨x, e⟩ | _ | _⟩ <;> simp only [TerminationSound] at h ⊢ <;>
    try exact ViolationSound.mono sys hle h

omit fp in
/-- Checking a state records only violations that it exhibits. -/
theorem checkViolationsAndMaybeTerminate_sound (params : SearchParameters ρ σ) {fpSt : σₕ} {curr : σ}
    (completedDepth : Nat) {rep : σₕ → Option σ} (hrep : rep fpSt = some curr) :
    let res := checkViolationsAndMaybeTerminate params th fpSt curr completedDepth
      (!(sys.tr th curr).successes.isEmpty) (sys.tr th curr).failures
    (∀ v ∈ res.1, ViolationSound sys params rep v) ∧
      (∀ r, res.2 = some r → TerminationSound sys params rep (some (.earlyTermination r))) := by
  fun_cases checkViolationsAndMaybeTerminate
  rename_i safetyViolations safetyViolation deadlock tmp1 tmp2
  dsimp ; constructor
  · dsimp [tmp1] ; split_ifs
    all_goals simp [ViolationSound] ; grind
  · dsimp [tmp2] ; simp-- ; split_ifs
    intro r hr ; rw [List.findSome?_eq_some_iff] at hr
    rcases hr with ⟨pre, a, suf, heq, ha, -⟩
    dsimp [TerminationSound, ViolationSound] ; cases a <;> dsimp at ha
    all_goals (try split at ha) <;> simp at ha <;> subst_vars <;> try grind
    rcases ha with ⟨a, ha, rfl⟩ ; simp ; have ha := List.mem_of_head? ha
    exists curr ; apply And.intro hrep ; exists a

-- FIXME: Why is this thing here?
omit fp in
theorem BaseSearchContext.processState_snd {asm : Type} [fp : StateFingerprint σ σₕ] [ActionStatUpdate κ asm]
    (params : SearchParameters ρ σ) (th : ρ) (fpSt : σₕ) (curr : σ) (trs : Transitions κ Int σ)
    (ctx : BaseSearchContext σ κ σₕ asm) :
    ∀ succs, (ctx.processState params th fpSt curr trs).2 = some succs → succs = trs.successes := by
  unfold BaseSearchContext.processState ; grind

/-- Processing a state records only violations that it exhibits. -/
theorem BaseSearchContext.processState_sound {asm : Type} [ActionStatUpdate κ asm]
    (params : SearchParameters ρ σ) {fpSt : σₕ} {curr : σ}
    (ctx : BaseSearchContext σ κ σₕ asm) {rep : σₕ → Option σ} (hrep : rep fpSt = some curr)
    (hv : ∀ v ∈ ctx.violatingStates, ViolationSound sys params rep v)
    (hf : TerminationSound sys params rep ctx.finished) :
    letI res := ctx.processState params th fpSt curr (sys.tr th curr)
    (∀ v ∈ res.1.violatingStates, ViolationSound sys params rep v) ∧
      TerminationSound sys params rep res.1.finished := by
  have hchk := checkViolationsAndMaybeTerminate_sound sys params (fpSt := fpSt) (curr := curr) ctx.completedDepth hrep
  dsimp only at hchk ⊢
  unfold BaseSearchContext.processState
  grind

end Veil.ModelChecker.Concrete
