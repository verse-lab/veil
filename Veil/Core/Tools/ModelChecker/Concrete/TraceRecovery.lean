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
    (h : LogInvariants sys look rep dep) {x : σₕ} : (look x).isSome = (rep x).isSome := by
  rw [Bool.eq_iff_iff] ; constructor
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

/-- A trace recovered from the log: the path that the log records for `x`, from the initial state
at position `initIdx` of `sys.initStates`, and the trace that re-executing it in `sys` builds. The
path places each step of the trace among the successes of its pre-state. -/
structure RecoveredTrace (look : LogLookup σₕ κ) (x : σₕ) where
  initIdx : Nat
  path : List (RetracedStep σₕ κ)
  trace : Trace ρ σ κ
  retrace_eq : retrace look x [] = some (initIdx, path)
  rebuild_eq : rebuild sys initIdx path = some trace

/-- The trace from an initial state to the state the search explored for `x`, with the path that
the log records. Total: the invariant says the log records such a trace. -/
def recoverTrace (look : LogLookup σₕ κ) (x : σₕ)
    (h : ∃ rep dep, LogInvariants sys look rep dep) (hx : (look x).isSome) : RecoveredTrace sys look x :=
  match hret : retrace look x [] with
  | some (i, path) =>
    match hreb : rebuild sys i path with
    | some t => ⟨i, path, t, hret, hreb⟩
    | none => False.elim (by
        obtain ⟨rep, dep, h⟩ := h ; obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hx
        obtain ⟨i', path', t, _, hret', hreb', -⟩ := retrace_rebuild sys h e x [] he
        grind)
  | none => False.elim (by
      obtain ⟨rep, dep, h⟩ := h ; obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hx
      obtain ⟨_, _, _, _, hret', -⟩ := retrace_rebuild sys h e x [] he
      simp [hret] at hret')

omit fp in
theorem RecoveredTrace.isValid {look : LogLookup σₕ κ} {x : σₕ} (r : RecoveredTrace sys look x) :
    r.trace.isValid sys.toRelational ∧ r.trace.theory = th :=
  rebuild_isValid sys r.rebuild_eq

/-- The recovered trace ends at the representative of `x`, for any representatives that the log
is sound for. -/
theorem RecoveredTrace.lastState {look : LogLookup σₕ κ} {rep : σₕ → Option σ} {dep : σₕ → Nat}
    (hrep : LogInvariants sys look rep dep) {x : σₕ} {s : σ} (hs : rep x = some s)
    (r : RecoveredTrace sys look x) : r.trace.lastState = s := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (hrep.rep_mem x (by simp [hs]))
  obtain ⟨i, path, t, s', hret, hreb, hs', hlast⟩ := retrace_rebuild sys hrep e x [] he
  rw [r.retrace_eq, List.append_nil] at hret ; cases hret
  rw [r.rebuild_eq] at hreb ; cases hreb
  rw [hs] at hs' ; cases hs' ; exact hlast

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

/-- Recording a layer of fresh fingerprints at once, as the parallel search does: `items` have
pairwise distinct fingerprints that the log does not know, each reached from a representative
the log knows, and `look'` is the log with their entries on top. -/
theorem LogInvariants.update_layer {look : LogLookup σₕ κ} {rep : σₕ → Option σ} {dep : σₕ → Nat}
    (h : LogInvariants sys look rep dep) (items : List (MapReduceQueueItem σₕ σ κ))
    (hnodup : (items.map MapReduceQueueItem.fingerprint).Nodup)
    (hfresh : ∀ item ∈ items, look item.fingerprint = none)
    (hfp : ∀ item ∈ items, fp.view item.state = item.fingerprint)
    (hstep : ∀ item ∈ items, ∃ p l i sp, item.entry = .step p l i ∧ rep p = some sp ∧
      (sys.tr th sp).successes[i]? = some (l, item.state))
    {look' : LogLookup σₕ κ}    -- The updated log after recording the new items
    (hl1 : ∀ item ∈ items, look' item.fingerprint = some item.entry)
    (hl2 : ∀ x, (∀ item ∈ items, item.fingerprint ≠ x) → look' x = look x) :
    ∃ rep' dep', LogInvariants sys look' rep' dep' ∧
      (∀ item ∈ items, rep' item.fingerprint = some item.state) ∧
      (∀ x s, rep x = some s → rep' x = some s) := by
  induction items generalizing look rep dep with
  | nil =>
    exists rep, dep
    obtain rfl : look' = look := funext fun x => hl2 x (by simp)
    grind
  | cons item rest ih =>
    obtain ⟨p, l, i, sp, hentry, hrp, hi⟩ := hstep item (List.mem_cons_self ..)
    have hx : look item.fingerprint = none := hfresh item (List.mem_cons_self ..)
    -- a fingerprint the log knows is not the one being recorded
    have hknown : ∀ y, (rep y).isSome → y ≠ item.fingerprint := by
      intro y ; rw [← h.rep_isSome_iff] ; grind
    rw [List.map_cons, List.nodup_cons] at hnodup
    have h' := h.update_step sys hx hrp hi (hfp item (List.mem_cons_self ..))
    rw [← hentry] at h'
    obtain ⟨rep', dep', hinv, hitems, hmono⟩ := ih h' hnodup.2
      (fun it hit => by unfold lookUpdate ; grind)
      (fun it hit => by grind)
      (fun it hit => by unfold repUpdate ; grind)
      (fun it hit => by grind)
      (fun x hx' => by unfold lookUpdate ; grind)
    refine ⟨rep', dep', hinv, ?_, ?_⟩
    · simp ; constructor
      · apply hmono ; simp [repUpdate]
      · grind
    · intro x s hs ; apply hmono
      simp [repUpdate, hknown x (by simp [hs]), hs]

/-! ### Deduplicating folds

The initial log of the sequential search and the merge of a round of the parallel search are both
folds that keep an item only when its key is new: they put the kept items in front of a list, and
map their keys to values. -/

/-- What a deduplicating fold over `l` does from `acc` to `res`. Think `l` as the input list of key-value
pairs (`K × V`), and `γ` being the type of the container that also holds `K × V` pairs,
but in an abstract way that requires `lst` to view the elements and `look` to find them by key.
`proj` is applied to `α` during folding. -/
def DedupFoldDescriptionWithAcc (key : α → K) (val : α → V) (proj : α → β)
    (lst : γ → List β) (look : γ → K → Option V)
    (l : List α) (acc res : γ) : Prop :=
  ∃ pfx : List α,
    lst res = pfx.map proj ++ lst acc ∧
    (pfx.map key).Nodup ∧
    (∀ a ∈ l, look acc (key a) = none → key a ∈ pfx.map key) ∧
    (∀ a ∈ pfx, a ∈ l ∧ look acc (key a) = none) ∧
    (∀ k v, look res k = some v ↔ look acc k = some v ∨ (k, v) ∈ pfx.map fun a => (key a, val a))

def DedupFoldDescription (key : α → K) (val : α → V) (proj : α → β)
    (lst : γ → List β) (look : γ → K → Option V)
    (l : List α) (res : γ) : Prop :=
  ∃ pfx : List α,
    lst res = pfx.map proj ∧
    (pfx.map key).Nodup ∧
    (∀ a ∈ l, key a ∈ pfx.map key) ∧
    (∀ a ∈ pfx, a ∈ l) ∧
    (∀ k v, look res k = some v ↔ (k, v) ∈ pfx.map fun a => (key a, val a))

/-- A deduplicating fold from an empty accumulator describes just the kept items. -/
theorem DedupFoldDescription.ofDedupFoldDescriptionWithAcc
    {key : α → K} {val : α → V} {proj : α → β} {lst : γ → List β} {look : γ → K → Option V}
    {l : List α} {acc res : γ}
    (h : DedupFoldDescriptionWithAcc key val proj lst look l acc res)
    (h_lst : lst acc = []) (h_look : ∀ k, look acc k = none) :
    DedupFoldDescription key val proj lst look l res := by
  simpa [DedupFoldDescriptionWithAcc, DedupFoldDescription, h_lst, h_look] using h

/-- Folding a step that keeps an item exactly when the map does not have its key yet, and then puts
`proj` of it in front of the list and maps its key to `val` of it. -/
theorem DedupFoldDescriptionWithAcc.of_foldl [BEq K] [LawfulBEq K]
    {key : α → K} {val : α → V} {proj : α → β} {lst : γ → List β} {look : γ → K → Option V}
    (f : γ → α → γ)
    -- If `a` is already in the accumulator (its key is present), it is not added again.
    (h_old : ∀ acc a, (look acc (key a)).isSome → f acc a = acc)
    -- Otherwise, `a` is added to the accumulator.
    (h_new : ∀ acc a, look acc (key a) = none →
      lst (f acc a) = proj a :: lst acc ∧
      ∀ k, look (f acc a) k = if key a == k then some (val a) else look acc k)
    (l : List α) (acc : γ) :
    DedupFoldDescriptionWithAcc key val proj lst look l acc (l.foldl f acc) := by
  induction l generalizing acc with
  | nil => exists [] ; simp
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases h : look acc (key a) with _ | v
    · obtain ⟨h_lst, h_look⟩ := h_new acc a h
      obtain ⟨pfx, h1, h2, h3, h4, h5⟩ := ih (f acc a)
      exists pfx ++ [a] ; grind
    · rw [h_old acc a (by simp [h])]
      obtain ⟨pfx, h1, h2, h3, h4, h5⟩ := ih acc
      exists pfx ; grind

/-! ### Violations recorded by the search -/

/-- `s` exhibits the violation `kind`: it violates exactly the invariants `names` of a
`safetyFailure names`, has no successor and is not terminating for a `deadlock`, has an
assertion failure with exception `e` for an `assertionFailure e`. No state exhibits an
`assumptionFailure`, which is about the theory, not a state. -/
def ExhibitsViolation (params : SearchParameters ρ σ) (s : σ) : ViolationKind → Prop
  | .safetyFailure names => violatedInvariantNames params th s = names ∧ names ≠ []
  | .deadlock => (sys.tr th s).successes = [] ∧ params.terminating.holdsOn th s = false
  | .assertionFailure e => ∃ f ∈ (sys.tr th s).failures, f.error = e
  | .assumptionFailure _ => False

/-- The violation recorded against fingerprint `x` is exhibited by the representative of `x`. -/
def ViolationSound (params : SearchParameters ρ σ) (rep : σₕ → Option σ) : σₕ × ViolationKind → Prop
  | (x, kind) => ∃ s, rep x = some s ∧ ExhibitsViolation sys params s kind

/-- The violation that an early termination reports, if any, is exhibited by the representative
of its fingerprint. -/
def TerminationSound (params : SearchParameters ρ σ) (rep : σₕ → Option σ) :
    Option (TerminationReason σₕ) → Prop
  | some (.earlyTermination (.foundViolatingState x names)) => ViolationSound sys params rep (x, .safetyFailure names)
  | some (.earlyTermination (.deadlockOccurred x)) => ViolationSound sys params rep (x, .deadlock)
  | some (.earlyTermination (.assertionFailed x e)) => ViolationSound sys params rep (x, .assertionFailure e)
  | _ => True

/-- The recovered trace ends at a state that exhibits the violation recorded against `x`. -/
theorem RecoveredTrace.exhibitsViolation {params : SearchParameters ρ σ} {look : LogLookup σₕ κ}
    {rep : σₕ → Option σ} {dep : σₕ → Nat} (hrep : LogInvariants sys look rep dep)
    {x : σₕ} {kind : ViolationKind} (hv : ViolationSound sys params rep (x, kind))
    (r : RecoveredTrace sys look x) : ExhibitsViolation sys params r.trace.lastState kind := by
  obtain ⟨s, hs, hex⟩ := hv
  rw [r.lastState sys hrep hs] ; exact hex

/-- The failing step of an assertion failure with exception `e` at `s`: total, since `s` has one. -/
def failingStepOf (s : σ) (e : Int) (h : ∃ f ∈ (sys.tr th s).failures, f.error = e) : Step σ κ :=
  let f := ((sys.tr th s).failures.find? (·.error == e)).get (by simpa [List.find?_isSome] using h)
  { transitionLabel := f.label, nextState := f.state }

/-- The failing step of `failingStepOf` fails with `e`, from `s`. -/
theorem failingStepOf_mem {s : σ} {e : Int} (h : ∃ f ∈ (sys.tr th s).failures, f.error = e) :
    letI step := failingStepOf sys s e h
    (step.transitionLabel, ExecutionOutcome.assertionFailure e step.nextState) ∈ sys.tr th s := by
  have key : ∀ f, (sys.tr th s).failures.find? (·.error == e) = some f →
      (⟨f.label, e, f.state⟩ : FailedTransition κ Int σ) ∈ (sys.tr th s).failures := by
    intro f hf
    have he : f.error = e := by simpa using List.find?_some hf
    rw [← he] ; exact List.mem_of_find?_eq_some hf
  exact Transitions.mem_assertionFailure_iff.mpr (key _ (Option.eq_some_of_isSome _))

/-- The failing step of a trace `t` that ends in the violation `kind`: for an assertion failure
with exception `e`, a transition from the last state of `t` that fails with `e`; for any other
violation, none. -/
def FailingStepSound (t : Trace ρ σ κ) : ViolationKind → Prop
  | .assertionFailure e => ∃ step, t.failingStep = some step ∧
      (step.transitionLabel, ExecutionOutcome.assertionFailure e step.nextState) ∈ sys.tr th t.lastState
  | _ => t.failingStep = none

/-! ### The picks of a recovered trace

The search runs `sys`, which does not log picks; `src` gives the initial states and transitions of
the same system computed with the picks logged, each with the picks that led to it. Nothing in the
proofs relates the two, so the picks of a trace recovered in `sys` are best effort: the initial
state of the trace looks up the initial state at the same position in `src`, and each step the
transition at the same position from the same pre-state; the picks are taken only if the state
found there has the fingerprint that the trace has. -/

variable (src : PickSource σ κ)

/-- The picks of the `idx`-th initial state in `src`, if it has fingerprint `x`. -/
def picksOfInit (idx : Nat) (x : σₕ) : Option (List String) := do
  let (s, picks) ← src.initStates[idx]?
  if fp.view s == x then some (picks.map toString) else none

/-- The picks of the `idx`-th success of `s` in `src`, if it leads to a state of fingerprint `x`. -/
def picksOfSuccess (s : σ) (idx : Nat) (x : σₕ) : Option (List String) := do
  let (l, s') ← (src.tr s).successes[idx]?
  if fp.view s' == x then some (l.picks.map toString) else none

/-- The picks of the first assertion failure of `s` with exception `e` in `src`, if it leads to a
state of fingerprint `x`. -/
def picksOfFailure (s : σ) (e : Int) (x : σₕ) : Option (List String) := do
  let f ← (src.tr s).failures.find? (·.error == e)
  if fp.view f.state == x then some (f.label.picks.map toString) else none

/-- The picks of the steps of `t`, which follows `path`: each step is at the position that `path`
records among the successes of its pre-state, and leads to the fingerprint that `path` records. -/
def stepPicksOf (t : Trace ρ σ κ) (path : List (RetracedStep σₕ κ)) : Array (Option (List String)) :=
  let pres := t.initialState :: t.steps.toList.map (·.nextState)
  (pres.zip path).toArray.map fun (s, p) => picksOfSuccess src s p.idx p.fingerprint

/-- The trace to the state recorded against `x`, recovered in `sys` from the log `look`, with the
failing step when the violation is an assertion failure, and beside it the picks of its states from
`src`. Total: the log is sound for some representatives, and the representative of `x` exhibits
the violation `kind`. -/
def recoverViolationTrace (params : SearchParameters ρ σ) (look : LogLookup σₕ κ) (x : σₕ)
    (kind : ViolationKind)
    (h : ∃ rep dep, LogInvariants sys look rep dep ∧ ViolationSound sys params rep (x, kind)) :
    Trace ρ σ κ × TracePicks :=
  let r := recoverTrace sys look x (h.elim fun rep h => h.elim fun dep h => ⟨rep, dep, h.1⟩) (by
    obtain ⟨rep, dep, hinv, s, hs, -⟩ := h ; exact hinv.rep_mem x (by simp [hs]))
  let failingStep := match kind, h with
    | .assertionFailure e, h => some (failingStepOf sys r.trace.lastState e (by
        obtain ⟨rep, dep, hinv, hv⟩ := h ; exact r.exhibitsViolation sys hinv hv))
    | _, _ => none
  ({ r.trace with failingStep := failingStep },
   { initialState := picksOfInit src r.initIdx (fp.view r.trace.initialState)
     steps := stepPicksOf src r.trace r.path
     failingStep := match kind, failingStep with
       | .assertionFailure e, some step => picksOfFailure src r.trace.lastState e (fp.view step.nextState)
       | _, _ => none })

variable {src} in
/-- The recovered trace of a violation is valid in `sys`, ends at a state that exhibits the
violation, and has the failing step of an assertion failure (and none otherwise). -/
theorem recoverViolationTrace_sound {params : SearchParameters ρ σ} {look : LogLookup σₕ κ}
    {x : σₕ} {kind : ViolationKind}
    (h : ∃ rep dep, LogInvariants sys look rep dep ∧ ViolationSound sys params rep (x, kind)) :
    letI t := (recoverViolationTrace sys src params look x kind h).1
    t.isValid sys.toRelational ∧ t.theory = th ∧ ExhibitsViolation sys params t.lastState kind ∧
      FailingStepSound sys t kind := by
  have ⟨rep, dep, hinv, hv⟩ := h
  have ⟨s, hs, _⟩ := hv
  let r := recoverTrace sys look x ⟨rep, dep, hinv⟩ (hinv.rep_mem x (by simp [hs]))
  obtain ⟨⟨h1, h2, h3⟩, hth⟩ := r.isValid sys
  refine ⟨⟨h1, h2, h3⟩, hth, r.exhibitsViolation sys hinv hv, ?_⟩
  cases kind <;> first | rfl | exact ⟨_, rfl, failingStepOf_mem sys _⟩

/-- What a result of the search guarantees: a violation comes with a trace that is valid in `sys`,
ends at a state that exhibits it, and has the failing step of an assertion failure (and none
otherwise), except for an `assumptionFailure`, which comes without one and names the assumptions
that the theory violates. Nothing is claimed about a search that found no violation, or was
cancelled. -/
def ResultSound (params : SearchParameters ρ σ) : ModelCheckingResult ρ σ κ σₕ → Prop
  | .foundViolation _ kind trace? _ =>
    match trace? with
    | some t => t.isValid sys.toRelational ∧ t.theory = th ∧ ExhibitsViolation sys params t.lastState kind ∧
        FailingStepSound sys t kind
    | none => ∃ names, kind = .assumptionFailure names ∧ names = params.violatedAssumptions th ∧ names ≠ []
  | .noViolationFound _ _ => True
  | .cancelled => True

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

/-- The violations that `ctx` has recorded, and the one that its early termination reports, if any,
are exhibited by the representatives `rep`. -/
structure BaseSearchContext.ViolationTerminationSound {asm : Type} [ActionStatUpdate κ asm]
    (params : SearchParameters ρ σ) (ctx : BaseSearchContext σ κ σₕ asm) (rep : σₕ → Option σ) : Prop where
  violations_sound : ∀ v ∈ ctx.violatingStates, ViolationSound sys params rep v
  termination_sound : TerminationSound sys params rep ctx.finished

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
    all_goals simp [ViolationSound, ExhibitsViolation] ; grind
  · dsimp [tmp2] ; simp-- ; split_ifs
    intro r hr ; rw [List.findSome?_eq_some_iff] at hr
    rcases hr with ⟨pre, a, suf, heq, ha, -⟩
    dsimp [TerminationSound, ViolationSound, ExhibitsViolation] ; cases a <;> dsimp at ha
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

/-- Merging base contexts keeps what their violations say. -/
theorem BaseSearchContext.mergeWithoutDepthChange_foldl_sound {asm : Type} [ActionStatUpdate κ asm]
    (params : SearchParameters ρ σ) {rep : σₕ → Option σ}
    {acc : BaseSearchContext σ κ σₕ asm} {ctxs : List (BaseSearchContext σ κ σₕ asm)}
    (h_acc : acc.ViolationTerminationSound sys params rep)
    (h_ctxs : ∀ ctx ∈ ctxs, ctx.ViolationTerminationSound sys params rep) :
    (ctxs.foldl (init := acc) BaseSearchContext.mergeWithoutDepthChange).ViolationTerminationSound sys params rep := by
  induction ctxs generalizing acc with
  | nil => exact h_acc
  | cons ctx ctxs ih =>
    apply ih _ fun ctx' h => h_ctxs ctx' (List.mem_cons_of_mem _ h)
    obtain ⟨hv1, hf1⟩ := h_acc ; obtain ⟨hv2, hf2⟩ := h_ctxs ctx List.mem_cons_self
    constructor <;> simp only [BaseSearchContext.mergeWithoutDepthChange] <;> try grind
    rcases h : acc.finished with _ | r <;> simp only [h, Option.none_or, Option.some_or] at hf1 ⊢ <;> assumption

end Veil.ModelChecker.Concrete
