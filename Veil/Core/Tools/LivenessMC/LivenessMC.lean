module

public import Veil.Core.Tools.LivenessMC.Interface
public import LTLLib.TGBABased.ModelCheck
public import LTLLib.ModelCheck

public section

/-! Example usage for a liveness property "someChosen":

```lean
#eval Veil.LivenessMC.check (enumerableTransitionSystem th0) someChosen
  (by native_decide) (by native_decide)
```
-/

namespace Veil.LivenessMC

variable {σ : Type} [BEq σ] [Hashable σ] [LawfulBEq σ]


/-- Finds a finite closed superset of the reachable states by exploration, for proving termination.
  Enables user to just write `native_decide` instead of manually proving finiteness.  -/
partial def bfsClosure (succs : σ → Array σ) (initialStates : List σ) : Std.HashSet σ :=
  go (Std.HashSet.ofList initialStates) initialStates.toArray
where
  go (seen : Std.HashSet σ) (frontier : Array σ) : Std.HashSet σ :=
    if frontier.isEmpty then
      seen
    else
      let (seen, next) := frontier.foldl (init := (seen, (#[] : Array σ)))
        fun (seen, next) s =>
          (succs s).foldl (init := (seen, next))
            fun (seen, next) t =>
              if seen.contains t then (seen, next) else (seen.insert t, next.push t)
      go seen next

/-- If `closure` contains every initial state and is closed under `succs`, the reachable set is finite. -/
theorem finiteReach_of_closed
    (succs : σ → Array σ) (initialStates : List σ) (closure : Std.HashSet σ)
    (hinit : initialStates.all closure.contains = true)
    (hclosed : closure.toList.all (fun s => (succs s).all closure.contains) = true) :
    LTLLib.FiniteReach initialStates succs := by
  refine ⟨closure.toList, ?_⟩
  intro x hx
  induction hx with
  | base hi =>
    exact Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr
      (List.all_eq_true.mp hinit _ hi))
  | step _ ht ih =>
    have h2 := List.all_eq_true.mp hclosed _ ih
    exact Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr
      (Array.all_eq_true'.mp h2 _ ht))

variable {ρ l : Type} [BEq l] [Hashable l] {th : ρ}

def sysSucc
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) : σ → Array σ := fun st =>
  ((sys.tr th st).filterMap fun (_, o) => match o with
    | .success s' => some s'
    | _ => none).toArray

/-- The labels (action instantiations) that can *fire* in `st`: those with a `.success` outcome.

"Step-enabled" (not "guard-enabled"). Reading `E(a)` off the successful outcomes keeps it coherent with `T(a)` on the graph the checker walks: `E(a)`
holds at `s` exactly when some `T(a)`-step leaves `s`.
Under the other reading `□(E(a) → ◇T(a))` would be unsatisfiable on a model whose action always faults,
reporting a fairness violation where the real problem is the assertion failure. -/
def enabledLabelsTr [BEq l] [Hashable l]
    (tr : σ → List (l × Veil.ExecutionOutcome Int σ)) (st : σ) : List l :=
  ((tr st).foldl (init := Std.HashSet.emptyWithCapacity) fun seen (lbl, o) =>
    match o with
    | .success _ => seen.insert lbl
    | _ => seen).toList

def enabledLabels [BEq l] [Hashable l]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (st : σ) : List l :=
  enabledLabelsTr (sys.tr th) st

/-- One shared empty letter as a nullary definition so it is a closed constant allocated once -/
def emptyLetter : Std.HashSet Nat := ∅

/-- The edge labelling as **data**, not as a function: `none` when the property has no `T(…)`. -/
def edgeLabelling (p : LivenessProperty ρ σ l) : Option (l → Std.HashSet Nat) :=
  if p.hasEdgeAtoms then some p.edgeLabel else none

/-- The system as a *labelled* graph: each successful step paired with the atoms it contributes, which are
the `T(a)` atoms its label matches. -/
def sysStepsLabelledTr (tr : σ → List (l × Veil.ExecutionOutcome Int σ))
    (edgeLabel? : Option (l → Std.HashSet Nat)) :
    σ → Array (LTLLib.LStep Nat σ) :=
  match edgeLabel? with
  | none => fun st =>
    ((tr st).filterMap fun (_, o) => match o with
      | .success s' => some (emptyLetter, s')
      | _ => none).toArray
  | some edgeLabel => fun st =>
    ((tr st).filterMap fun (lbl, o) => match o with
      | .success s' => some (edgeLabel lbl, s')
      | _ => none).toArray

def sysStepsLabelled
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th)
    (edgeLabel? : Option (l → Std.HashSet Nat)) :
    σ → Array (LTLLib.LStep Nat σ) :=
  sysStepsLabelledTr (sys.tr th) edgeLabel?

omit [BEq σ] [Hashable σ] [LawfulBEq σ] [BEq l] [Hashable l] in
/-- Forgetting the letters gives back the unlabelled graph. -/
theorem targets_sysStepsLabelled
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th)
    (edgeLabel? : Option (l → Std.HashSet Nat)) :
    LTLLib.LSys.targets (sysStepsLabelled sys edgeLabel?) = sysSucc sys := by
  funext st
  cases edgeLabel? <;>
    · show Array.map Prod.snd _ = _
      apply Array.ext'
      simp only [sysStepsLabelled, sysStepsLabelledTr, sysSucc, Array.toList_map,
        List.toList_toArray, List.map_filterMap]
      congr 1
      funext x
      cases x.2 <;> rfl

/-- The state labelling: the `⌜ … ⌝` atoms, plus the `E(a)` atoms. The enabled set costs a `tr` call, so it
is only computed when the property actually mentions an `E`. -/
def sysLabelOfTr [BEq l] [Hashable l]
    (tr : σ → List (l × Veil.ExecutionOutcome Int σ)) (p : LivenessProperty ρ σ l) (th' : ρ) :
    σ → Std.HashSet Nat :=
  if p.hasEnabledAtoms then fun st => p.stateLabel th' st (enabledLabelsTr tr st)
  else fun st => p.stateLabel th' st []

def sysLabelOf [BEq l] [Hashable l]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l) (th' : ρ) :
    σ → Std.HashSet Nat :=
  sysLabelOfTr (sys.tr th) p th'

/-! ## One walk of `tr` per state, structurally

`sysStepsLabelled` and `sysLabelOf` each enumerate `sys.tr`, and with an `E(a)` in the property the search
needs both at every state it visits.

`sysStepOf` removes the need for two `sys.tr` calls.
LTLLib's routes now take `LSys.StepFn`(a state's steps and its atoms from one call)
so "one walk per state" is a property of the *type*. -/

/-- The steps of an already-enumerated outcome list. `sysStepsLabelledTr` with the walk factored out. -/
@[inline] def stepsOfOutcomes (outs : List (l × Veil.ExecutionOutcome Int σ))
    (edgeLabel? : Option (l → Std.HashSet Nat)) : Array (LTLLib.LStep Nat σ) :=
  match edgeLabel? with
  | none =>
    (outs.filterMap fun (_, o) => match o with
      | .success s' => some (emptyLetter, s')
      | _ => none).toArray
  | some edgeLabel =>
    (outs.filterMap fun (lbl, o) => match o with
      | .success s' => some (edgeLabel lbl, s')
      | _ => none).toArray

/-- The step-enabled labels of an already-enumerated outcome list. `enabledLabelsTr`, walk factored out. -/
@[inline] def enabledOfOutcomes [BEq l] [Hashable l]
    (outs : List (l × Veil.ExecutionOutcome Int σ)) : List l :=
  (outs.foldl (init := Std.HashSet.emptyWithCapacity) fun seen (lbl, o) =>
    match o with
    | .success _ => seen.insert lbl
    | _ => seen).toList

/-- The system callback: one `tr` walk gives a state's steps and its atoms. -/
def sysStepOf [BEq l] [Hashable l]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l) (th' : ρ) :
    LTLLib.LSys.StepFn Nat σ :=
  let edgeLabel? := edgeLabelling p
  let hasE := p.hasEnabledAtoms
  fun st =>
    let outs := sys.tr th st
    (stepsOfOutcomes outs edgeLabel?,
      p.stateLabel th' st (if hasE then enabledOfOutcomes outs else []))

omit [BEq σ] [Hashable σ] [LawfulBEq σ] [BEq l] [Hashable l] in
/-- It is the pair `sysStepsLabelled`/`sysLabelOf`, so every contract stated over those two transfers. -/
theorem sysStepOf_eq [BEq l] [Hashable l]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l) (th' : ρ) :
    sysStepOf sys p th'
      = fun st => (sysStepsLabelled sys (edgeLabelling p) st, sysLabelOf sys p th' st) := by
  funext st
  refine Prod.ext ?_ ?_
  · show stepsOfOutcomes (sys.tr th st) (edgeLabelling p) = _
    rw [sysStepsLabelled, sysStepsLabelledTr.eq_def]
    cases edgeLabelling p <;> rfl
  · show p.stateLabel th' st (if p.hasEnabledAtoms then enabledOfOutcomes (sys.tr th st) else []) = _
    rw [sysLabelOf, sysLabelOfTr]
    split <;> rfl

/-- Run `LTLLib.modelCheck` for a `liveness`-declared property `p` -/
def check
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (hinit : sys.initStates.all (bfsClosure (sysSucc sys) sys.initStates).contains = true)
    (hclosed : (bfsClosure (sysSucc sys) sys.initStates).toList.all
      (fun s => (sysSucc sys s).all (bfsClosure (sysSucc sys) sys.initStates).contains) = true) :
    LTLLib.EmptinessResult (σ × LTLLib.BAState) :=
  LTLLib.modelCheck (S := Std.HashSet (LTLLib.NNF Nat)) p.φ sys.initStates (sysSucc sys)
    (sysLabelOf sys p th)
    (finiteReach_of_closed (sysSucc sys) sys.initStates (bfsClosure (sysSucc sys) sys.initStates) hinit hclosed)

/-- Run `LTLLib.modelCheckDijkstra` for a `liveness`-declared property `p` -/
def checkDijkstra [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l) :
    LTLLib.EmptinessResult (σ × Nat) :=
  -- `LTLLib.modelCheckTGBA` reads a *labelled* system, where each step carries the atoms it itself
  -- contributes (for `T(a)`). The steps come from one pass over `tr`.
  --
  -- PERF: `sysSucc` and `sysLabel` are each entered exactly once per product state, because LTLLib's search
  -- walks a fused `expand` callback whose result the DFS frame caches (`GenericDFS.DFSStep.succMarks`).
  LTLLib.modelCheckTGBAOfStep p.φ sys.initStates (sysStepOf sys p th)

/-- Run `LTLLib.modelCheckNDFS` (nested DFS over the degeneralized automaton) for a `liveness`-declared
property `p`. Like `checkDijkstra` this route is labelled, so a `T(a)` atom is decided on the step that
carries it rather than on either endpoint. -/
def checkNDFS [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (hinit : sys.initStates.all (bfsClosure (sysSucc sys) sys.initStates).contains = true)
    (hclosed : (bfsClosure (sysSucc sys) sys.initStates).toList.all
      (fun s => (sysSucc sys s).all (bfsClosure (sysSucc sys) sys.initStates).contains) = true) :
    LTLLib.EmptinessResult (σ × LTLLib.TBAState) :=
  LTLLib.modelCheckNDFSOfStep p.φ sys.initStates (sysStepOf sys p th)
    (by simp only [sysStepOf_eq]
        rw [targets_sysStepsLabelled]
        exact finiteReach_of_closed (sysSucc sys) sys.initStates
          (bfsClosure (sysSucc sys) sys.initStates) hinit hclosed)

/-- Run `LTLLib.modelCheckUnderFairness` on the declared property as written. The router splits the negated
property at its conjunctions, and every conjunct that is a fairness in the sense of [LSFZ16] and flattens into
`LTL(F, G)` becomes acceptance marks and a region restriction on the product rather than reaching the tableau.

This route is *labelled*, so a hoisted fairness may mention `T(a)`. -/
def checkUnderFairness [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l) :
    LTLLib.EmptinessResult ((σ × Nat) × Bool) :=
  LTLLib.modelCheckUnderFairness p.φ sys.initStates
    (sysStepsLabelled sys (edgeLabelling p)) (sysLabelOf sys p th)

/-! ## When the prune takes its fast path

The prune is the faster route and the default.
What the test below still says is not whether the route is *sound* but whether it
is *free*: a hoisted `◇□` region that mentions an edge atom has to be committed before a report, which
costs an extra search level over the accepting SCC, while a region that does not is committable on the
first pass and nothing changes.

The detection is syntactic. Veil knows which atom indices are `T(…)`, and `LTLLib.regionsAvoid` checks
that no region mentions one.
This is the common case: written as an *assumption*, `SF(a)` and `WF(a)`
hoist to regions `¬E(a)` and `⊤`, which are state atoms, so the motivating workload pays nothing. -/

omit [BEq σ] [Hashable σ] [LawfulBEq σ] [BEq l] [Hashable l] in
/-- Every atom a labelled step contributes is a `T(…)` index.
The totalizing self-loop contributes none, and a real step contributes `edgeLabelOf p`'s output. -/
theorem steps_edgeAtom
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l) :
    ∀ s, ∀ st ∈ LTLLib.LSys.totalize (sysStepsLabelled sys (edgeLabelling p)) s,
      ∀ a ∈ st.1, p.isEdgeAtom a = true := by
  intro s st hst a ha
  -- with no `T(…)` every step reads `emptyLetter`, so there is nothing to classify
  rcases hlab : edgeLabelling p with _ | f
  · rw [hlab] at hst
    rcases LTLLib.LSys.mem_totalize.mp hst with h
    split at h
    · rw [h] at ha; simp at ha
    · obtain ⟨lbl, o, -, heq⟩ :
          ∃ lbl o, (lbl, o) ∈ sys.tr th s ∧
            (match o with
              | .success s' => some (emptyLetter, s')
              | _ => none) = some st := by
          simpa [sysStepsLabelled, sysStepsLabelledTr] using h
      cases o with
      | assertionFailure _ _ => simp at heq
      | divergence => simp at heq
      | success s' =>
        have hst1 : st.1 = emptyLetter := by
          simp only [Option.some.injEq] at heq; rw [← heq]
        rw [hst1] at ha; simp [emptyLetter] at ha
  · -- otherwise `f = p.edgeLabel`, and `isEdgeAtom_of_mem_edgeLabel` pins its output down
    have hf : f = p.edgeLabel := by
      unfold edgeLabelling at hlab; split at hlab
      · exact (Option.some.inj hlab).symm
      · exact absurd hlab (by simp)
    subst hf
    rw [hlab] at hst
    rcases LTLLib.LSys.mem_totalize.mp hst with h
    split at h
    · rw [h] at ha; simp at ha
    · obtain ⟨lbl, o, -, heq⟩ :
          ∃ lbl o, (lbl, o) ∈ sys.tr th s ∧
            (match o with
              | .success s' => some (p.edgeLabel lbl, s')
              | _ => none) = some st := by
          simpa [sysStepsLabelled, sysStepsLabelledTr] using h
      cases o with
      | assertionFailure _ _ => simp at heq
      | divergence => simp at heq
      | success s' =>
        have hst1 : st.1 = p.edgeLabel lbl := by
          simp only [Option.some.injEq] at heq; rw [← heq]
        rw [hst1] at ha
        exact p.isEdgeAtom_of_mem_edgeLabel lbl ha

/-- The regions `modelCheckFair` hands the prune: the first split, the re-hoisted conjuncts, and the
options each branch of the disjunctive hoist adds. -/
def pruneRegionsAvoidEdgeAtoms (p : LivenessProperty ρ σ l) : Bool :=
  let split := LTLLib.hoistFairness (p.φ.toNNF false).splitConj
  let rehoisted := LTLLib.rehoist split.2
  (LTLLib.branches rehoisted.2).all fun b =>
    LTLLib.regionsAvoid p.isEdgeAtom (split.1 ++ rehoisted.1 ++ b.1)

/-- Drop the region latch's Bool: the crossing reports in `(σ × Nat) × Bool` and the prune in `σ × Nat`,
so `checkFair` projects the latch away and both routes report in the same product. -/
def dropLatch {α β} : LTLLib.EmptinessResult ((σ × α) × β) → LTLLib.EmptinessResult (σ × α)
  | .empty n => .empty n
  | .nonEmpty stem loop => .nonEmpty (stem.map Prod.fst) (loop.map Prod.fst)

omit [BEq σ] [Hashable σ] [LawfulBEq σ] in
private theorem dropLatch_empty {α β} {r : LTLLib.EmptinessResult ((σ × α) × β)} {n : Nat}
    (h : dropLatch r = .empty n) : r = .empty n := by
  cases r with
  | empty m => simpa [dropLatch] using h
  | nonEmpty s l => simp [dropLatch] at h

omit [BEq σ] [Hashable σ] [LawfulBEq σ] in
private theorem dropLatch_nonEmpty {α β} {r : LTLLib.EmptinessResult ((σ × α) × β)}
    {stem loop : List (σ × α)} (h : dropLatch r = .nonEmpty stem loop) :
    ∃ s' l', r = .nonEmpty s' l' := by
  cases r with
  | empty n => simp [dropLatch] at h
  | nonEmpty s' l' => exact ⟨s', l', rfl⟩

/-- `modelCheckFair`, the default and fastest route: every fairness conjunct hoisted and decided per SCC. -/
def checkFair [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l) :
    LTLLib.EmptinessResult (σ × Nat) :=
  if pruneRegionsAvoidEdgeAtoms p then
    LTLLib.modelCheckFairOfStep p.φ sys.initStates (sysStepOf sys p th)
  else
    dropLatch (LTLLib.modelCheckFairFNFCrossOfStep p.φ sys.initStates (sysStepOf sys p th))

omit [BEq σ] [Hashable σ] [LawfulBEq σ] in
/-- `StateOnly` for every region every branch hands the prune. -/
theorem stateOnly_of_pruneRegionsAvoid
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (hprune : pruneRegionsAvoidEdgeAtoms p = true) :
    ∀ b ∈ LTLLib.branches (LTLLib.rehoist (LTLLib.hoistFairness (p.φ.toNNF false).splitConj).2).2,
      ∀ ds ∈ (LTLLib.hoistFairness (p.φ.toNNF false).splitConj).1 ++
          (LTLLib.rehoist (LTLLib.hoistFairness (p.φ.toNNF false).splitConj).2).1 ++ b.1,
      ∀ d ∈ ds, LTLLib.LSys.StateOnly (sysStepsLabelled sys (edgeLabelling p))
        (sysLabelOf sys p th) d.1.eval := by
  intro b hb
  exact LTLLib.stateOnly_of_regionsAvoid (steps_edgeAtom sys p)
    (List.all_eq_true.mp hprune b hb)

/-- Soundness of `checkFair`: an `.empty` result means every labelled run of the system satisfies `p.φ`. -/
theorem checkFair_empty_unsat [Inhabited σ] [LawfulHashable σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (hinit : sys.initStates.all (bfsClosure (sysSucc sys) sys.initStates).contains = true)
    (hclosed : (bfsClosure (sysSucc sys) sys.initStates).toList.all
      (fun s => (sysSucc sys s).all (bfsClosure (sysSucc sys) sys.initStates).contains) = true)
    {n : Nat} (h : checkFair sys p = .empty n) :
    ∀ ρ' : Nat → LTLLib.LSys.Edge Nat σ,
      (LTLLib.LSys.toSpec (sysStepsLabelled sys (edgeLabelling p)) sys.initStates
        (sysLabelOf sys p th)).isRun ρ' →
      LTLLib.Formula.directSatisfies (LTLLib.LSys.valuation (sysLabelOf sys p th) ρ') p.φ := by
  have hfr : LTLLib.FiniteReach sys.initStates
      (LTLLib.LSys.targets (sysStepsLabelled sys (edgeLabelling p))) := by
    rw [targets_sysStepsLabelled]
    exact finiteReach_of_closed (sysSucc sys) sys.initStates
      (bfsClosure (sysSucc sys) sys.initStates) hinit hclosed
  rw [checkFair] at h
  split at h
  · rw [sysStepOf_eq] at h
    exact LTLLib.modelCheckFair_empty_unsat p.φ sys.initStates _ _ hfr h
  · have h' := dropLatch_empty h
    have hx := LTLLib.modelCheckFairFNFCrossOfStep_empty_unsat
      (φ := p.φ) (sysInit := sys.initStates) (sysStep := sysStepOf sys p th)
      (by simpa only [sysStepOf_eq] using hfr) h'
    simpa only [sysStepOf_eq] using hx

/-- Completeness of `checkFair`: a `.nonEmpty` result yields a real labelled run violating `p.φ`. -/
theorem checkFair_nonEmpty_sat [Inhabited σ] [LawfulHashable σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (hinit : sys.initStates.all (bfsClosure (sysSucc sys) sys.initStates).contains = true)
    (hclosed : (bfsClosure (sysSucc sys) sys.initStates).toList.all
      (fun s => (sysSucc sys s).all (bfsClosure (sysSucc sys) sys.initStates).contains) = true)
    {stem loop : List (σ × Nat)}
    (h : checkFair sys p = .nonEmpty stem loop) :
    ∃ ρ' : Nat → LTLLib.LSys.Edge Nat σ,
      (LTLLib.LSys.toSpec (sysStepsLabelled sys (edgeLabelling p)) sys.initStates
        (sysLabelOf sys p th)).isRun ρ' ∧
      ¬ LTLLib.Formula.directSatisfies (LTLLib.LSys.valuation (sysLabelOf sys p th) ρ') p.φ := by
  rw [checkFair] at h
  split at h
  · rename_i hprune
    rw [sysStepOf_eq] at h
    exact LTLLib.modelCheckFair_nonEmpty_sat p.φ sys.initStates _ _
      (stateOnly_of_pruneRegionsAvoid sys p hprune) h
  · obtain ⟨s', l', hx⟩ := dropLatch_nonEmpty h
    have hc := LTLLib.modelCheckFairFNFCrossOfStep_nonEmpty_sat
      (φ := p.φ) (sysInit := sys.initStates) (sysStep := sysStepOf sys p th)
      (by rw [sysStepOf_eq]
          show LTLLib.FiniteReach _ (LTLLib.LSys.targets (sysStepsLabelled sys (edgeLabelling p)))
          rw [targets_sysStepsLabelled]
          exact finiteReach_of_closed (sysSucc sys) sys.initStates
            (bfsClosure (sysSucc sys) sys.initStates) hinit hclosed) hx
    simpa only [sysStepOf_eq] using hc

end Veil.LivenessMC
