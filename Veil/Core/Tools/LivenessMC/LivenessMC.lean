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
      (Veil.Transitions l Int σ) th) : σ → Array σ := fun st =>
  ((sys.tr th st).successes.map Prod.snd).toArray

/-- The labels (action instantiations) that can *fire* in `st`: those with a `.success` outcome.

"Step-enabled" (not "guard-enabled"). Reading `E(a)` off the successful outcomes keeps it coherent with `T(a)` on the graph the checker walks: `E(a)`
holds at `s` exactly when some `T(a)`-step leaves `s`.
Under the other reading `□(E(a) → ◇T(a))` would be unsatisfiable on a model whose action always faults,
reporting a fairness violation where the real problem is the assertion failure. -/
def enabledLabelsTr [BEq l] [Hashable l]
    (tr : σ → Veil.Transitions l Int σ) (st : σ) : List l :=
  ((tr st).successes.foldl (init := Std.HashSet.emptyWithCapacity) fun seen (lbl, _) =>
    seen.insert lbl).toList

def enabledLabels [BEq l] [Hashable l]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (st : σ) : List l :=
  enabledLabelsTr (sys.tr th) st

/-- One shared empty letter as a nullary definition so it is a closed constant allocated once -/
def emptyLetter : Std.HashSet Nat := ∅

/-- The edge labelling as **data**, not as a function: `none` when the property has no `T(…)`. -/
def edgeLabelling (p : LivenessProperty ρ σ l) : Option (l → Std.HashSet Nat) :=
  if p.hasEdgeAtoms then some p.edgeLabel else none

/-- The system as a *labelled* graph: each successful step paired with the atoms it contributes, which are
the `T(a)` atoms its label matches. -/
def sysStepsLabelledTr (tr : σ → Veil.Transitions l Int σ)
    (edgeLabel? : Option (l → Std.HashSet Nat)) :
    σ → Array (LTLLib.LStep Nat σ) :=
  match edgeLabel? with
  | none => fun st =>
    ((tr st).successes.map fun (_, s') => (emptyLetter, s')).toArray
  | some edgeLabel => fun st =>
    ((tr st).successes.map fun (lbl, s') => (edgeLabel lbl, s')).toArray

def sysStepsLabelled
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th)
    (edgeLabel? : Option (l → Std.HashSet Nat)) :
    σ → Array (LTLLib.LStep Nat σ) :=
  sysStepsLabelledTr (sys.tr th) edgeLabel?

omit [BEq σ] [Hashable σ] [LawfulBEq σ] [BEq l] [Hashable l] in
/-- Forgetting the letters gives back the unlabelled graph. -/
theorem targets_sysStepsLabelled
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th)
    (edgeLabel? : Option (l → Std.HashSet Nat)) :
    LTLLib.LSys.targets (sysStepsLabelled sys edgeLabel?) = sysSucc sys := by
  funext st
  cases edgeLabel? <;>
    · show Array.map Prod.snd _ = _
      apply Array.ext'
      simp only [sysStepsLabelled, sysStepsLabelledTr, sysSucc, Array.toList_map,
        List.toList_toArray, List.map_map]
      rfl

/-- The state labelling: the `⌜ … ⌝` atoms, plus the `E(a)` atoms. The enabled set costs a `tr` call, so it
is only computed when the property actually mentions an `E`. -/
def sysLabelOfTr [BEq l] [Hashable l]
    (tr : σ → Veil.Transitions l Int σ) (p : LivenessProperty ρ σ l) (th' : ρ) :
    σ → Std.HashSet Nat :=
  if p.hasEnabledAtoms then fun st => p.stateLabel th' st (enabledLabelsTr tr st)
  else fun st => p.stateLabel th' st []

def sysLabelOf [BEq l] [Hashable l]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l) (th' : ρ) :
    σ → Std.HashSet Nat :=
  sysLabelOfTr (sys.tr th) p th'

/-! ## One walk of `tr` per state, structurally

`sysStepsLabelled` and `sysLabelOf` each enumerate `sys.tr`, and with an `E(a)` in the property the search
needs both at every state it visits.

`sysStepOf` removes the need for two `sys.tr` calls.
LTLLib's routes now take `LSys.StepFn`(a state's steps and its atoms from one call)
so "one walk per state" is a property of the *type*. -/

/-- The steps of already-enumerated transitions. `sysStepsLabelledTr` with the walk factored out. -/
@[inline] def stepsOfOutcomes (outs : Veil.Transitions l Int σ)
    (edgeLabel? : Option (l → Std.HashSet Nat)) : Array (LTLLib.LStep Nat σ) :=
  match edgeLabel? with
  | none =>
    (outs.successes.map fun (_, s') => (emptyLetter, s')).toArray
  | some edgeLabel =>
    (outs.successes.map fun (lbl, s') => (edgeLabel lbl, s')).toArray

/-- The step-enabled labels of already-enumerated transitions. `enabledLabelsTr`, walk factored out. -/
@[inline] def enabledOfOutcomes [BEq l] [Hashable l]
    (outs : Veil.Transitions l Int σ) : List l :=
  (outs.successes.foldl (init := Std.HashSet.emptyWithCapacity) fun seen (lbl, _) =>
    seen.insert lbl).toList

/-- The system callback: one `tr` walk gives a state's steps and its atoms. -/
def sysStepOf [BEq l] [Hashable l]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l) (th' : ρ) :
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
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l) (th' : ρ) :
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
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l)
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
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l) :
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
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l)
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
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l) :
    LTLLib.EmptinessResult ((σ × Nat) × Bool) :=
  LTLLib.modelCheckUnderFairness p.φ sys.initStates
    (sysStepsLabelled sys (edgeLabelling p)) (sysLabelOf sys p th)

/-! ## When the prune takes its fast path

The prune is the faster route and the default. What the test below says is not whether the route is
*sound* but whether it is *free*: a hoisted `◇□` region that mentions an edge atom has to be committed
before a report, which costs an extra search level over the accepting SCC, while a region that does not is
committable on the first pass and nothing changes.

The decision itself is `LTLLib.modelCheckFairRoutedOfStep`, which tests the regions its own hoisting
produced. All Veil owes it is the classification — which atom indices are `T(…)` (`isEdgeAtom`) and the
proof that a step contributes nothing else (`steps_edgeAtom` below). That is the whole of the Veil side:
nothing here reproduces LTLLib's hoisting, so a change to how a route hoists cannot leave this stale.

The detection is syntactic, and the common case passes: written as an *assumption*, `SF(a)` and `WF(a)`
hoist to regions `¬E(a)` and `⊤`, which are state atoms, so the motivating workload pays nothing. -/

omit [BEq σ] [Hashable σ] [LawfulBEq σ] [BEq l] [Hashable l] in
/-- Every atom a labelled step contributes is a `T(…)` index.
The totalizing self-loop contributes none, and a real step contributes `edgeLabelOf p`'s output. -/
theorem steps_edgeAtom
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l) :
    ∀ s, ∀ st ∈ LTLLib.LSys.totalize (sysStepsLabelled sys (edgeLabelling p)) s,
      ∀ a ∈ st.1, p.isEdgeAtom a = true := by
  intro s st hst a ha
  -- with no `T(…)` every step reads `emptyLetter`, so there is nothing to classify
  rcases hlab : edgeLabelling p with _ | f
  · rw [hlab] at hst
    rcases LTLLib.LSys.mem_totalize.mp hst with h
    split at h
    · rw [h] at ha; simp at ha
    · obtain ⟨lbl, s', -, heq⟩ :
          ∃ lbl s', (lbl, s') ∈ (sys.tr th s).successes ∧ (emptyLetter, s') = st := by
          simpa [sysStepsLabelled, sysStepsLabelledTr] using h
      rw [← heq] at ha
      simp [emptyLetter] at ha
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
    · obtain ⟨lbl, s', -, heq⟩ :
          ∃ lbl s', (lbl, s') ∈ (sys.tr th s).successes ∧ (p.edgeLabel lbl, s') = st := by
          simpa [sysStepsLabelled, sysStepsLabelledTr] using h
      rw [← heq] at ha
      exact p.isEdgeAtom_of_mem_edgeLabel lbl ha

/-- Does every region the prune would receive avoid the `T(…)` atoms? `LTLLib.pruneApplicable` tests the
regions `modelCheckFair` actually hands the prune — the first split, the re-hoisted conjuncts, and the
options each branch of the disjunctive hoist adds — so this stays correct as the route's hoisting changes.
Veil supplies only the classification; `LTLLib.modelCheckFairRoutedOfStep` makes the choice. -/
def pruneRegionsAvoidEdgeAtoms (p : LivenessProperty ρ σ l) : Bool :=
  LTLLib.pruneApplicable p.isEdgeAtom p.φ

/-- The default route: `LTLLib.modelCheckFairRoutedOfStep`, which takes the prune (every fairness conjunct
hoisted and decided per SCC) and falls back to the crossing when a hoisted region mentions a `T(…)` atom.
Veil's whole contribution is `p.isEdgeAtom`, the classification of which atom indices a *step* can
contribute; the choice, and the proof that it discharges the prune's witness contract, are LTLLib's. -/
def checkFair [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l) :
    LTLLib.EmptinessResult (σ × Nat) :=
  LTLLib.modelCheckFairRoutedOfStep p.φ sys.initStates (sysStepOf sys p th) p.isEdgeAtom

/-- Soundness of `checkFair`: an `.empty` result means every labelled run of the system satisfies `p.φ`. -/
theorem checkFair_empty_unsat [Inhabited σ] [LawfulHashable σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l)
    (sysFR : LTLLib.FiniteReach sys.initStates
      (LTLLib.LSys.targets (sysStepsLabelled sys (edgeLabelling p))))
    {n : Nat} (h : checkFair sys p = .empty n) :
    ∀ ρ' : Nat → LTLLib.LSys.Edge Nat σ,
      (LTLLib.LSys.toSpec (sysStepsLabelled sys (edgeLabelling p)) sys.initStates
        (sysLabelOf sys p th)).isRun ρ' →
      LTLLib.Formula.directSatisfies (LTLLib.LSys.valuation (sysLabelOf sys p th) ρ') p.φ := by
  rw [checkFair] at h
  have hx := LTLLib.modelCheckFairRoutedOfStep_empty_unsat
    (φ := p.φ) (sysInit := sys.initStates) (sysStep := sysStepOf sys p th)
    (edgeAtom := p.isEdgeAtom) (by simpa only [sysStepOf_eq] using sysFR) h
  simpa only [sysStepOf_eq] using hx

/-- Completeness of `checkFair`: a `.nonEmpty` result yields a real labelled run violating `p.φ`. -/
theorem checkFair_nonEmpty_sat [Inhabited σ] [LawfulHashable σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l)
    (sysFR : LTLLib.FiniteReach sys.initStates
      (LTLLib.LSys.targets (sysStepsLabelled sys (edgeLabelling p))))
    {stem loop : List (σ × Nat)}
    (h : checkFair sys p = .nonEmpty stem loop) :
    ∃ ρ' : Nat → LTLLib.LSys.Edge Nat σ,
      (LTLLib.LSys.toSpec (sysStepsLabelled sys (edgeLabelling p)) sys.initStates
        (sysLabelOf sys p th)).isRun ρ' ∧
      ¬ LTLLib.Formula.directSatisfies (LTLLib.LSys.valuation (sysLabelOf sys p th) ρ') p.φ := by
  rw [checkFair] at h
  -- `steps_edgeAtom` is the premise the routed theorem asks of `p.isEdgeAtom`: every atom a step
  -- contributes is one it marks. Whichever route then ran, the witness is a real run.
  have hc := LTLLib.modelCheckFairRoutedOfStep_nonEmpty_sat
    (φ := p.φ) (sysInit := sys.initStates) (sysStep := sysStepOf sys p th)
    (edgeAtom := p.isEdgeAtom)
    (by simpa only [sysStepOf_eq] using steps_edgeAtom sys p)
    -- finiteness is owed only on the fallback branch, so the prune-routed case never reads it
    (fun _ => by simpa only [sysStepOf_eq] using sysFR) h
  simpa only [sysStepOf_eq] using hc

/-! ## Selecting a route

`checkFair` is the route a Veil user gets by default, and the only one whose soundness and
completeness are proved here (`checkFair_empty_unsat`, `checkFair_nonEmpty_sat`). The routes it is
built from are reachable through `#liveness_check (route := …)` so that the *ablation* — what each
technique in the pipeline buys — can be run through the same command a user runs, rather than
through a separate harness that reimplements the dispatch.

Consecutive pairs isolate one technique each (`ltl-bench/METHODOLOGY.md`):

| `Route`    | entry point                        | what it does with the fairness assumption |
|------------|------------------------------------|-------------------------------------------|
| `ndfs`     | `checkNDFS`                        | nothing: the whole formula is translated, degeneralized to a `TBA`, nested DFS |
| `dijkstra` | `LTLLib.modelCheckDijkstraOfStep`  | nothing: the same translation, SCC emptiness check on the TGBA product |
| `patOnly`  | `LTLLib.modelCheckFairDirectOfStep`| hoist only the conjuncts that are *syntactically* `□◇p`/`◇□p`, translate the rest, then prune |
| `crossing` | `LTLLib.modelCheckFairFNFCrossOfStep` | [LSFZ16]: hoist through the fair normal form and cross — `2ⁿ` emptiness checks |
| `prune`    | `LTLLib.modelCheckFairFNFPruneOfStep` | [SLDP09] on top of [LSFZ16]: the same split, decided per SCC instead of crossed — one pass |
| `fair`     | `checkFair`                        | the default: the prune plus the disjunctive hoist, routed |

`ndfs` is the route whose *definition* recurses on its `FiniteReach` certificate (LTLLib `tmp/FINITEREACH_FREE_DEFS.md` §4), so unlike the
other five it cannot simply be called. `Route.Certificate` makes that an explicit hypothesis of
`checkRoute`, which keeps the obligation where it belongs: the five free routes ask for `True`, and
whoever selects `ndfs` says in their own file how they discharge it. Discharging it honestly means
`native_decide`, i.e. a `bfsClosure` of the whole state space at elaboration time — which is the
work being measured, so a benchmark will want `sorry` there and will carry the `sorryAx` itself.
Nothing reachable from `checkFair` is affected either way.

References:
- [LSFZ16] Li, Song, Feng, Zhang. Verify LTL with Fairness Assumptions Efficiently. arXiv:1606.08116, 2016.
- [SLDP09] Sun, Liu, Dong, Pang. PAT: Towards Flexible Verification under Fairness. CAV 2009.
-/

/-- Which search `#liveness_check` runs. `fair` is the default and the only proved one; the rest are
the stages it is built from, selectable for the ablation. See the table above. -/
inductive Route where
  | ndfs
  | dijkstra
  | patOnly
  | crossing
  | prune
  | fair
  deriving Repr, DecidableEq, Inhabited

def Route.name : Route → String
  | .ndfs => "ndfs"
  | .dijkstra => "dijkstra"
  | .patOnly => "patOnly"
  | .crossing => "crossing"
  | .prune => "prune"
  | .fair => "fair"

/-- Whether the route has to be handed a `FiniteReach` certificate before it will run. -/
def Route.needsFiniteReach : Route → Bool
  | .ndfs => true
  | _ => false

/-- Every route reports in its own product, and the caller only ever wants the system half of a
lasso, so a route's result is projected to `σ` before it leaves `checkRoute`. -/
private def projectStates {P : Type} (f : P → σ) :
    LTLLib.EmptinessResult P → LTLLib.EmptinessResult σ :=
  LTLLib.EmptinessResult.map f

/-- What a route must be handed before it can run, as a function of the route, so that selecting one
of the five `FiniteReach`-free routes costs nothing.

`ndfs` asks for the two decidable facts that `finiteReach_of_closed` turns into a `FiniteReach`
witness: the `bfsClosure` of the system contains every initial state, and it is closed under
successors. Deciding them runs a full exploration of the state space, so this is a real cost and
not a formality, which is why it is visible in the type rather than hidden in the route.

Every other route gets `True`, and `RouteCertificate` makes that automatic, so no caller of the
shipped `fair` route sees this at all. -/
def Route.Certificate [Inhabited σ] (route : Route)
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) : Prop :=
  match route with
  | .ndfs =>
    sys.initStates.all (bfsClosure (sysSucc sys) sys.initStates).contains = true ∧
    (bfsClosure (sysSucc sys) sys.initStates).toList.all
      (fun s => (sysSucc sys s).all (bfsClosure (sysSucc sys) sys.initStates).contains) = true
  | _ => True

/-- A route's certificate, as an instance, so that selecting one of the five free routes needs no
argument and selecting `ndfs` cannot be done by accident. There is an instance for each free route
and none for `ndfs`: a caller that wants `ndfs` has to supply `⟨…⟩` itself, and whatever it uses to
prove the two facts — `native_decide`, or a `sorry` in a benchmark — is recorded against that
caller rather than against anything Veil ships. -/
class RouteCertificate [Inhabited σ] (route : Route)
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) where
  cert : route.Certificate sys

omit [LawfulBEq σ] [BEq l] [Hashable l] in
/-- `ndfs`'s certificate from the conjunction of its two facts, stated without the `Route.Certificate`
indirection so that a caller's tactic sees a plain goal about `bfsClosure`. This is the only way to
build one: `ndfs` has no instance. -/
theorem RouteCertificate.ofClosure [Inhabited σ]
    {sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th}
    (h : sys.initStates.all (bfsClosure (sysSucc sys) sys.initStates).contains = true ∧
      (bfsClosure (sysSucc sys) sys.initStates).toList.all
        (fun s => (sysSucc sys s).all (bfsClosure (sysSucc sys) sys.initStates).contains) = true) :
    RouteCertificate .ndfs sys := ⟨h⟩

instance [Inhabited σ] {sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
    (Veil.Transitions l Int σ) th} : RouteCertificate .dijkstra sys := ⟨trivial⟩
instance [Inhabited σ] {sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
    (Veil.Transitions l Int σ) th} : RouteCertificate .patOnly sys := ⟨trivial⟩
instance [Inhabited σ] {sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
    (Veil.Transitions l Int σ) th} : RouteCertificate .crossing sys := ⟨trivial⟩
instance [Inhabited σ] {sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
    (Veil.Transitions l Int σ) th} : RouteCertificate .prune sys := ⟨trivial⟩
instance [Inhabited σ] {sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
    (Veil.Transitions l Int σ) th} : RouteCertificate .fair sys := ⟨trivial⟩

/-- `patOnly` and `prune` run unrouted, so they must not be given a property whose hoisted regions
mention a `T(a)`: the prune's witness contract (`LSys.StateOnly`, LTLLib `EdgeLabels.md` §17) fails
there and the report could name a lasso that no single run takes. `checkFair` makes that decision
internally; here it is made before the call, and such a property falls back to the crossing, which
needs no such guard. The common case passes: `SF(a)`/`WF(a)` written as assumptions hoist to the
state regions `¬E(a)` and `⊤`. -/
def checkRoute [Inhabited σ] (route : Route)
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l)
    [cert : RouteCertificate route sys] :
    LTLLib.EmptinessResult σ :=
  let init := sys.initStates
  let step := sysStepOf sys p th
  -- `crossing` was a `let` here, bound before the `match`. It is used by three branches only, but
  -- the compiler evaluated it on **every** route, so each route paid a full `2^n` crossing on top
  -- of its own search. Measured 2026-10-10 on `sfHub` n=12 `Goal`: `fair` 0.54 ms -> 2342 ms,
  -- which is the crossing's 2326 ms plus `fair`'s own 0.54 ms, and at n=22, where the crossing
  -- times out, `fair`/`prune`/`patOnly` timed out with it -- inverting the headline claim. The
  -- prediction `new = old(crossing) + old(route)` held on 208 of 241 measured rows within 25%.
  -- Inlined into the three branches that need it so the other routes never build it. Inlining
  -- rather than thunking keeps the `.fair` branch's term unchanged, so `checkRoute_fair` below
  -- still closes by `rfl`.
  match route, cert.cert with
  | .ndfs, ⟨hinit, hclosed⟩ =>
    projectStates Prod.fst (checkNDFS sys p hinit hclosed)
  | .dijkstra, _ => projectStates Prod.fst (LTLLib.modelCheckDijkstraOfStep p.φ init step)
  | .crossing, _ =>
    projectStates (fun q => q.1.1) (LTLLib.modelCheckFairFNFCrossOfStep p.φ init step)
  | .patOnly, _ =>
    if pruneRegionsAvoidEdgeAtoms p then
      projectStates Prod.fst (LTLLib.modelCheckFairDirectOfStep p.φ init step)
    else projectStates (fun q => q.1.1) (LTLLib.modelCheckFairFNFCrossOfStep p.φ init step)
  | .prune, _ =>
    if pruneRegionsAvoidEdgeAtoms p then
      projectStates Prod.fst (LTLLib.modelCheckFairFNFPruneOfStep p.φ init step)
    else projectStates (fun q => q.1.1) (LTLLib.modelCheckFairFNFCrossOfStep p.φ init step)
  | .fair, _ => projectStates Prod.fst (checkFair sys p)

/-- On the default route, `checkRoute` is `checkFair` up to the projection every caller applies
anyway, so `checkFair_empty_unsat` and `checkFair_nonEmpty_sat` transfer to it unchanged. -/
theorem checkRoute_fair [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l) :
    checkRoute .fair sys p = LTLLib.EmptinessResult.map Prod.fst (checkFair sys p) := by
  unfold checkRoute projectStates; rfl

end Veil.LivenessMC
