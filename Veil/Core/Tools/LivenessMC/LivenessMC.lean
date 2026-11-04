module

public import Veil.Core.Tools.LivenessMC.Interface
public import Lasso.ModelCheck

public section

namespace Veil.LivenessMC

variable {σ : Type} [BEq σ] [Hashable σ] [LawfulBEq σ]


/-- A finite closed superset of the reachable states, by exploration. -/
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
    Lasso.FiniteReach initialStates succs := by
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

/-- The labels (action instantiations) that can fire in `st`, those with a `.success` outcome. Step-enabled, not
guard-enabled, which keeps `Enabled a` coherent with `⟨a⟩`: `Enabled a` holds at `s` exactly when some `⟨a⟩`-step leaves `s`. -/
def enabledLabelsTr [BEq l] [Hashable l]
    (tr : σ → Veil.Transitions l Int σ) (st : σ) : List l :=
  ((tr st).successes.foldl (init := Std.HashSet.emptyWithCapacity) fun seen (lbl, _) =>
    seen.insert lbl).toList

def enabledLabels [BEq l] [Hashable l]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (st : σ) : List l :=
  enabledLabelsTr (sys.tr th) st

/-- One shared empty letter, a closed constant allocated once. -/
def emptyLetter : Std.HashSet Nat := ∅

/-- The edge labelling as data, `none` when the property has no `⟨…⟩`. -/
def edgeLabelling (p : LivenessProperty ρ σ l) : Option (l → Std.HashSet Nat) :=
  if p.hasEdgeAtoms then some p.edgeLabel else none

/-- The system as a labelled graph, each successful step paired with the `⟨a⟩` atoms its label matches. -/
def sysStepsLabelledTr (tr : σ → Veil.Transitions l Int σ)
    (edgeLabel? : Option (l → Std.HashSet Nat)) :
    σ → Array (Lasso.LStep Nat σ) :=
  match edgeLabel? with
  | none => fun st =>
    ((tr st).successes.map fun (_, s') => (emptyLetter, s')).toArray
  | some edgeLabel => fun st =>
    ((tr st).successes.map fun (lbl, s') => (edgeLabel lbl, s')).toArray

def sysStepsLabelled
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th)
    (edgeLabel? : Option (l → Std.HashSet Nat)) :
    σ → Array (Lasso.LStep Nat σ) :=
  sysStepsLabelledTr (sys.tr th) edgeLabel?

omit [BEq σ] [Hashable σ] [LawfulBEq σ] [BEq l] [Hashable l] in
/-- Forgetting the letters gives back the unlabelled graph. -/
theorem targets_sysStepsLabelled
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th)
    (edgeLabel? : Option (l → Std.HashSet Nat)) :
    Lasso.LSys.targets (sysStepsLabelled sys edgeLabel?) = sysSucc sys := by
  funext st
  cases edgeLabel? <;>
    · show Array.map Prod.snd _ = _
      apply Array.ext'
      simp only [sysStepsLabelled, sysStepsLabelledTr, sysSucc, Array.toList_map,
        List.toList_toArray, List.map_map]
      rfl

/-- The state labelling, the `⌜ … ⌝` atoms plus the `Enabled a` atoms. The enabled set costs a `tr` call, so it is computed only
when the property mentions an `Enabled`. -/
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

/-! ## One walk of `tr` per state

`sysStepsLabelled` and `sysLabelOf` each enumerate `sys.tr`, and with an `Enabled a` in the property the search needs both at
every state it visits. `sysStepOf` gives a state's steps and its atoms from one call. -/

/-- The steps of already-enumerated transitions. -/
@[inline] def stepsOfOutcomes (outs : Veil.Transitions l Int σ)
    (edgeLabel? : Option (l → Std.HashSet Nat)) : Array (Lasso.LStep Nat σ) :=
  match edgeLabel? with
  | none =>
    (outs.successes.map fun (_, s') => (emptyLetter, s')).toArray
  | some edgeLabel =>
    (outs.successes.map fun (lbl, s') => (edgeLabel lbl, s')).toArray

/-- The step-enabled labels of already-enumerated transitions. -/
@[inline] def enabledOfOutcomes [BEq l] [Hashable l]
    (outs : Veil.Transitions l Int σ) : List l :=
  (outs.successes.foldl (init := Std.HashSet.emptyWithCapacity) fun seen (lbl, _) =>
    seen.insert lbl).toList

/-- The system callback, one `tr` walk gives a state's steps and its atoms. -/
def sysStepOf [BEq l] [Hashable l]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l) (th' : ρ) :
    Lasso.LSys.StepFn Nat σ :=
  let edgeLabel? := edgeLabelling p
  let hasE := p.hasEnabledAtoms
  fun st =>
    let outs := sys.tr th st
    (stepsOfOutcomes outs edgeLabel?,
      p.stateLabel th' st (if hasE then enabledOfOutcomes outs else []))

omit [BEq σ] [Hashable σ] [LawfulBEq σ] [BEq l] [Hashable l] in
/-- `sysStepOf` is the pair `sysStepsLabelled` and `sysLabelOf`. -/
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

/-- Run `Lasso.modelCheckDijkstra` for the property `p`. -/
def checkDijkstra [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l) :
    Lasso.EmptinessResult (σ × Nat) :=
  Lasso.modelCheckTGBAOfStep p.φ sys.initStates (sysStepOf sys p th)

/-- Run `Lasso.modelCheckNDFS`, nested DFS over the degeneralized automaton, for the property `p`. -/
def checkNDFS [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l)
    (hinit : sys.initStates.all (bfsClosure (sysSucc sys) sys.initStates).contains = true)
    (hclosed : (bfsClosure (sysSucc sys) sys.initStates).toList.all
      (fun s => (sysSucc sys s).all (bfsClosure (sysSucc sys) sys.initStates).contains) = true) :
    Lasso.EmptinessResult (σ × Lasso.TBAState) :=
  Lasso.modelCheckNDFSOfStep p.φ sys.initStates (sysStepOf sys p th)
    (by simp only [sysStepOf_eq]
        rw [targets_sysStepsLabelled]
        exact finiteReach_of_closed (sysSucc sys) sys.initStates
          (bfsClosure (sysSucc sys) sys.initStates) hinit hclosed)

/-! ## When the prune takes its fast path

The prune is the faster route and the default. A hoisted `◇□` region that mentions an edge atom has to be committed before a
report, which costs an extra search level over the accepting SCC, while a region that does not is committable on the first
pass. The decision is `Lasso.modelCheckFairRoutedOfStep`'s, Veil owes it only the classification of which atom indices are
`⟨…⟩` and the proof that a step contributes nothing else. -/

omit [BEq σ] [Hashable σ] [LawfulBEq σ] [BEq l] [Hashable l] in
/-- Every atom a labelled step contributes is a `⟨…⟩` index. -/
theorem steps_edgeAtom
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l) :
    ∀ s, ∀ st ∈ Lasso.LSys.totalize (sysStepsLabelled sys (edgeLabelling p)) s,
      ∀ a ∈ st.1, p.isEdgeAtom a = true := by
  intro s st hst a ha
  -- with no `⟨…⟩` every step reads `emptyLetter`, so there is nothing to classify
  rcases hlab : edgeLabelling p with _ | f
  · rw [hlab] at hst
    rcases Lasso.LSys.mem_totalize.mp hst with h
    split at h
    · rw [h] at ha; simp at ha
    · obtain ⟨lbl, s', -, heq⟩ :
          ∃ lbl s', (lbl, s') ∈ (sys.tr th s).successes ∧ (emptyLetter, s') = st := by
          simpa [sysStepsLabelled, sysStepsLabelledTr] using h
      rw [← heq] at ha
      simp [emptyLetter] at ha
  · -- otherwise `f = p.edgeLabel`
    have hf : f = p.edgeLabel := by
      unfold edgeLabelling at hlab; split at hlab
      · exact (Option.some.inj hlab).symm
      · exact absurd hlab (by simp)
    subst hf
    rw [hlab] at hst
    rcases Lasso.LSys.mem_totalize.mp hst with h
    split at h
    · rw [h] at ha; simp at ha
    · obtain ⟨lbl, s', -, heq⟩ :
          ∃ lbl s', (lbl, s') ∈ (sys.tr th s).successes ∧ (p.edgeLabel lbl, s') = st := by
          simpa [sysStepsLabelled, sysStepsLabelledTr] using h
      rw [← heq] at ha
      exact p.isEdgeAtom_of_mem_edgeLabel lbl ha

/-- Does every region the prune would receive avoid the `⟨…⟩` atoms? -/
def pruneRegionsAvoidEdgeAtoms (p : LivenessProperty ρ σ l) : Bool :=
  Lasso.pruneApplicable p.isEdgeAtom p.φ

/-- The default route, `Lasso.modelCheckFairRoutedOfStep`, which takes the prune, every fairness conjunct hoisted and
decided per SCC, and falls back to the crossing when a hoisted region mentions a `⟨…⟩` atom. -/
def checkFair [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l) :
    Lasso.EmptinessResult (σ × Nat) :=
  Lasso.modelCheckFairRoutedOfStep p.φ sys.initStates (sysStepOf sys p th) p.isEdgeAtom

/-- Soundness of `checkFair`: an `.empty` result means every labelled run of the system satisfies `p.φ`. -/
theorem checkFair_empty_unsat [Inhabited σ] [LawfulHashable σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l)
    (sysFR : Lasso.FiniteReach sys.initStates
      (Lasso.LSys.targets (sysStepsLabelled sys (edgeLabelling p))))
    {n : Nat} (h : checkFair sys p = .empty n) :
    ∀ ρ' : Nat → Lasso.LSys.Edge Nat σ,
      (Lasso.LSys.toSpec (sysStepsLabelled sys (edgeLabelling p)) sys.initStates
        (sysLabelOf sys p th)).isRun ρ' →
      Lasso.Formula.directSatisfies (Lasso.LSys.valuation (sysLabelOf sys p th) ρ') p.φ := by
  rw [checkFair] at h
  have hx := Lasso.modelCheckFairRoutedOfStep_empty_unsat
    (φ := p.φ) (sysInit := sys.initStates) (sysStep := sysStepOf sys p th)
    (edgeAtom := p.isEdgeAtom) (by simpa only [sysStepOf_eq] using sysFR) h
  simpa only [sysStepOf_eq] using hx

/-- Completeness of `checkFair`: a `.nonEmpty` result yields a real labelled run violating `p.φ`, whose
`i`-th state is the `i`-th state of the reported lasso: `stem`, then `loop.tail` repeated. -/
theorem checkFair_nonEmpty_sat [Inhabited σ] [LawfulHashable σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l)
    (sysFR : Lasso.FiniteReach sys.initStates
      (Lasso.LSys.targets (sysStepsLabelled sys (edgeLabelling p))))
    {stem loop : List (σ × Nat)}
    (h : checkFair sys p = .nonEmpty stem loop) :
    ∃ ρ' : Nat → Lasso.LSys.Edge Nat σ,
      (Lasso.LSys.toSpec (sysStepsLabelled sys (edgeLabelling p)) sys.initStates
        (sysLabelOf sys p th)).isRun ρ' ∧
      ¬ Lasso.Formula.directSatisfies (Lasso.LSys.valuation (sysLabelOf sys p th) ρ') p.φ ∧
      ∀ i, Lasso.lassoAt (stem.map Prod.fst) (loop.tail.map Prod.fst) i = some (ρ' i).1 := by
  rw [checkFair] at h
  have hc := Lasso.modelCheckFairRoutedOfStep_nonEmpty_sat
    (φ := p.φ) (sysInit := sys.initStates) (sysStep := sysStepOf sys p th)
    (edgeAtom := p.isEdgeAtom)
    (by simpa only [sysStepOf_eq] using steps_edgeAtom sys p)
    -- finiteness is owed only on the fallback branch, so the prune-routed case never reads it
    (fun _ => by simpa only [sysStepOf_eq] using sysFR) h
  simpa only [sysStepOf_eq, Lasso.lassoAt_map] using hc

/-! ## Routes

| `Route`    | entry point                           | search |
|------------|---------------------------------------|--------|
| `ndfs`     | `checkNDFS`                           | whole formula, degeneralized `TBA`, nested DFS |
| `dijkstra` | `Lasso.modelCheckDijkstraOfStep`     | whole formula, SCC emptiness check on the TGBA product |
| `patOnly`  | `Lasso.modelCheckFairDirectOfStep`   | syntactic `□◇p`/`◇□p` conjuncts hoisted, then pruned |
| `crossing` | `Lasso.modelCheckFairFNFCrossOfStep` | fair normal form [LSFZ16], one check per combination of disjuncts |
| `prune`    | `Lasso.modelCheckFairFNFPruneOfStep` | fair normal form [LSFZ16], decided per SCC [SLDP09] |
| `fair`     | `checkFair`                           | default |

References:
- [LSFZ16] Li, Song, Feng, Zhang. Verify LTL with Fairness Assumptions Efficiently. arXiv:1606.08116, 2016.
- [SLDP09] Sun, Liu, Dong, Pang. PAT: Towards Flexible Verification under Fairness. CAV 2009.
-/

/-- The search run by `#temporal_check`. -/
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

/-- Whether the route needs a `FiniteReach` certificate. -/
def Route.needsFiniteReach : Route → Bool
  | .ndfs => true
  | _ => false

/-- Project a route's result to system states. -/
private def projectStates {P : Type} (f : P → σ) :
    Lasso.EmptinessResult P → Lasso.EmptinessResult σ :=
  Lasso.EmptinessResult.map f

/-- The precondition of a route. For `ndfs`: the `bfsClosure` of the system contains every initial
state and is closed under successors. `True` otherwise. -/
def Route.Certificate [Inhabited σ] (route : Route)
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) : Prop :=
  match route with
  | .ndfs =>
    sys.initStates.all (bfsClosure (sysSucc sys) sys.initStates).contains = true ∧
    (bfsClosure (sysSucc sys) sys.initStates).toList.all
      (fun s => (sysSucc sys s).all (bfsClosure (sysSucc sys) sys.initStates).contains) = true
  | _ => True

/-- A proof of `route.Certificate sys`. Every route except `ndfs` has an instance. -/
class RouteCertificate [Inhabited σ] (route : Route)
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) where
  cert : route.Certificate sys

omit [LawfulBEq σ] [BEq l] [Hashable l] in
/-- The certificate of `ndfs`. -/
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

/-- Run `route` on `p`. `patOnly` and `prune` fall back to `crossing` when a hoisted region mentions
a `⟨…⟩` atom. -/
def checkRoute [Inhabited σ] (route : Route)
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l)
    [cert : RouteCertificate route sys] :
    Lasso.EmptinessResult σ :=
  let init := sys.initStates
  let step := sysStepOf sys p th
  match route, cert.cert with
  | .ndfs, ⟨hinit, hclosed⟩ =>
    projectStates Prod.fst (checkNDFS sys p hinit hclosed)
  | .dijkstra, _ => projectStates Prod.fst (Lasso.modelCheckDijkstraOfStep p.φ init step)
  | .crossing, _ =>
    projectStates (fun q => q.1.1) (Lasso.modelCheckFairFNFCrossOfStep p.φ init step)
  | .patOnly, _ =>
    if pruneRegionsAvoidEdgeAtoms p then
      projectStates Prod.fst (Lasso.modelCheckFairDirectOfStep p.φ init step)
    else projectStates (fun q => q.1.1) (Lasso.modelCheckFairFNFCrossOfStep p.φ init step)
  | .prune, _ =>
    if pruneRegionsAvoidEdgeAtoms p then
      projectStates Prod.fst (Lasso.modelCheckFairFNFPruneOfStep p.φ init step)
    else projectStates (fun q => q.1.1) (Lasso.modelCheckFairFNFCrossOfStep p.φ init step)
  | .fair, _ => projectStates Prod.fst (checkFair sys p)

/-- On `fair`, `checkRoute` is `checkFair` projected to system states. -/
theorem checkRoute_fair [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (Veil.Transitions l Int σ) th) (p : LivenessProperty ρ σ l) :
    checkRoute .fair sys p = Lasso.EmptinessResult.map Prod.fst (checkFair sys p) := by
  unfold checkRoute projectStates; rfl

end Veil.LivenessMC
