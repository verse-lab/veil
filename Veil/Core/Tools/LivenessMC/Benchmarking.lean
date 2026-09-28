import Veil.Core.Tools.LivenessMC.LivenessMC

namespace Veil.LivenessMC

variable {σ : Type} [BEq σ] [Hashable σ] [LawfulBEq σ]
variable {ρ l : Type} [BEq l] [Hashable l] {th : ρ}

/-! ## Benchmark instrumentation

`modelCheck`/`modelCheckTGBA` call back into Veil for two things: computing the successors of a
state (`sysSucc`, which *executes* every action instance) and computing a state's label
(`LivenessProperty.sysLabel`, which *decides* every atom instance). Both are the Veil-specific cost.

`timed`/`timedLabel` are identity wrappers whose `@[implemented_by]` impls accumulate wall-clock
time (and call/element counts) spent inside those callbacks into the refs below. A harness resets
the refs with `resetVeilTimers`, runs an instrumented `checkTimed`/`checkDijkstraTimed`, then reads
them back with `readVeilTimers` and compares against its own wall-clock total. See
`Examples/LivenessMC/MCDijkstraPerf.lean`. -/

initialize sysSuccNs : IO.Ref Nat ← IO.mkRef 0
initialize sysSuccElems : IO.Ref Nat ← IO.mkRef 0  -- total successors produced (also forces r)
initialize sysSuccCalls : IO.Ref Nat ← IO.mkRef 0  -- number of `sysSucc` invocations
@[noinline] private unsafe def timedImpl (f : σ → Array σ) : σ → Array σ := fun s =>
  unsafeBaseIO do
    let t0 ← IO.monoNanosNow
    let r := f s
    let sz := r.foldl (init := 0) fun n _ => n + 1
    let t1 ← IO.monoNanosNow
    sysSuccElems.modify (· + sz)
    sysSuccCalls.modify (· + 1)
    sysSuccNs.modify (· + (t1 - t0))
    return r
@[implemented_by timedImpl] private def timed (f : σ → Array σ) : σ → Array σ := f

@[noinline] private unsafe def timedStepsImpl (f : σ → Array (LTLLib.LStep Nat σ)) :
    σ → Array (LTLLib.LStep Nat σ) := fun s =>
  unsafeBaseIO do
    let t0 ← IO.monoNanosNow
    let r := f s
    let sz := r.foldl (init := 0) fun n _ => n + 1
    let t1 ← IO.monoNanosNow
    sysSuccElems.modify (· + sz)
    sysSuccCalls.modify (· + 1)
    sysSuccNs.modify (· + (t1 - t0))
    return r
@[implemented_by timedStepsImpl] private def timedSteps (f : σ → Array (LTLLib.LStep Nat σ)) :
    σ → Array (LTLLib.LStep Nat σ) := f

/-- `timed` for the **fused** system callback. With `sysStepOf` the steps and the label come from one
call, so there is no longer a succ/label split to report: the whole Veil cost lands in the `succ`
counters and `label` stays at zero. -/
@[noinline] private unsafe def timedStepFnImpl
    (f : LTLLib.LSys.StepFn Nat σ) : LTLLib.LSys.StepFn Nat σ := fun s =>
  unsafeBaseIO do
    let t0 ← IO.monoNanosNow
    let r := f s
    let sz := r.1.foldl (init := 0) fun n _ => n + 1
    let sz2 := r.2.fold (init := sz) fun n _ => n + 1
    let t1 ← IO.monoNanosNow
    sysSuccElems.modify (· + sz2)
    sysSuccCalls.modify (· + 1)
    sysSuccNs.modify (· + (t1 - t0))
    return r

@[implemented_by timedStepFnImpl] private def timedStepFn
    (f : LTLLib.LSys.StepFn Nat σ) : LTLLib.LSys.StepFn Nat σ := f

initialize sysLabelNs : IO.Ref Nat ← IO.mkRef 0
initialize sysLabelElems : IO.Ref Nat ← IO.mkRef 0  -- total atoms found to hold (also forces r)
initialize sysLabelCalls : IO.Ref Nat ← IO.mkRef 0  -- number of `sysLabel` invocations
@[noinline] private unsafe def timedLabelImpl (f : σ → Std.HashSet Nat) : σ → Std.HashSet Nat :=
  fun s =>
  unsafeBaseIO do
    let t0 ← IO.monoNanosNow
    let r := f s
    let sz := r.fold (init := 0) fun n _ => n + 1
    let t1 ← IO.monoNanosNow
    sysLabelElems.modify (· + sz)
    sysLabelCalls.modify (· + 1)
    sysLabelNs.modify (· + (t1 - t0))
    return r
@[implemented_by timedLabelImpl] private def timedLabel (f : σ → Std.HashSet Nat) :
    σ → Std.HashSet Nat := f

/-- A snapshot of the Veil-specific timers (nanoseconds and counts). -/
structure VeilTimers where
  succNs : Nat
  succCalls : Nat
  succElems : Nat
  labelNs : Nat
  labelCalls : Nat
  labelElems : Nat

def resetVeilTimers : IO Unit := do
  sysSuccNs.set 0; sysSuccElems.set 0; sysSuccCalls.set 0
  sysLabelNs.set 0; sysLabelElems.set 0; sysLabelCalls.set 0

def readVeilTimers : IO VeilTimers := do
  return {
    succNs := (← sysSuccNs.get), succCalls := (← sysSuccCalls.get), succElems := (← sysSuccElems.get),
    labelNs := (← sysLabelNs.get), labelCalls := (← sysLabelCalls.get), labelElems := (← sysLabelElems.get)
  }

/-- Instrumented `check`: both Veil callbacks are wrapped so
that `readVeilTimers` reports the time spent computing successors and labels. -/
def checkTimed
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (hinit : sys.initStates.all (bfsClosure (sysSucc sys) sys.initStates).contains = true)
    (hclosed : (bfsClosure (sysSucc sys) sys.initStates).toList.all
      (fun s => (sysSucc sys s).all (bfsClosure (sysSucc sys) sys.initStates).contains) = true) :
    LTLLib.EmptinessResult (σ × LTLLib.BAState) :=
  LTLLib.modelCheck (S := Std.HashSet (LTLLib.NNF Nat)) p.φ sys.initStates
    (timed (sysSucc sys)) (timedLabel (sysLabelOf sys p th))
    (finiteReach_of_closed (sysSucc sys) sys.initStates (bfsClosure (sysSucc sys) sys.initStates) hinit hclosed)

/-- Instrumented `checkNDFS` (nested DFS over the *labelled* degeneralized TBA product): see `checkTimed`.

Distinct from `checkTimed`, which benchmarks the legacy `LTLLib.modelCheck` (NNF tableau +
`nestedDFSChecker`) route with an *unlabelled* successor function. That route never touches `TBAProduct`,
so it cannot measure anything about edge labels. This one is the route `checkNDFS` ships. -/
def checkNDFSTimed [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (hinit : sys.initStates.all (bfsClosure (sysSucc sys) sys.initStates).contains = true)
    (hclosed : (bfsClosure (sysSucc sys) sys.initStates).toList.all
      (fun s => (sysSucc sys s).all (bfsClosure (sysSucc sys) sys.initStates).contains) = true) :
    LTLLib.EmptinessResult (σ × LTLLib.TBAState) :=
  LTLLib.modelCheckNDFS p.φ sys.initStates
    (timedSteps (sysStepsLabelled sys (edgeLabelling p))) (timedLabel (sysLabelOf sys p th))
    (by show LTLLib.FiniteReach _ (LTLLib.LSys.targets (sysStepsLabelled sys (edgeLabelling p)))
        rw [targets_sysStepsLabelled]
        exact finiteReach_of_closed (sysSucc sys) sys.initStates
          (bfsClosure (sysSucc sys) sys.initStates) hinit hclosed)

/-- Instrumented `checkDijkstra` (Dijkstra SCC / TGBA): see `checkTimed`. -/
def checkDijkstraTimed [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (hinit : sys.initStates.all (bfsClosure (sysSucc sys) sys.initStates).contains = true)
    (hclosed : (bfsClosure (sysSucc sys) sys.initStates).toList.all
      (fun s => (sysSucc sys s).all (bfsClosure (sysSucc sys) sys.initStates).contains) = true) :
    LTLLib.EmptinessResult (σ × Nat) :=
  LTLLib.modelCheckTGBA p.φ sys.initStates
    (timedSteps (sysStepsLabelled sys (edgeLabelling p))) (timedLabel (sysLabelOf sys p th))
    (by show LTLLib.FiniteReach _ (LTLLib.LSys.targets (sysStepsLabelled sys (edgeLabelling p)))
        rw [targets_sysStepsLabelled]
        exact finiteReach_of_closed (sysSucc sys) sys.initStates
          (bfsClosure (sysSucc sys) sys.initStates) hinit hclosed)

/-! ### Probe: The region scan's per-state callback cost -/
private partial def productClosure (succs : (σ × Nat) → Array (σ × Nat))
    (init : List (σ × Nat)) : Array (σ × Nat) :=
  go (Std.HashSet.ofList init) init.toArray
where
  go (seen : Std.HashSet (σ × Nat)) (frontier : Array (σ × Nat)) : Array (σ × Nat) :=
    if frontier.isEmpty then seen.toArray
    else
      let (seen, next) := frontier.foldl (init := (seen, (#[] : Array (σ × Nat))))
        fun acc s => (succs s).foldl (init := acc) fun (seen, next) t =>
          if seen.contains t then (seen, next) else (seen.insert t, next.push t)
      go seen next

/-- The reachable product states, computed with **uninstrumented** callbacks so the probe's own setup
does not pollute the counters. -/
def probeProductStates [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (tgba : LTLLib.TGBA Nat) : Array (σ × Nat) :=
  let ss := sysStepsLabelled sys (edgeLabelling p)
  let sl := sysLabelOf sys p th
  productClosure (LTLLib.TGBAProduct.getSuccessors tgba ss sl)
    (LTLLib.TGBAProduct.initialStates tgba sys.initStates)

/-- The top-level shape: one fused `expand` per state. Returns the total number of successors, so the
caller can report mean out-degree. -/
def probeFusedExpand [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (tgba : LTLLib.TGBA Nat) (states : Array (σ × Nat)) : Nat :=
  let ss := timedSteps (sysStepsLabelled sys (edgeLabelling p))
  let sl := timedLabel (sysLabelOf sys p th)
  states.foldl (init := 0) fun acc q =>
    let e := LTLLib.TGBAProduct.expand tgba ss sl q
    -- §13.17 widened `expand` to a triple; the marks are `.2.1` and the option payload `.2.2` is empty
    -- on this route, so forcing the first two arrays is still forcing all the work there is
    acc + e.1.size + (e.2.1.foldl (init := 0) fun n _ => n)

/-- The region shape, as `Candidate.expand` composes it: successors, then `keptEdgeMarks` once per
successor. `sccSuccs`'s state filter is omitted because it only drops elements and makes no callbacks. -/
def probeRegionExpand [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (tgba : LTLLib.TGBA Nat) (states : Array (σ × Nat)) : Nat :=
  let ss := timedSteps (sysStepsLabelled sys (edgeLabelling p))
  let sl := timedLabel (sysLabelOf sys p th)
  states.foldl (init := 0) fun acc q =>
    let out := LTLLib.TGBAProduct.keptSuccs tgba ss sl (fun _ => true) q
    let ms := out.map (LTLLib.TGBAProduct.keptEdgeMarks tgba ss sl (fun _ => true) q)
    acc + out.size + (ms.foldl (init := 0) fun n _ => n)

/-- The region shape **after** Level 1: the spec's own fused `keptExpand`, which is what
`Candidate.expand` now filters. Should read 1.0x on both callbacks, like the top-level scan. -/
def probeKeptExpand [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (tgba : LTLLib.TGBA Nat) (states : Array (σ × Nat)) : Nat :=
  let ss := timedSteps (sysStepsLabelled sys (edgeLabelling p))
  let sl := timedLabel (sysLabelOf sys p th)
  states.foldl (init := 0) fun acc q =>
    let e := LTLLib.TGBAProduct.keptExpand tgba ss sl (fun _ => true) q
    acc + e.1.size + (e.2.1.foldl (init := 0) fun n _ => n)

/-! ### Mode-split probes

`patOnly`, `prune` and `fair` all end in `modelCheckPruneSplit`; they differ only in which conjuncts
reach it. `patOnly` hoists the syntactically flat ones (`hoistFlat`), `prune` adds [LSFZ16] Appendix A
flattening, `fair` adds the disjunctive hoist on top.
These three instrumented copies let the modes be compared on one system with callback counts and explored-state counts. -/

/-- Instrumented `patOnly`: hoist only the syntactically flat conjuncts. -/
def checkFairDirectTimed [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l) :
    LTLLib.EmptinessResult (σ × Nat) :=
  LTLLib.modelCheckFairDirectOfStep p.φ sys.initStates (timedStepFn (sysStepOf sys p th))

/-- Instrumented `prune`: the fair-normal-form split, decided per SCC. -/
def checkFairFNFPruneTimed [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l) :
    LTLLib.EmptinessResult (σ × Nat) :=
  LTLLib.modelCheckFairFNFPruneOfStep p.φ sys.initStates (timedStepFn (sysStepOf sys p th))

/-- Instrumented `fair`: the prune plus the disjunctive hoist. The shipped default route. -/
def checkFairTimed [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l) :
    LTLLib.EmptinessResult (σ × Nat) :=
  LTLLib.modelCheckFairOfStep p.φ sys.initStates (timedStepFn (sysStepOf sys p th))

/-- The **top-level scan** of a prune route, run on its own.

`streettCheck` is `streettRun` followed by `pruneLoop`. This is the first half only, so the caller can
count the Veil callbacks it makes and subtract from the full route's total, the difference is exactly
what the candidate re-scans cost. Returns `(live, dead)` so the caller can force the result and report
the states the scan settled.

`kept`/`dss` are what the mode's hoisting produced: `patOnly` passes `hoistFlat`'s, `prune` passes
`hoistFairness` + `rehoist`'s. -/
def pruneScanOnly [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (kept : LTLLib.Formula Nat) (dss : List (List (LTLLib.NNF.FairDisjunct Nat))) : Nat × Nat :=
  match LTLLib.ltl3ba (kept.toNNF false) with
  | none => (0, 0)
  | some tgba =>
    let ss := timedSteps (sysStepsLabelled sys (edgeLabelling p))
    let sl := timedLabel (sysLabelOf sys p th)
    let cs := LTLLib.CompiledSpec.of (LTLLib.streettRSpecOf tgba ss sl dss)
    let r := LTLLib.streettRunF cs 0
      (LTLLib.TGBAProduct.expandWithOpts tgba ss sl cs)
      (LTLLib.TGBAProduct.initialStates tgba sys.initStates)
    (r.2.live.size, r.2.dead.size)

/-- Partition a Streett scan's Veil callbacks between the DFS and `streettPop`.

* `timeExpand = true`  — counts the DFS's own expansions, one per state discovered.
* `timeExpand = false` — counts what `streettPop` spends, i.e. `scanFrame`'s `internalEdges succs`.

The two should sum to the figure `pruneScanOnly` reports. -/
def pruneScanSplit [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (kept : LTLLib.Formula Nat) (dss : List (List (LTLLib.NNF.FairDisjunct Nat)))
    (which : Nat) : Nat × Nat :=
  match LTLLib.ltl3ba (kept.toNNF false) with
  | none => (0, 0)
  | some tgba =>
    let ssU := sysStepsLabelled sys (edgeLabelling p)
    let slU := sysLabelOf sys p th
    -- 0 = the DFS's `expand`; 1 = `succs`/`edgeMarks`, which reach only `ops.pop`; 2 = the spec's own
    -- region callbacks, which `scanFrame` -> `scanLetters` enters when it evaluates a region on an edge
    -- (that needs the edge's *letter*, hence `sysLabel`). The three are disjoint and must sum.
    let ssE := if which == 0 then timedSteps ssU else ssU
    let slE := if which == 0 then timedLabel slU else slU
    let ssC := if which == 2 then timedSteps ssU else ssU
    let slC := if which == 2 then timedLabel slU else slU
    let cs := LTLLib.CompiledSpec.of (LTLLib.streettRSpecOf tgba ssC slC dss)
    let r := LTLLib.streettRunF cs 0
      (LTLLib.TGBAProduct.expandWithOpts tgba ssE slE cs)
      (LTLLib.TGBAProduct.initialStates tgba sys.initStates)
    (r.2.live.size, r.2.dead.size)

/-- The compiled spec's shape, to divide the measured region-callback count by.

`scanLabels` walks the edge list and `scanOptionsAt` walks the options inside it, so the region
callbacks are one `regionSuccs` per (edge, option) plus the option's mark predicates, each of which
is another. -/
def specShape [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (kept : LTLLib.Formula Nat) (dss : List (List (LTLLib.NNF.FairDisjunct Nat))) :
    Nat × Nat × Nat :=
  match LTLLib.ltl3ba (kept.toNNF false) with
  | none => (0, 0, 0)
  | some tgba =>
    let ss := sysStepsLabelled sys (edgeLabelling p)
    let sl := sysLabelOf sys p th
    let cs := LTLLib.CompiledSpec.of (LTLLib.streettRSpecOf tgba ss sl dss)
    (cs.numOptions, cs.numOptMarks, cs.optMarks.foldl (init := 0) fun n m => n + m.size)

/-- Instrumented `checkUnderFairness` (cross / region latch): both Veil callbacks are wrapped so that
`readVeilTimers` reports the time spent computing successors and labels. -/
def checkUnderFairnessTimed [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ l)
    (hinit : sys.initStates.all (bfsClosure (sysSucc sys) sys.initStates).contains = true)
    (hclosed : (bfsClosure (sysSucc sys) sys.initStates).toList.all
      (fun s => (sysSucc sys s).all (bfsClosure (sysSucc sys) sys.initStates).contains) = true) :
    LTLLib.EmptinessResult ((σ × Nat) × Bool) :=
  LTLLib.modelCheckUnderFairness p.φ sys.initStates
    (timedSteps (sysStepsLabelled sys (edgeLabelling p))) (timedLabel (sysLabelOf sys p th))
    (by show LTLLib.FiniteReach _ (LTLLib.LSys.targets (sysStepsLabelled sys (edgeLabelling p)))
        rw [targets_sysStepsLabelled]
        exact finiteReach_of_closed (sysSucc sys) sys.initStates
          (bfsClosure (sysSucc sys) sys.initStates) hinit hclosed)

end Veil.LivenessMC
