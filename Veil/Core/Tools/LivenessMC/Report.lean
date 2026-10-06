module

public import Veil.Core.Tools.LivenessMC.LivenessMC
public import LTLLib

public section

namespace Veil.LivenessMC

variable {σ : Type} [BEq σ] [Hashable σ] [LawfulBEq σ]
variable {ρ l : Type} [BEq l] [Hashable l] {th : ρ}

/-- Render an `NNF` with atoms shown by their declared names, and `⊤ U ψ` and `⊥ R ψ` shown as `◇` and `□`. -/
private def showNNF (nm : Nat → String) : LTLLib.NNF Nat → String
  | .tt => "⊤"
  | .ff => "⊥"
  | .prop a => nm a
  | .nprop a => s!"¬{nm a}"
  | .and φ ψ => s!"({showNNF nm φ} ∧ {showNNF nm ψ})"
  | .or φ ψ => s!"({showNNF nm φ} ∨ {showNNF nm ψ})"
  | .next φ => s!"X {showNNF nm φ}"
  | .until .tt ψ => s!"◇{showNNF nm ψ}"
  | .until φ ψ => s!"({showNNF nm φ} U {showNNF nm ψ})"
  | .release .ff ψ => s!"□{showNNF nm ψ}"
  | .release φ ψ => s!"({showNNF nm φ} R {showNNF nm ψ})"

/-- The total acceptance marks a hoisted split carries, over every option of every conjunct. -/
private def markCount (dss : List (List (LTLLib.NNF.FairDisjunct Nat))) : Nat :=
  dss.foldl (init := 0) fun n ds =>
    ds.foldl (init := n) fun m (d : LTLLib.NNF.FairDisjunct Nat) => m + d.2.length

/-- The options a hoisted split offers, summed over its conjuncts. -/
private def optionCount (dss : List (List (LTLLib.NNF.FairDisjunct Nat))) : Nat :=
  dss.foldl (init := 0) fun n ds => n + ds.length

/-- What the translator ends up seeing, given the conjuncts a route kept. -/
private def keptDesc (nm : Nat → String) (cs : List (LTLLib.NNF Nat)) : String :=
  if cs.isEmpty then "the tableau gets ⊤"
  else s!"the tableau gets {String.intercalate " ∧ " (cs.map (showNNF nm))}"

/-- Explain how a `liveness` property written as `fairness → property` is routed: which conjuncts of the
assumption are hoisted onto the product, which stay in the property, and what the hoisted ones cost.
Nothing here affects checking.

The route is read off LTLLib's own split (`fairPruneSplits`, `fairCrossSplit`, `pruneApplicable`), not
re-derived here, so what this prints is what `checkFair` will actually run. -/
def explainFairness (p : LivenessProperty ρ σ l) : IO Unit := do
  let nm := fun i => match p.atoms[i]? with
    | some a => toString a.name
    | none => s!"atom{i}"
  let conjuncts := LTLLib.NNF.splitConj (p.φ.toNNF false)
  IO.println s!"{p.name}"
  IO.println s!"  property   {showNNF nm (p.φ.toNNF true)}"
  IO.println s!"  negated, it splits into {conjuncts.length} conjunct(s)"
  for c in conjuncts do
    let route := match c.classify with
      | .notFairness => "not a fairness"
      | .fgFragment => "fairness in LTL(F, G)"
      | .temporal => "fairness, outside LTL(F, G)"
    let cost := match LTLLib.hoistConjunct c with
      | some ds => s!"hoisted, {ds.length} disjunct(s), {ds.foldl (fun n (d : LTLLib.NNF.FairDisjunct Nat) => n + d.2.length) 0} mark(s)"
      | none => "kept, goes to the tableau"
    IO.println s!"    {showNNF nm c}"
    IO.println s!"      {route}, {cost}"
  -- Which route `checkFair` takes, and what that route will run.
  if pruneRegionsAvoidEdgeAtoms p then
    let splits := LTLLib.fairPruneSplits p.φ
    IO.println s!"  route      prune, {splits.length} run(s); no hoisted region mentions a T(…) atom"
    for (kept, dss) in splits do
      IO.println s!"    run      {dss.length} hoisted conjunct(s), {optionCount dss} option(s), \
{markCount dss} mark(s); {keptDesc nm kept}"
  else
    let (kept, ds) := LTLLib.fairCrossSplit p.φ
    IO.println s!"  route      crossing, {ds.length} latched check(s), \
{ds.foldl (fun n (d : LTLLib.NNF.FairDisjunct Nat) => n + d.2.length) 0} extra mark(s); a hoisted ◇□ \
region mentions a T(…) atom, which the prune cannot decide per SCC"
    IO.println s!"    kept     {keptDesc nm kept}"

def printCheckResult {α} [Repr σ] (sysName propName : String) :
    LTLLib.EmptinessResult (σ × α) → IO Unit
  | .empty n => IO.println s!"{sysName} ⊨ {propName} (explored {n} product states)"
  | .nonEmpty stem loop => IO.println
    s!"{sysName} ⊭ {propName}; counterexample\n\nstem={reprStr (stem.map Prod.fst)}\n\nloop={reprStr (loop.map Prod.fst)}"

end Veil.LivenessMC
