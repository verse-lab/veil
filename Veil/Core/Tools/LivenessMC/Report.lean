import Veil.Core.Tools.LivenessMC.Interface
import LTLLib

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

/-- Explain how a `liveness` property written as `fairness → property` is routed: which conjuncts of the
assumption are hoisted onto the product, which stay in the property, and what the hoisted ones cost. Nothing
here affects checking, it only reports what `checkUnderFairness` would do. -/
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
  let hoisted := LTLLib.hoistFairness conjuncts
  let ds := LTLLib.NNF.crossAllDNF hoisted.1
  let left := if hoisted.2.isEmpty then "nothing left, the tableau gets ⊤" else s!"{hoisted.2.length} conjunct(s) left for the tableau"
  IO.println s!"  total      {ds.length} emptiness check(s), \
{ds.foldl (fun n (d : LTLLib.NNF.FairDisjunct Nat) => n + d.2.length) 0} extra mark(s), {left}"

def printCheckResult {α} [Repr σ] (sysName propName : String) :
    LTLLib.EmptinessResult (σ × α) → IO Unit
  | .empty n => IO.println s!"{sysName} ⊨ {propName} (explored {n} product states)"
  | .nonEmpty stem loop => IO.println
    s!"{sysName} ⊭ {propName}; counterexample\n\nstem={reprStr (stem.map Prod.fst)}\n\nloop={reprStr (loop.map Prod.fst)}"

end Veil.LivenessMC
