module

public import Veil.Core.Tools.LivenessMC.LivenessMC

/-! # The positive control of `VeilTest/TrustAudit.lean`

`checkFair` with its system callback behind `@[implemented_by]`. The audit must flag it, or it is not looking at
anything. The implementation is the callback itself, so nothing here is `unsafe`. -/

public section

namespace VeilTest.TrustAudit

open Veil Veil.LivenessMC

variable {σ : Type} [BEq σ] [Hashable σ] [LawfulBEq σ]
variable {ρ l : Type} [BEq l] [Hashable l] {th : ρ}

private def tracedImpl (f : Lasso.LSys.StepFn Nat σ) : Lasso.LSys.StepFn Nat σ := f

@[implemented_by tracedImpl] private def traced (f : Lasso.LSys.StepFn Nat σ) : Lasso.LSys.StepFn Nat σ := f

/-- `checkFair`, with the system callback behind `@[implemented_by]`. -/
def checkFairTraced [Inhabited σ]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l (Veil.Transitions l Int σ) th)
    (p : LivenessProperty ρ σ l) : Lasso.EmptinessResult (σ × Nat) :=
  Lasso.modelCheckFairRoutedOfStep p.φ sys.initStates (traced (sysStepOf sys p th)) p.isEdgeAtom

end VeilTest.TrustAudit
