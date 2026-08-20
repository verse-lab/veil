module

public import Veil.Core.Tools.LivenessMC.Interface
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

variable {ρ l : Type} {th : ρ}


def sysSucc
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) : σ → Array σ := fun st =>
  ((sys.tr th st).filterMap fun (_, o) => match o with
    | .success s' => some s'
    | _ => none).toArray

/-- The labels (action instantiations) enabled in `st`: those whose `require`s hold.  -/
def enabledLabels [BEq l] [Hashable l]
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (st : σ) : List l :=
  ((sys.tr th st).foldl (init := Std.HashSet.emptyWithCapacity) fun seen (l, _) => seen.insert l).toList

/-- Run `LTLLib.modelCheck` for a `liveness`-declared property `p` -/
def check
    (sys : Veil.EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int l
      (List (l × Veil.ExecutionOutcome Int σ)) th) (p : LivenessProperty ρ σ)
    (hinit : sys.initStates.all (bfsClosure (sysSucc sys) sys.initStates).contains = true)
    (hclosed : (bfsClosure (sysSucc sys) sys.initStates).toList.all
      (fun s => (sysSucc sys s).all (bfsClosure (sysSucc sys) sys.initStates).contains) = true) :
    LTLLib.EmptinessResult (σ × LTLLib.BAState) :=
  LTLLib.modelCheck (S := Std.HashSet (LTLLib.NNF String)) p.φ sys.initStates (sysSucc sys)
    (p.sysLabel th)
    (finiteReach_of_closed (sysSucc sys) sys.initStates (bfsClosure (sysSucc sys) sys.initStates) hinit hclosed)

def checkResultToString [Repr σ] (sysName propName : String) :
    LTLLib.EmptinessResult (σ × LTLLib.BAState) → String
  | .empty n => s!"{sysName} ⊨ {propName} (explored {n} product states)"
  | .nonEmpty stem loop => s!"{sysName} ⊭ {propName}; counterexample stem={reprStr stem} loop={reprStr loop}"

end Veil.LivenessMC
