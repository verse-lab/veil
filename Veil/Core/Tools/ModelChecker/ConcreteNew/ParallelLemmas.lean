import Veil.Core.Tools.ModelChecker.ConcreteNew.SequentialLemmas

namespace Veil.ModelChecker.Concrete

variable {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)

def MapReduceSearchContextMain.initial : MapReduceSearchContextMain σ κ σₕ :=
  { base := BaseSearchContext.initial sys.initStates,
    tovisitQueue := sys.initStates.map (fun s => ⟨fp.view s, s, 0⟩) |>.toArray,
    tovisitSet := Std.HashSet.ofList <| sys.initStates.map fp.view }

/-- Create an empty local context with the given `completedDepth`. -/
def MapReduceSearchContextLocal.initial (completedDepth : Nat) : MapReduceSearchContextLocal σ κ σₕ :=
  ({ log := Std.HashMap.emptyWithCapacity,
     violatingStates := [],
     finished := none,
     completedDepth := completedDepth,
     currentFrontierDepth := completedDepth + 1,
     statesFound := 0,
     actionStatsMap := Std.HashMap.emptyWithCapacity }, #[])

end Veil.ModelChecker.Concrete
