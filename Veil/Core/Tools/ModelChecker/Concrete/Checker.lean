import Veil.Core.Tools.ModelChecker.TransitionSystem
import Veil.Core.Tools.ModelChecker.Interface
import Veil.Core.Tools.ModelChecker.Concrete.FunctionalQueue

namespace Veil.ModelChecker.Concrete
open Std

/-- A function that maps a full state to a view of the state. -/
class StateView (FullState View : Type) where
  view : FullState → View

@[default_instance low] instance : StateView σ σ where
  view := id

class abbrev StateFingerprint (FullState View : Type) := BEq View, LawfulBEq View, Hashable View, LawfulHashable View, StateView FullState View

/-- A model checker search context is parametrised by the system that's being
checked and the theory it's being checked under. -/
structure SearchContext {ρ σ κ σₕ : Type} (SetT : Type → Type)
  [Collection SetT ρ] [Collection SetT σ] [Collection SetT (κ × σ)]
  [fp : StateFingerprint σ σₕ]
  (sys : EnumerableTransitionSystem ρ (SetT ρ) σ (SetT σ) κ (SetT (κ × σ)))
  (th : ρ) (hTh : th ∈ sys.theories)
where
  seen  : Std.HashSet σₕ
  sq    : fQueue (σₕ × σ)
  /- We use a `HashMap σ_post (σ_pre × κ)` to store the log of transitions, which
  will make it easier to reconstruct counterexample trace. -/
  log                : Std.HashMap σₕ (σₕ × κ)
  violatingStates    : List σₕ
  /-- Have we finished the search? -/
  finished           : Bool
  queue_sound        : ∀ x : σ, ⟨fp.view x, x⟩ ∈ fQueue.toList sq → sys.reachable th x
  visited_sound      : Function.Injective fp.view → ∀ x, (fp.view x) ∈ seen → sys.reachable th x
  queue_sub_visited  : ∀ x : σ, ⟨fp.view x, x⟩ ∈ fQueue.toList sq → (fp.view x) ∈ seen
  queue_wellformed   : ∀ fingerprint st, ⟨fingerprint, st⟩ ∈ fQueue.toList sq → fingerprint = fp.view st

def SearchContext.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq ρ] [BEq σ] [BEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)))
  (th : ρ) (hTh : th ∈ sys.theories) :
  @SearchContext ρ σ κ σₕ List _ _ _ fp sys th hTh := {
    seen := HashSet.insertMany HashSet.emptyWithCapacity (sys.initStates th |> Functor.map fp.view),
    sq := fQueue.ofList (sys.initStates th |> Functor.map (fun s => (fp.view s, s))),
    log := Std.HashMap.emptyWithCapacity
    violatingStates := []
    finished := false
    queue_sound := by dsimp only [Functor.map]; intros; grind
    visited_sound := by
      dsimp only [Functor.map]
      intro h_view_inj x h_in
      have h_in_init : x ∈ (EnumerableTransitionSystem.initStates σ (List (κ × σ)) th) := by {
        have h_in_list : fp.view x ∈ ((EnumerableTransitionSystem.initStates σ (List (κ × σ)) th)).map fp.view := by
          { grind [Std.HashSet.mem_of_mem_insertMany_list] }
        rw [List.mem_map] at h_in_list
        obtain ⟨s, h_s_in, h_eq_view⟩ := h_in_list
        have h_eq_st : s = x := h_view_inj h_eq_view
        grind
      }
      grind
    queue_sub_visited := by dsimp only [Functor.map]; intros; grind
    queue_wellformed := by dsimp only [Functor.map]; intros; grind
  }

def SearchContext.bfsStep {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq ρ] [BEq σ] [BEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)))
  (th : ρ) (hTh : th ∈ sys.theories)
  (ctx : @SearchContext ρ σ κ σₕ List _ _ _ fp sys th hTh) :
  @SearchContext ρ σ κ σₕ List _ _ _ fp sys th hTh := sorry


end Veil.ModelChecker.Concrete
