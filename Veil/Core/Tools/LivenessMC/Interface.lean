module

public import Veil.Core.Tools.ModelChecker.Interface
public import LTLLib.LTL.Syntax

public section

namespace Veil.LivenessMC
open Lean

/-- An atomic proposition of a liveness property.

`state` is the `⌜ … ⌝` form, a predicate on the state. `enabled` and `taken` are the two action
primitives, both identified by a predicate on the action *label*, so that `E(send)` (any instantiation)
and `E(send n next)` (one instantiation) are the same construct with a different predicate.

The split that matters is that **`enabled` is a state atom and only `taken` is an edge atom**: whether some
instantiation of an action can fire is determined by the state alone, so `E(a)` needs nothing from the
labelled product and works on every mode, while `T(a)` is a property of the step. -/
inductive LivenessAtom (ρ σ l : Type) where
  | state (p : Veil.ModelChecker.SafetyProperty ρ σ)
  | enabled (name : Name) (isMatch : l → Bool)
  | taken (name : Name) (isMatch : l → Bool)

def LivenessAtom.name : LivenessAtom ρ σ l → Name
  | .state p => p.name
  | .enabled n _ => n
  | .taken n _ => n

structure LivenessProperty (ρ σ l : Type) where
  name : Name := Name.anonymous
  atoms : List (LivenessAtom ρ σ l)
  φ : LTLLib.Formula Nat -- Reference atomic props by their index in `atoms`

/-- The state atoms holding at `st`: the `⌜ … ⌝` predicates, plus the `E(a)` atoms matched by some label
that can fire at `st`.

`enabledHere` is the caller's list of **step-enabled** labels — those with a `.success` outcome, not merely
those whose guard passes. That keeps `E` and `T` coherent on the graph the checker actually walks: `E(a)`
holds at `s` exactly when some `T(a)`-step leaves `s`. An action whose guard holds but which then faults is
not enabled in this sense; that is an assertion failure, which the safety checker reports, not a fairness
obligation. -/
@[inline, specialize]
def LivenessProperty.stateLabel (p : LivenessProperty ρ σ l) (th : ρ) (st : σ)
    (enabledHere : List l) : Std.HashSet Nat :=
  (p.atoms.foldl (init := ((0 : Nat), (∅ : Std.HashSet Nat))) fun (i, acc) a =>
    (i + 1, match a with
      | .state q => if q.holdsOn th st then acc.insert i else acc
      | .enabled _ isMatch => if enabledHere.any isMatch then acc.insert i else acc
      | .taken _ _ => acc)).2

/-- The edge atoms a step labelled `lbl` contributes: the `T(a)` atoms matching it. -/
@[inline, specialize]
def LivenessProperty.edgeLabel (p : LivenessProperty ρ σ l) (lbl : l) : Std.HashSet Nat :=
  (p.atoms.foldl (init := ((0 : Nat), (∅ : Std.HashSet Nat))) fun (i, acc) a =>
    (i + 1, match a with
      | .taken _ isMatch => if isMatch lbl then acc.insert i else acc
      | _ => acc)).2

/-- Is atom index `i` a `T(…)`, i.e. one a *step* can contribute? This is the `edgeAtom` predicate
LTLLib's `modelCheckFairRoutedOfStep` takes, and the whole of what Veil tells it: a hoisted `◇□` region
mentioning one of these cannot be decided by the source state, which is the condition the prune needs, so
a property that has one is routed to the crossing instead. -/
def LivenessProperty.isEdgeAtom (p : LivenessProperty ρ σ l) (i : Nat) : Bool :=
  match p.atoms[i]? with
  | some (.taken _ _) => true
  | _ => false

/-- Everything `edgeLabel` contributes is an edge atom's index. -/
theorem LivenessProperty.isEdgeAtom_of_mem_edgeLabel (p : LivenessProperty ρ σ l) (lbl : l)
    {i : Nat} (h : i ∈ p.edgeLabel lbl) : p.isEdgeAtom i = true := by
  -- generalise over the suffix being folded and the accumulator's start index
  suffices hgen : ∀ (as : List (LivenessAtom ρ σ l)) (k : Nat) (acc : Std.HashSet Nat),
      (∀ j ∈ acc, p.isEdgeAtom j = true) →
      (∀ m, (hm : m < as.length) → p.atoms[k + m]? = some as[m]) →
      ∀ j ∈ (as.foldl (init := (k, acc)) fun (n, a') a =>
              (n + 1, match a with
                | .taken _ isMatch => if isMatch lbl then a'.insert n else a'
                | _ => a')).2,
        p.isEdgeAtom j = true by
    exact hgen p.atoms 0 ∅ (by simp) (fun m hm => by simp [List.getElem?_eq_getElem hm]) i h
  intro as
  induction as with
  | nil => intro k acc hacc _ j hj; exact hacc j hj
  | cons a as ih =>
    intro k acc hacc hidx j hj
    refine ih (k + 1) _ (fun j' hj' => ?_) (fun m hm => by
      have := hidx (m + 1) (by simpa using hm)
      rwa [show k + (m + 1) = k + 1 + m from by omega] at this) j hj
    -- the accumulator grows by at most `k`, and only when `a` is a `.taken`
    cases ha : a with
    | taken nm isMatch =>
      simp only [ha] at hj'
      split at hj'
      · rcases Std.HashSet.mem_insert.mp hj' with heq | hmem
        · have hk := hidx 0 (by simp)
          simp only [Nat.add_zero, List.getElem_cons_zero, ha] at hk
          have hjk : k = j' := by simpa using heq
          subst hjk
          simp [LivenessProperty.isEdgeAtom, hk]
        · exact hacc j' hmem
      · exact hacc j' hj'
    | state _ => simp only [ha] at hj'; exact hacc j' hj'
    | enabled _ _ => simp only [ha] at hj'; exact hacc j' hj'

/-- Does the property mention an `E(a)`? -/
def LivenessProperty.hasEnabledAtoms (p : LivenessProperty ρ σ l) : Bool :=
  p.atoms.any fun | .enabled _ _ => true | _ => false

/-- Does the property mention a `T(a)`? Only then are the steps' letters non-empty, and only then does the
route have to be a labelled one. -/
def LivenessProperty.hasEdgeAtoms (p : LivenessProperty ρ σ l) : Bool :=
  p.atoms.any fun | .taken _ _ => true | _ => false

instance : Inhabited (LivenessProperty ρ σ l) where
  default := {
    name := Name.anonymous
    atoms := []
    φ := default
  }

end Veil.LivenessMC
