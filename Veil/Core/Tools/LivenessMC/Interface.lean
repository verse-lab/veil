module

public import Veil.Core.Tools.ModelChecker.Interface
public import Veil.Frontend.DSL.State.Types
public import Lasso.LTL.Syntax
public import Lentil.Utils.MiscLemmas

public section

namespace Veil.LivenessMC
open Lean

/-- An atomic proposition of a liveness property. `enabled` is a state atom and only `taken` is an edge atom, whether some
instantiation of an action can fire is determined by the state alone. -/
inductive LivenessAtom (ρ σ l : Type) where
  -- the `⌜ … ⌝` form, a predicate on the state
  | state (p : Veil.ModelChecker.SafetyProperty ρ σ)
  -- `Enabled a`, matched on the action label, so `Enabled send` and `Enabled (send n next)` use different predicates
  | enabled (name : Name) (isMatch : l → Bool)
  -- `⟨a⟩`, a property of the step
  | taken (name : Name) (isMatch : l → Bool)

def LivenessAtom.name : LivenessAtom ρ σ l → Name
  | .state p => p.name
  | .enabled n _ => n
  | .taken n _ => n

structure LivenessProperty (ρ σ l : Type) where
  name : Name := Name.anonymous
  atoms : List (LivenessAtom ρ σ l)
  φ : Lasso.Formula Nat -- Reference atomic props by their index in `atoms`

/-- The disjunction of a list of formulas, `⊥` for the empty list.

TODO: This belongs in Lasso, next to `Lasso.Formula.conj`. -/
def disj (φs : List (Lasso.Formula α)) : Lasso.Formula α :=
  LentilLib.List.foldrD .or .ff φs

/-- The conjunction of `φ x` over all values `x` that `Enumeration` lists. In a Veil module, `[ltl| ∀ x, φ]` elaborates to it. -/
def forallEnum (φ : α → Lasso.Formula β) [Enumeration α] : Lasso.Formula β :=
  Lasso.Formula.conj (Enumeration.allValues.map φ)

/-- The disjunction of `φ x` over all values `x` that `Enumeration` lists. In a Veil module, `[ltl| ∃ x, φ]` elaborates to it. -/
def existsEnum (φ : α → Lasso.Formula β) [Enumeration α] : Lasso.Formula β :=
  disj (Enumeration.allValues.map φ)

/-- The property `φ` with its atoms numbered, every occurrence becoming an atomic proposition of its own, numbered in the
order `φ` mentions it, left to right. -/
def LivenessProperty.ofFormula (name : Name) (φ : Lasso.Formula (LivenessAtom ρ σ l)) :
    LivenessProperty ρ σ l :=
  let (φ, atoms) := (number φ).run #[]
  { name, atoms := atoms.toList, φ }
where
  number : Lasso.Formula (LivenessAtom ρ σ l) → StateM (Array (LivenessAtom ρ σ l)) (Lasso.Formula Nat)
    | .tt => pure .tt
    | .ff => pure .ff
    | .atom a => modifyGet fun atoms => (.atom atoms.size, atoms.push a)
    | .not φ => .not <$> number φ
    | .and φ ψ => .and <$> number φ <*> number ψ
    | .or φ ψ => .or <$> number φ <*> number ψ
    | .implies φ ψ => .implies <$> number φ <*> number ψ
    | .iff φ ψ => .iff <$> number φ <*> number ψ
    | .next φ => .next <$> number φ
    | .until φ ψ => .until <$> number φ <*> number ψ
    | .release φ ψ => .release <$> number φ <*> number ψ
    | .eventually φ => .eventually <$> number φ
    | .always φ => .always <$> number φ

/-- The state atoms holding at `st`, the `⌜ … ⌝` predicates plus the `Enabled a` atoms matched by some label that can fire at `st`.
`enabledHere` is the caller's list of step-enabled labels, those with a `.success` outcome, not merely those whose guard passes. -/
@[inline, specialize]
def LivenessProperty.stateLabel (p : LivenessProperty ρ σ l) (th : ρ) (st : σ)
    (enabledHere : List l) : Std.HashSet Nat :=
  (p.atoms.foldl (init := ((0 : Nat), (∅ : Std.HashSet Nat))) fun (i, acc) a =>
    (i + 1, match a with
      | .state q => if q.holdsOn th st then acc.insert i else acc
      | .enabled _ isMatch => if enabledHere.any isMatch then acc.insert i else acc
      | .taken _ _ => acc)).2

/-- The edge atoms a step labelled `lbl` contributes: the `⟨a⟩` atoms matching it. -/
@[inline, specialize]
def LivenessProperty.edgeLabel (p : LivenessProperty ρ σ l) (lbl : l) : Std.HashSet Nat :=
  (p.atoms.foldl (init := ((0 : Nat), (∅ : Std.HashSet Nat))) fun (i, acc) a =>
    (i + 1, match a with
      | .taken _ isMatch => if isMatch lbl then acc.insert i else acc
      | _ => acc)).2

/-- Is atom index `i` a `⟨…⟩`, one a step can contribute? This is the `edgeAtom` predicate Lasso's
`modelCheckFairRoutedOfStep` takes, and the whole of what Veil tells it. -/
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

/-- Does the property mention an `Enabled a`? -/
def LivenessProperty.hasEnabledAtoms (p : LivenessProperty ρ σ l) : Bool :=
  p.atoms.any fun | .enabled _ _ => true | _ => false

/-- Does the property mention a `⟨a⟩`? Only then are the steps' letters non-empty. -/
def LivenessProperty.hasEdgeAtoms (p : LivenessProperty ρ σ l) : Bool :=
  p.atoms.any fun | .taken _ _ => true | _ => false

instance : Inhabited (LivenessProperty ρ σ l) where
  default := {
    name := Name.anonymous
    atoms := []
    φ := default
  }

end Veil.LivenessMC
