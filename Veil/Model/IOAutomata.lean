import Lean
import Std.Data.HashSet.Lemmas
import Veil.Model.TransitionSystem
open Lean

/-!# IOAutomata -/

inductive ActionKind where
  | internal
  | input
  | output
deriving BEq, Hashable

def ActionKind.toName : ActionKind → Name
  | .input => ``ActionKind.input
  | .internal => ``ActionKind.internal
  | .output => ``ActionKind.output

instance : Inhabited ActionKind where
  default := ActionKind.internal

instance : ToString ActionKind where
  toString
    | .internal => "internal"
    | .input => "input"
    | .output => "output"

abbrev ActionIdentifier := Lean.Name

/-- This is an implementation detail of the DSL, used to construct the
Label type for specifications. -/
structure ActionDeclaration where
  kind: ActionKind
  name: ActionIdentifier
  ctor : Option (TSyntax `Lean.Parser.Command.ctor)
deriving BEq, Inhabited

instance [BEq α] [Hashable α] : Inter (Std.HashSet α) where
  inter xs ys := xs.filter ys.contains

instance {α} [BEq α] [Hashable α] : SDiff (Std.HashSet α) where
  sdiff xs ys := xs.filter (fun x => !ys.contains x)

instance : ToString ActionDeclaration where
  toString a := s!"{a.kind} {a.name} with ctor {a.ctor}"

/-- This typeclass connects the label type to the action declarations.
We introduce this because our actions take parameters, so they carry
strictly more information than just the action declaration. -/
class ActionLabel (l : Type) where
  /-- The action identifier for a given label. -/
  id : l → ActionIdentifier
  /-- The action kind for a given action identifier. -/
  kind : Std.HashMap ActionIdentifier ActionKind

def actionIdentifier (a : l) [L : ActionLabel l] : ActionIdentifier :=
  L.id a

def isInputAction (a : l) [L : ActionLabel l] : Bool :=
  L.kind.get? (actionIdentifier a) == .some .input

def isOutputAction (a : l) [L : ActionLabel l] : Bool :=
  L.kind.get? (actionIdentifier a) == .some .output

def isInternalAction (a : l) [L : ActionLabel l] : Bool :=
  L.kind.get? (actionIdentifier a) == .some .internal

-- A concrete `Label` type is constructed based on the `ActionDeclaration`s
-- for each specification in Veil.
structure IOAutomatonSignature where
  internal : Std.HashSet ActionIdentifier
  input : Std.HashSet ActionIdentifier
  output : Std.HashSet ActionIdentifier

def IOAutomatonSignature.actions (s : IOAutomatonSignature) : Std.HashSet ActionIdentifier :=
  s.internal ∪ s.input ∪ s.output

instance : Membership ActionIdentifier IOAutomatonSignature where
  mem s a := a ∈ s.actions

/-- The set of actions locally-controlled actions, i.e. those triggered
by the automaton itself (i.e. internal and output). -/
def IOAutomatonSignature.local (s : IOAutomatonSignature) : Std.HashSet ActionIdentifier :=
  s.internal ∪ s.output

/-- The set of actions visible to the environment, i.e. input and output actions. -/
def IOAutomatonSignature.external (s : IOAutomatonSignature) : Std.HashSet ActionIdentifier :=
  s.input ∪ s.output

/-- Every action only has one kind. -/
def IOAutomatonSignature.isValid (s : IOAutomatonSignature) : Bool :=
  (s.input ∩ s.output).isEmpty ∧
  (s.output ∩ s.internal).isEmpty ∧
  (s.input ∩ s.internal).isEmpty

/-- Create a new signature with only the external actions. -/
def IOAutomatonSignature.mkExternal (s : IOAutomatonSignature) : IOAutomatonSignature :=
  { s with internal := ∅ }

/-!## Definition-/

/--
  A type class for IOAutomata.
  `σ` is the type of states.
  `l` is the type of labels.
-/
class IOAutomaton (σ : Type) (l : Type) [ActionLabel l] where
  signature : IOAutomatonSignature
  /-- Initial states -/
  init : σ → Prop
  /-- Transition relation -/
  step : σ → l → σ → Prop

def IOAutomaton.actions [ActionLabel l] (m : IOAutomaton σ l) : Std.HashSet ActionIdentifier :=
  m.signature.actions

def IOAutomaton.hasAction [ActionLabel l] (m : IOAutomaton σ l) (e : Option l) : Bool :=
  match e with
  | some e => m.actions.contains (actionIdentifier e)
  | none => false

def IOAutomaton.inputs [ActionLabel l] (m : IOAutomaton σ l) : Std.HashSet ActionIdentifier :=
  m.signature.input

def IOAutomaton.outputs [ActionLabel l] (m : IOAutomaton σ l) : Std.HashSet ActionIdentifier :=
  m.signature.output

/-- The set of initial states is non-empty. -/
def IOAutomaton.hasInitialStates [ActionLabel l] (m : IOAutomaton σ l) : Prop :=
  ∃ s, m.init s

/-- The transition relation of the automaton is consistent with the
signature, i.e. it doesn't use any actions that are not in the
signature. -/
def IOAutomaton.hasConsistentSignature [ActionLabel l] (m : IOAutomaton σ l) : Prop :=
  ∀ s₁ a s₂, m.step s₁ a s₂ → actionIdentifier a ∈ m.signature

/-- Input actions can always be taken. In practice, this isn't an
onerous constraint, since these actions can always stutter if their
parameters are invalid. -/
def IOAutomaton.isInputEnabled [ℓ : ActionLabel l] (m : IOAutomaton σ l) : Prop :=
  ∀ a, isInputAction a → (∀ s₁, ∃ s₂, m.step s₁ a s₂)

def IOAutomaton.isValid [ActionLabel l] (m : IOAutomaton σ l) : Prop :=
  m.signature.isValid ∧
  m.hasInitialStates ∧
  m.hasConsistentSignature ∧
  m.isInputEnabled

/-!## Parallel composition-/

/-- Two automata are compatible if their output actions and all
internal actions are unique (i.e. no other action has the same name).
-/
def IOAutomaton.compatible [ActionLabel l₁] [ActionLabel l₂] (m₁ : IOAutomaton σ₁ l₁) (m₂ : IOAutomaton σ₂ l₂) : Bool :=
  (m₁.outputs ∩ m₂.outputs).isEmpty ∧
  (m₁.inputs ∩ m₂.actions).isEmpty ∧
  (m₂.inputs ∩ m₁.actions).isEmpty

def IOAutomatonSignature.compose (s₁ : IOAutomatonSignature) (s₂ : IOAutomatonSignature) : IOAutomatonSignature :=
  {
    internal := s₁.internal ∪ s₂.internal,
    -- Input actions which are not matched to output actions remain input.
    -- Those that are matched become output actions.
    input := ((s₁.input ∪ s₂.input) \ (s₁.output ∪ s₂.output))
    output := s₁.output ∪ s₂.output
  }

class ComposedActionLabel (l₁ : Type) (l₂ : Type) (l : outParam Type) where
  conv₁ : l → Option l₁
  conv₂ : l → Option l₂

def transitionOrStutter [ActionLabel l] (a : Option l) (m : IOAutomaton σ l) (s₁ s₂ : σ) : Prop :=
  match a with
  | none => s₁ = s₂
  | some a => m.step s₁ a s₂

def IOAutomaton.parallelCompose [ActionLabel l₁] [ActionLabel l₂] [ActionLabel l] [ℓ : ComposedActionLabel l₁ l₂ l]
  (m₁ : IOAutomaton σ₁ l₁) (m₂ : IOAutomaton σ₂ l₂) : IOAutomaton (σ₁ × σ₂) l :=
  {
    signature := IOAutomatonSignature.compose m₁.signature m₂.signature,
    init := fun ⟨s₁, s₂⟩ => m₁.init s₁ ∧ m₂.init s₂,
    step := fun ⟨s₁, s₂⟩ a ⟨s₁', s₂'⟩ =>
      let a₁ := ℓ.conv₁ a
      let a₂ := ℓ.conv₂ a
      -- this is an action of at least one of the two automata
      (m₁.hasAction a₁ ∨ m₂.hasAction a₂) ∧
      -- each sub-state transitions according to `a` or stutters (if `a` is not an action of that sub-automaton)
      transitionOrStutter a₁ m₁ s₁ s₁' ∧ transitionOrStutter a₂ m₂ s₂ s₂'
  }
