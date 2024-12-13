import LeanSts.TransitionSystem
open Lean

/- ## IO Automata -/
namespace IOAutomata

class Label (ℓ : Type) extends BEq ℓ, Hashable ℓ, ToString ℓ, Inhabited ℓ
instance [BEq ℓ] [Hashable ℓ] [ToString ℓ] [Inhabited ℓ] : Label ℓ := { }

inductive ActionType where
  | internal
  | input
  | output
deriving BEq, Hashable

instance : Inhabited ActionType where
  default := ActionType.internal

instance : ToString ActionType where
  toString
    | .internal => "internal"
    | .input => "input"
    | .output => "output"

inductive ActionLabel (ℓ : Type) [Label ℓ] where
  | internal (label : ℓ)
  | input (label : ℓ)
  | output (label : ℓ)
deriving BEq, Inhabited

instance [Label ℓ]: ToString (ActionLabel ℓ) where
  toString
    | ActionLabel.internal l => "internal " ++ toString l
    | ActionLabel.input l => "input " ++ toString l
    | ActionLabel.output l => "output " ++ toString l

def ActionLabel.type {ℓ : Type} [Label ℓ] : ActionLabel ℓ → ActionType
  | .internal _ => .internal
  | .input _ => .input
  | .output _ => .output

def ActionLabel.name {ℓ : Type} [Label ℓ] : ActionLabel ℓ → ℓ
  | ActionLabel.internal l => l
  | ActionLabel.input l => l
  | ActionLabel.output l => l

def ActionLabel.mk {ℓ : Type} [Label ℓ] (t : ActionType) (l : ℓ) : ActionLabel ℓ :=
  match t with
  | .internal => .internal l
  | .input => .input l
  | .output => .output l

structure ActionDeclaration where
  type: ActionType
  name: Lean.Name
  ctor : Option (TSyntax `Lean.Parser.Command.ctor)
deriving BEq, Inhabited

def ActionDeclaration.label (a : ActionDeclaration) : ActionLabel Name :=
  ActionLabel.mk a.type a.name

instance : ToString ActionDeclaration where
  toString a := s!"{a.type} {a.name} with ctor {a.ctor}"

/-- Actions with labels, which include parameters. -/
structure Action (σ : Type) (ℓ : Type) [Label ℓ] where
  decl : ActionDeclaration
  /- Given a label, return TLA-style two-state transition for this action -/
  next : (label : ℓ) → (σ → σ → Prop)
deriving Inhabited

instance [Label ℓ] : ToString (Action σ ℓ) where
  toString a := toString a.decl

/- A lifting of a (single) action into an IO Automata-style transition.
  IO Automata transitions are always enabled, i.e. for a given source
  state and label, there is always a post-state in the transition. -/
def Action.tr [Label ℓ] (a : Action σ ℓ) : σ → ℓ → σ → Prop := fun s l s' => a.next l s s'

def Action.liftStateR [Label ℓ] (a₁ : Action σ₁ ℓ) : Action (σ₁ × σ₂) ℓ := {
  decl := a₁.decl,
  next := fun l (s₁, s₂) (s₁', s₂') => a₁.next l s₁ s₁' ∧ s₂ = s₂',
}

def Action.liftStateL [Label ℓ] (a₂ : Action σ₂ ℓ) : Action (σ₁ × σ₂) ℓ := {
  decl := a₂.decl,
  next := fun l (s₁, s₂) (s₁', s₂') => s₁ = s₁' ∧ a₂.next l s₂ s₂',
}

def Action.compose [Label ℓ₁] [Label ℓ₂] [Label ℓ] (a₁ : Action σ₁ ℓ₁) (conv₁ : ℓ → ℓ₁) (a₂ : Action σ₂ ℓ₂) (conv₂ : ℓ → ℓ₂) : Option (Action (σ₁ × σ₂) ℓ) :=
  let next := fun l (s₁, s₂) (s₁', s₂') => a₁.next (conv₁ l) s₁ s₁' ∧ a₂.next (conv₂ l) s₂ s₂'
  match (a₁.decl.label, a₂.decl.label) with
  -- internal actions cannot be composed; they are supposed to be disjoint with all other actions
  | (ActionLabel.internal _, _) | (_, ActionLabel.internal _) => none
  -- similarly, output actions cannot be composed; they are supposed to be disjoint
  | (ActionLabel.output _, ActionLabel.output _) => none
  -- input actions can be composed and their composition is an input action
  | (ActionLabel.input l₁, ActionLabel.input l₂) => if l₁ != l₂ then none else some
    { next := next, decl := a₁.decl }
  -- the composition of an output action with an input action is an output action
  | (ActionLabel.input l₁, ActionLabel.output l₂) | (ActionLabel.output l₁, ActionLabel.input l₂) => if l₁ != l₂ then none else some
    { next := next, decl := { a₁.decl with type := ActionType.output } }

def Action.compose' [Label ℓ] (a₁ : Option (Action σ₁ ℓ)) (a₂ : Option (Action σ₂ ℓ)) : Option (Action (σ₁ × σ₂) ℓ) :=
  match (a₁, a₂) with
  | (some a₁, some a₂) => Action.compose a₁ id a₂ id
  | (some a, none) => some (Action.liftStateR a)
  | (none, some a) => some (Action.liftStateL a)
  | (none, none) => none

def ActionSignature := Lean.HashMap Name (ActionLabel Name)
def ActionMap (σ : Type) (ℓ : Type) [Label ℓ] := Lean.HashMap Name (Action σ ℓ)

instance [Label ℓ] : Inhabited (ActionMap σ ℓ) where
  default := Lean.HashMap.empty

instance [Label ℓ] : ToString (ActionMap σ ℓ) where
  toString m := toString m.toList

def ActionMap.toList {σ : Type} {ℓ : Type} [Label ℓ] (acts : ActionMap σ ℓ) : List (Name × Action σ ℓ) :=
  Lean.HashMap.toList acts

def ActionMap.ofList {σ : Type} {ℓ : Type} [Label ℓ] (l : List (Name × Action σ ℓ)) : ActionMap σ ℓ :=
  Lean.HashMap.ofList l

def ActionMap.ofListWith {σ : Type} {ℓ : Type} [Label ℓ] (l : List (Name × Action σ ℓ)) (f : Action σ ℓ → Action σ ℓ → Action σ ℓ) : ActionMap σ ℓ :=
  Lean.HashMap.ofListWith l f

/-- The action signature corresponding to this action map -/
def ActionMap.sig {σ : Type} {ℓ : Type} [Label ℓ] (acts : ActionMap σ ℓ) : ActionSignature :=
  Lean.HashMap.ofList $ acts.toList.map (fun (l, a) => (l, a.decl.label))

-- def ActionMap.tr {σ : Type} {ℓ : Type} [Label ℓ] (acts : ActionMap σ ℓ) : σ → ActionLabel ℓ → σ → Prop :=
--   fun s l s' =>
--   match acts.find? l.name with
--   | some a => a.tr s l s'
--   -- In the absence of an action with this name, the transition does not exist
--   | none => False

def ActionMap.actionNames {σ : Type} {ℓ : Type} [Label ℓ] (acts : ActionMap σ ℓ) : List Name := acts.toList.map (fun (l, a) => l)
private def ActionMap.actionsOfType {σ : Type} {ℓ : Type} [Label ℓ] (acts : ActionMap σ ℓ) (t : ActionType) : List Name :=
  acts.toList.filterMap (fun (l, a) => if a.decl.label.type == t then some l else none)

def ActionMap.internalActions [Label ℓ] (acts : ActionMap σ ℓ) := acts.actionsOfType ActionType.internal
def ActionMap.inputActions [Label ℓ] (acts : ActionMap σ ℓ) := acts.actionsOfType ActionType.input
def ActionMap.outputActions [Label ℓ] (acts : ActionMap σ ℓ) := acts.actionsOfType ActionType.output

end IOAutomata

open IOAutomata
/-- An IO Automaton -/
class IOAutomaton (σ : Type) (ℓ : Type) [Label ℓ] where
  /-- A non-empty set of initial states -/
  init : σ → Prop
  /-- A mapping from labels (names) to actions -/
  acts : ActionMap σ ℓ

instance [Label ℓ] : ToString (IOAutomaton σ ℓ) where
  toString sys := s!"IOAutomaton {sys.acts}"

/-- The action signature of the automaton -/
def IOAutomaton.sig {ℓ : Type} [Label ℓ] [sys : IOAutomaton σ ℓ] := sys.acts.sig
/- The transition relation of the automaton -/
-- def IOAutomaton.tr {ℓ : Type} [Label ℓ] [sys : IOAutomaton σ ℓ] := sys.acts.tr

section Composition

def ActionMap.compose {σ₁ σ₂ : Type} {ℓ : Type} [Label ℓ] (am₁ : ActionMap σ₁ ℓ) (am₂ : ActionMap σ₂ ℓ) : Option (ActionMap (σ₁ × σ₂) ℓ) :=
  -- The internal actions must be unique across the two automata
  let disjoint_internal := (am₁.internalActions.all (fun l => !am₂.actionNames.contains l)) && (am₂.internalActions.all (fun l => !am₁.actionNames.contains l))
  -- The output actions must be disjoint
  let disjoint_output := am₁.outputActions.all (fun l => !am₂.outputActions.contains l)
  if !(disjoint_internal && disjoint_output) then none else
    -- All actions with the same name fire in parallel
    let actions : List (Name × Action (σ₁ × σ₂) ℓ) := (am₁.actionNames ++ am₂.actionNames).map (fun action =>
      match Action.compose' (am₁.find? action) (am₂.find? action) with
      | none => panic s!"Action composition of {action} failed! This is a logic bug!"
      | some comp_act => (action, comp_act)
    )
    some (ActionMap.ofList actions)

def IOAutomaton.compose [Label ℓ] (sys₁ : IOAutomaton σ₁ ℓ) (sys₂ : IOAutomaton σ₂ ℓ) : Option (IOAutomaton (σ₁ × σ₂) ℓ) :=
  match ActionMap.compose sys₁.acts sys₂.acts with
  | none => none
  | some acts => some { init := λ s => sys₁.init s.1 ∧ sys₂.init s.2, acts := acts }

end Composition
