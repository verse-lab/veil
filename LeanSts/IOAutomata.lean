import LeanSts.TransitionSystem

/- ## IO Automata -/
namespace IOAutomata

-- Label ℓ := [BEq ℓ] [Hashable ℓ] [ToString ℓ]

inductive ActionType where
  | internal
  | input
  | output
deriving BEq, Hashable

instance : Inhabited ActionType where
  default := ActionType.internal

inductive ActionLabel (ℓ : Type) [Hashable ℓ] [ToString ℓ] where
  | internal (label : ℓ)
  | input (label : ℓ)
  | output (label : ℓ)
deriving BEq

instance [Hashable ℓ] [ToString ℓ] : ToString (ActionLabel ℓ) where
  toString
    | ActionLabel.internal l => "internal " ++ toString l
    | ActionLabel.input l => "input " ++ toString l
    | ActionLabel.output l => "output " ++ toString l

def ActionLabel.type {ℓ : Type} [BEq ℓ] [Hashable ℓ] [ToString ℓ] : ActionLabel ℓ → ActionType
  | .internal _ => .internal
  | .input _ => .input
  | .output _ => .output

def ActionLabel.name {ℓ : Type} [BEq ℓ] [Hashable ℓ] [ToString ℓ] : ActionLabel ℓ → ℓ
  | ActionLabel.internal l => l
  | ActionLabel.input l => l
  | ActionLabel.output l => l

def ActionLabel.mk {ℓ : Type} [BEq ℓ] [Hashable ℓ] [ToString ℓ] (t : ActionType) (l : ℓ) : ActionLabel ℓ :=
  match t with
  | .internal => .internal l
  | .input => .input l
  | .output => .output l

#check ActionLabel.mk

/-- TLA-style actions with labels -/
structure Action (σ : Type) (ℓ : Type) [BEq ℓ] [Hashable ℓ] [ToString ℓ] where
  /-- TLA-style two-state transition for this action -/
  next : σ → σ → Prop
  /-- The label of the action. -/
  label : ActionLabel ℓ

instance [BEq ℓ] [Hashable ℓ] [ToString ℓ] : ToString (Action σ ℓ) where
  toString a := toString a.label

/-- A lifting of a (single) action into an IO Automata-style transition.
  IO Automata transitions are always enabled, i.e. for a given source
  state and label, there is always a post-state in the transition. -/
def Action.tr [BEq ℓ] [Hashable ℓ] [ToString ℓ] (a : Action σ ℓ) : σ → ActionLabel ℓ → σ → Prop := fun s l s' =>
  if l == a.label then a.next s s' else s = s'

def ActionSignature (ℓ : Type) [BEq ℓ] [Hashable ℓ] [ToString ℓ] := Lean.HashMap ℓ (ActionLabel ℓ)
def ActionMap (σ : Type) (ℓ : Type) [BEq ℓ] [Hashable ℓ] [ToString ℓ] := Lean.HashMap ℓ (Action σ ℓ)

instance [BEq ℓ] [Hashable ℓ] [ToString ℓ] : ToString (ActionMap σ ℓ) where
  toString m := toString m.toList

def ActionMap.ofList {σ : Type} {ℓ : Type} [BEq ℓ] [Hashable ℓ] [ToString ℓ] (l : List (ℓ × Action σ ℓ)) : ActionMap σ ℓ :=
  Lean.HashMap.ofList l

/-- The action signature corresponding to this action map -/
def ActionMap.sig {σ : Type} {ℓ : Type} [BEq ℓ] [Hashable ℓ] [ToString ℓ](acts : ActionMap σ ℓ) : ActionSignature ℓ :=
  Lean.HashMap.ofList $ acts.toList.map (fun (l, a) => (l, a.label))

def ActionMap.tr {σ : Type} {ℓ : Type} [BEq ℓ] [Hashable ℓ] [ToString ℓ] (acts : ActionMap σ ℓ) : σ → ActionLabel ℓ → σ → Prop :=
  fun s l s' =>
  match acts.find? l.name with
  | some a => a.tr s l s'
  -- In the absence of an action with this name, the transition does not exist
  | none => False

end IOAutomata

open IOAutomata
/-- An IO Automaton -/
class IOAutomaton (σ : Type) (ℓ : Type) [BEq ℓ] [Hashable ℓ] [ToString ℓ] where
  /-- A non-empty set of initial states -/
  init : σ → Prop
  /-- A mapping from labels (names) to actions -/
  acts : ActionMap σ ℓ

instance [BEq ℓ] [Hashable ℓ] [ToString ℓ] : ToString (IOAutomaton σ ℓ) where
  toString sys := s!"IOAutomaton {sys.acts}"

/-- The action signature of the automaton -/
def IOAutomaton.sig {ℓ : Type} [BEq ℓ] [Hashable ℓ] [ToString ℓ] [sys : IOAutomaton σ ℓ] := sys.acts.sig
/-- The transition relation of the automaton -/
def IOAutomaton.tr {ℓ : Type} [BEq ℓ] [Hashable ℓ] [ToString ℓ] [sys : IOAutomaton σ ℓ] := sys.acts.tr
