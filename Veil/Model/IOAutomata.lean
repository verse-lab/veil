import Lean
import Veil.Model.TransitionSystem
open Lean

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
