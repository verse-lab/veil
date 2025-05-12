import Lean
import Veil.Model.TransitionSystem
open Lean

inductive ActionKind where
  | internal
  | input
  | output
deriving BEq, Hashable

instance : Inhabited ActionKind where
  default := ActionKind.internal

instance : ToString ActionKind where
  toString
    | .internal => "internal"
    | .input => "input"
    | .output => "output"

structure ActionDeclaration where
  kind: ActionKind
  name: Lean.Name
  ctor : Option (TSyntax `Lean.Parser.Command.ctor)
deriving BEq, Inhabited

instance : ToString ActionDeclaration where
  toString a := s!"{a.kind} {a.name} with ctor {a.ctor}"
