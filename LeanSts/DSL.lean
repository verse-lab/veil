
import Lean
import LeanSts.DSLUtil
import Lean.Parser
open Lean Elab Command Term Meta Lean.Parser

-- Modelled after the Ivy language
-- https://github.com/kenmcmil/ivy/blob/master/doc/language.md

syntax "type" ident : command
macro_rules
| `(command | type $id:ident) => `(variable ($id : Type))

macro "state" ":=" fs:Command.structFields : command => do
  `(@[state] structure $(mkIdent "State") where mk :: $fs)

-- type node1
-- type node2

-- state :=
--   foo : node2
--   bar : node1

elab "initial" ":=" ini:term : command => do
  Command.runTermElabM fun vs => do
    let stateTp := (<- stsExt.get).typ
    unless stateTp != default do throwError "State has not been declared so far"
    -- TODO: Check that `State` uses all section variables here
    let stateTp := mkAppN stateTp vs
    let stateTp <- PrettyPrinter.delab stateTp
    liftCommandElabM $ elabCommand $ <- `(@[initial] def $(mkIdent "inital?") : $stateTp -> Prop := $ini)

-- initial := fun x => True
