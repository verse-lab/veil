
import Lean
import LeanSts.DSLUtil
import Lean.Parser
open Lean Elab Command Term Meta Lean.Parser

-- Modelled after the Ivy language
-- https://github.com/kenmcmil/ivy/blob/master/doc/language.md

-- declare_syntax_cat decl_type
-- syntax "type"       : decl_type -- sort declaration
-- syntax "relation"   : decl_type -- relation declaration
-- syntax "function"   : decl_type -- function declaration
-- syntax "instance"   : decl_type -- e.g. `instantiate total_order(le)`

syntax "type" ident : command
macro_rules
| `(command | type $id:ident) => `(variable ($id : Type))

-- -- for `instance`, declare a class instance, e.g. `variable [Quorum node quorum]`

-- declare_syntax_cat def_type
-- syntax "definition" : def_type -- (pure) definition
-- syntax "transition" : def_type -- two-state transition
-- syntax "action"     : def_type -- imperative action

-- declare_syntax_cat formula_type
-- syntax "axiom"      : formula_type -- axiom
-- syntax "invariant"  : formula_type -- invariant clause
-- syntax "safety"     : formula_type -- safety property

-- syntax (name := prop_decl) formula_type ("[" ident "]")? term : command

-- @[command_elab prop_decl]
-- def prop_declImpl : CommandElab := fun stx => do
--   logInfo s!"{stx}"

-- axiom True
-- invariant [gt7] ∃ (x : Nat), x ≥ 7
-- safety [consistency] True

macro "state" ":=" fs:Command.structFields : command => do
  `(@[state] structure $(mkIdent "State") where mk :: $fs)

-- section

variable (node1 node2 : Type)

state :=
  foo : node2
  bar : node1

elab "initial" ":=" ini:term : command => do
  Command.runTermElabM fun vs => do
    let stateTp := (<- stsExt.get).typ
    unless stateTp != default do throwError "State has not been declared so far"
    let stateTp := mkAppN stateTp vs
    let stateTp <- PrettyPrinter.delab stateTp
    liftCommandElabM $ elabCommand $ <- `(@[initial] def $(mkIdent "inital?") : $stateTp -> Prop := $ini)

initial := fun x => True
