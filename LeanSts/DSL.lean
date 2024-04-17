
import Lean
open Lean Elab Command Term Meta

-- Modelled after the Ivy language
-- https://github.com/kenmcmil/ivy/blob/master/doc/language.md

declare_syntax_cat decl_type
syntax "type"       : decl_type -- sort declaration
syntax "relation"   : decl_type -- relation declaration
syntax "function"   : decl_type -- function declaration
syntax "instance"   : decl_type -- e.g. `instantiate total_order(le)`

syntax (name := type_decl) "type" ident : command
macro_rules
| `(command | type $id:ident) => `(variable ($id : Type))

-- for `instance`, declare a class instance, e.g. `variable [Quorum node quorum]`

declare_syntax_cat def_type
syntax "definition" : def_type -- (pure) definition
syntax "transition" : def_type -- two-state transition
syntax "action"     : def_type -- imperative action

declare_syntax_cat formula_type
syntax "axiom"      : formula_type -- axiom
syntax "invariant"  : formula_type -- invariant clause
syntax "safety"     : formula_type -- safety property

syntax (name := prop_decl) formula_type ("[" ident "]")? term : command

@[command_elab prop_decl]
def prop_declImpl : CommandElab := fun stx => do
  logInfo s!"{stx}"

axiom True
invariant [gt7] ∃ (x : Nat), x ≥ 7
safety [consistency] True
