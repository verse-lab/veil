
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



elab "initial" ":=" ini:term : command => do
  Command.runTermElabM fun vs => do
    let stateTp := (<- stsExt.get).typ
    unless stateTp != default do throwError "State has not been declared so far"
    -- TODO: Check that `State` uses all section variables here
    let stateTp := mkAppN stateTp vs
    let stateTp <- PrettyPrinter.delab stateTp
    liftCommandElabM $ elabCommand $ <- `(@[initial] def $(mkIdent "inital?") : $stateTp -> Prop := $ini)


syntax "action" declId (explicitBinders)? ":=" term : command

-- def explicitBinders' : Parser := explicitBinders

-- def foo (x : Array $ TSyntax `Lean.Parser.Term.explicitBinder) : MacroM ((TSyntax `Lean.explicitBinders)) :=
--   if x.size == 1 then
--     match x[0]! with
--     | `(explicitBinder| ($[$x:ident]* : $tp)) => `(explicitBinders| $[($x : $tp)]*)
--     | _ => Macro.throwError "Unsupprted binder syntax"
--   else return default


elab_rules : command
  | `(command| action $nm:declId $br:explicitBinders ? := $act) => do
  Command.runTermElabM fun vs => do
    let stateTp := (<- stsExt.get).typ
    unless stateTp != default do throwError "State has not been declared so far"
    -- TODO: Check that `State` uses all section variables here
    let stateTp := mkAppN stateTp vs
    let stateTp <- PrettyPrinter.delab stateTp
    liftCommandElabM $ elabCommand $ <- match br with
    | some br =>
       `(@[action] def $nm : $stateTp -> $stateTp -> Prop := fun st1 st2 => exists $br, $act st1 st2)
    | _ =>
       `(@[action] def $nm : $stateTp -> $stateTp -> Prop := $act)

-- elab "action" nm:declId br:bracketedBinder ":=" act:term : command =>

def assembleActions : CommandElabM Unit := do
  Command.runTermElabM fun vs => do
    let stateTp := mkAppN (<- stsExt.get).typ vs
    let stateTp <- PrettyPrinter.delab stateTp
    let act0 :: actions := (<- stsExt.get).actions
      | throwError "There are no transitions defined"
    let act0 <- etaExpand act0
    let acts <- lambdaTelescope act0 fun args act0 => do
      let mut acts := act0
      for act in actions do
        let act := mkAppN act args
        acts <- mkAppM ``Or #[act, acts]
      mkLambdaFVars args acts
    let acts <- instantiateLambda acts vs
    let acts <- PrettyPrinter.delab acts
    liftCommandElabM $ elabCommand $ <- `(def $(mkIdent "Next") : $stateTp -> $stateTp -> Prop := $acts)

declare_syntax_cat inv
syntax "invariant" : inv
syntax "safety" : inv

elab inv ":=" inv:term : command => do
  Command.runTermElabM fun vs => do
    let stateTp := (<- stsExt.get).typ
    unless stateTp != default do throwError "State has not been declared so far"
    -- TODO: Check that `State` uses all section variables here
    let stateTp := mkAppN stateTp vs
    let stateTp <- PrettyPrinter.delab stateTp
    let num := (<- stsExt.get).invariants.length
    let inv_name := "inv" ++ toString num
    liftCommandElabM $ elabCommand $ <- `(@[inv] def $(mkIdent inv_name) : $stateTp -> Prop := $inv)

type node1
type node2

state :=
  foo : node1
  bar : node2

initial := fun x => True

action bazz (n m : Nat) := fun (x y : @State node1 node2) => n > m
#print bazz
action bazzz := fun x y => False
#eval assembleActions

invariant := fun st => True
invariant := fun st => st.foo = st.foo

#print Next
