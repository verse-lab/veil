
import Lean
import LeanSts.DSLUtil
import Lean.Parser
import LeanSts.TransitionSystem
open Lean Elab Command Term Meta Lean.Parser RelationalTransitionSystem

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
    liftCommandElabM $ elabCommand $ <- `(@[initial] def $(mkIdent "initalState?") : $stateTp -> Prop := $ini)


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
    | some br =>                                                            -- TODO: add macro a beta reduction here
       `(@[action] def $nm : $stateTp -> $stateTp -> Prop := fun st1 st2 => exists $br, $act st1 st2)
    | _ =>
       `(@[action] def $nm : $stateTp -> $stateTp -> Prop := $act)

-- elab "action" nm:declId br:bracketedBinder ":=" act:term : command =>

def combineLemmas (op : Name) (exps: List Expr) (vs : Array Expr) (name : String) : MetaM Expr := do
    let exp0 :: exprs := exps
      | throwError ("There are no" ++ name ++ "defined")
    let exp0 <- etaExpand exp0
    let exps <- lambdaTelescope exp0 fun args exp0 => do
      let mut exps := exp0
      for exp in exprs do
        let exp := mkAppN exp args
        exps <- mkAppM op #[exp, exps]
      mkLambdaFVars args exps
    instantiateLambda exps vs

def assembleActions : CommandElabM Unit := do
  Command.runTermElabM fun vs => do
    let stateTp := mkAppN (<- stsExt.get).typ vs
    let stateTp <- PrettyPrinter.delab stateTp
    let acts <- combineLemmas ``Or (<- stsExt.get).actions vs "transitions"
    let acts <- PrettyPrinter.delab acts
    liftCommandElabM $ elabCommand $ <- `(def $(mkIdent "Next") : $stateTp -> $stateTp -> Prop := $acts)

elab nm:("invariant" <|> "safety") ":=" inv:term : command => do
  Command.runTermElabM fun vs => do
    let stateTp := (<- stsExt.get).typ
    unless stateTp != default do throwError "State has not been declared so far"
    -- TODO: Check that `State` uses all section variables here
    let stateTp := mkAppN stateTp vs
    let stateTp <- PrettyPrinter.delab stateTp
    let num := (<- stsExt.get).invariants.length
    let inv_name := "inv" ++ toString num
    liftCommandElabM $ elabCommand $ <- `(@[inv] def $(mkIdent inv_name) : $stateTp -> Prop := $inv)

def assembleInvariant : CommandElabM Unit := do
  Command.runTermElabM fun vs => do
    let stateTp := mkAppN (<- stsExt.get).typ vs
    let stateTp <- PrettyPrinter.delab stateTp
    let invs <- combineLemmas ``And (<- stsExt.get).invariants vs "transitions"
    let invs <- PrettyPrinter.delab invs
    liftCommandElabM $ elabCommand $ <- `(def $(mkIdent "Inv") : $stateTp -> Prop := $invs)

def instantiateSystem : CommandElabM Unit :=
  Command.runTermElabM fun vs => do
    let stateTp   := mkAppN (<- stsExt.get).typ vs
    let stateTp   <- PrettyPrinter.delab stateTp
    let initSt    := mkAppN (<- mkConst "initalState?") vs
    let initSt    <- PrettyPrinter.delab initSt
    let nextTrans := mkAppN (<- mkConst "Next") vs
    let nextTrans <- PrettyPrinter.delab nextTrans
    liftCommandElabM $ elabCommand $ <-
      `(instance : RelationalTransitionSystem $stateTp where
          init := $initSt
          next := $nextTrans)


type node1
type node2

state :=
  foo : node1
  bar : node2

initial := fun x => True

action bazz (n m : Nat) := fun (x y) => n > m
-- #print bazz
action bazzz := fun x y => False
#eval assembleActions
#print Next

safety := fun st => 5 = 5
invariant := fun st => True
invariant := fun st => st.foo = st.foo

#eval assembleInvariant

#print Inv

#eval instantiateSystem
