
import Lean
import LeanSts.DSLUtil
import Lean.Parser
import LeanSts.TransitionSystem
open Lean Elab Command Term Meta Lean.Parser RelationalTransitionSystem

-- Modelled after the Ivy language
-- https://github.com/kenmcmil/ivy/blob/master/doc/language.md

macro "type" id:ident : command => `(variable ($id : Type))
macro "instantiate" t:term : command => `(variable [$t])
macro "instantiate" nm:ident " : " t:term : command => `(variable [$nm : $t])

structure foo := foo : nat

elab "state" ":=" fs:Command.structFields : command => do
  let scope <- getScope
  let vd := scope.varDecls
  elabCommand $ <-
    `(@[state] structure $(mkIdent "State") $[$vd]* where mk :: $fs)



elab "initial" ":=" ini:term : command => do
  let vd := (<- getScope).varDecls
  Command.runTermElabM fun vs => do
    let stateTp := (<- stsExt.get).typ
    unless stateTp != default do throwError "State has not been declared so far"
    -- TODO: Check that `State` uses all section variables here
    let stateTp := mkAppN stateTp vs
    let stateTp <- PrettyPrinter.delab stateTp
    liftCommandElabM $ elabCommand $ <-
      `(@[initial] def $(mkIdent "initalState?") $[$vd]* : $stateTp -> Prop := $ini)


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
  let vd := (<- getScope).varDecls
  Command.runTermElabM fun vs => do
    let stateTp := (<- stsExt.get).typ
    unless stateTp != default do throwError "State has not been declared so far"
    -- TODO: Check that `State` uses all section variables here
    let stateTp := mkAppN stateTp vs
    let stateTp <- PrettyPrinter.delab stateTp
    liftCommandElabM $ elabCommand $ <- match br with
    | some br =>                                                            -- TODO: add macro a beta reduction here
       `(@[action] def $nm $[$vd]* : $stateTp -> $stateTp -> Prop := fun st1 st2 => exists $br, $act st1 st2)
    | _ =>
       `(@[action] def $nm $[$vd]* : $stateTp -> $stateTp -> Prop := $act)

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
  let vd := (<- getScope).varDecls
  Command.runTermElabM fun vs => do
    let stateTp := mkAppN (<- stsExt.get).typ vs
    let stateTp <- PrettyPrinter.delab stateTp
    let acts <- combineLemmas ``Or (<- stsExt.get).actions vs "transitions"
    let acts <- PrettyPrinter.delab acts
    liftCommandElabM $ elabCommand $ <-
      `(def $(mkIdent "Next") $[$vd]* : $stateTp -> $stateTp -> Prop := $acts)

elab ("invariant" <|> "safety") ":=" inv:term : command => do
  let vd := (<- getScope).varDecls
  Command.runTermElabM fun vs => do
    let stateTp := (<- stsExt.get).typ
    unless stateTp != default do throwError "State has not been declared so far"
    -- TODO: Check that `State` uses all section variables here
    let stateTp := mkAppN stateTp vs
    let stateTp <- PrettyPrinter.delab stateTp
    let num := (<- stsExt.get).invariants.length
    let inv_name := "inv" ++ toString num
    liftCommandElabM $ elabCommand $ <-
      `(@[inv] def $(mkIdent inv_name) $[$vd]* : $stateTp -> Prop := $inv)

def assembleInvariant : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  Command.runTermElabM fun vs => do
    let stateTp := mkAppN (<- stsExt.get).typ vs
    let stateTp <- PrettyPrinter.delab stateTp
    let invs <- combineLemmas ``And (<- stsExt.get).invariants vs "transitions"
    let invs <- PrettyPrinter.delab invs
    liftCommandElabM $ elabCommand $ <-
      `(def $(mkIdent "Inv") $[$vd]* : $stateTp -> Prop := $invs)

def instantiateSystem : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  assembleActions
  assembleInvariant
  Command.runTermElabM fun vs => do
    let stateTp   := mkAppN (<- stsExt.get).typ vs
    let stateTp   <- PrettyPrinter.delab stateTp
    let initSt    := mkAppN (<- mkConst "initalState?") vs
    let initSt    <- PrettyPrinter.delab initSt
    let nextTrans := mkAppN (<- mkConst "Next") vs
    let nextTrans <- PrettyPrinter.delab nextTrans
    let inv       := mkAppN (<- mkConst "Inv") vs
    let inv       <- PrettyPrinter.delab inv
    liftCommandElabM $ elabCommand $ <-
      `(instance $[$vd]* : RelationalTransitionSystem $stateTp where
          init := $initSt
          next := $nextTrans
          inv  := $inv)

elab "#gen_spec" : command => instantiateSystem

elab "inv_init_by" proof:tacticSeq : command => do
  let vd := (<- getScope).varDecls
  Command.runTermElabM fun vs => do
    let stateTp   := mkAppN (<- stsExt.get).typ vs
    let stateTp   <- PrettyPrinter.delab stateTp
    liftCommandElabM $ elabCommand $ <-
      `(theorem $(mkIdent "invInit") $[$vd]* : inv_init (σ := $stateTp) :=
       by unfold inv_init; exact by $proof)

elab "inv_inductive_by" proof:tacticSeq : command => do
  let vd := (<- getScope).varDecls
  Command.runTermElabM fun vs => do
    let stateTp   := mkAppN (<- stsExt.get).typ vs
    let stateTp   <- PrettyPrinter.delab stateTp
    liftCommandElabM $ elabCommand $ <-
      `(theorem $(mkIdent "invInductive") $[$vd]* : inv_inductive (σ := $stateTp) :=
      by unfold inv_inductive; exact by $proof)

type node1
type node2
instantiate DecidableEq node1

state :=
  foo : node1
  bar : node2

initial := fun x => True

action bazz (n m : Nat) := fun (x y) => n > m

action bazzz := fun x y => False

safety := fun st => 5 = 5
invariant := fun st => True
invariant := fun st => st.foo = st.foo

#gen_spec

inv_init_by sorry

inv_inductive_by sorry
