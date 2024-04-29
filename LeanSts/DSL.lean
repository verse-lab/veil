
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

elab "state" "=" fs:Command.structFields : command => do
  let scope <- getScope
  let vd := scope.varDecls
  elabCommand $ <-
    `(@[state] structure $(mkIdent "State") $[$vd]* where mk :: $fs)

elab "relation" sig:Command.structSimpleBinder : command => do
  match sig with
  | `(Command.structSimpleBinder| $_:ident : $tp:term) =>
    let _ <- runTermElabM fun _ => elabTerm tp none
  | _ => throwErrorAt sig "Unsupported syntax"
  liftTermElabM do stsExt.modify (fun s => { s with rel_sig := s.rel_sig.push sig })

def assembleState : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  Command.runTermElabM fun _ => do
    let nms := (<- stsExt.get).rel_sig
    liftCommandElabM $ elabCommand $ <-
      `(@[stateDef] structure $(mkIdent "State") $[$vd]* where $(mkIdent "mk"):ident :: $[$nms]*)

elab "#gen_state" : command => assembleState

def prop := (Lean.Expr.sort (Lean.Level.zero))

elab "initial" "=" ini:term : command => do
  let vd := (<- getScope).varDecls
  elabCommand <| <- Command.runTermElabM fun vs => do
    let stateTp := (<- stsExt.get).typ
    unless stateTp != default do throwError "State has not been declared so far"
    let stateTp := mkAppN stateTp vs
    let _ <- elabTermEnsuringType ini (<- mkArrow stateTp prop)
    let stateTp <- PrettyPrinter.delab stateTp
    `(@[initDef, initSimp] def $(mkIdent "initalState?") $[$vd]* : $stateTp -> Prop := $ini)

-- elab "my_def" ":=" trm:term : command => do
--   Command.runTermElabM fun vs => do
--     elabCommand <| <- `(def foo := $trm)

-- my_def := 5 5

-- type node1
-- type node2
-- instantiate DecidableEq node1

-- relation foo : node1
-- relation bar : node2

-- #eval assembleState

-- -- #print State


-- initial = fun _ => True 5

-- #check initalState?

syntax "action" declId (explicitBinders)? "=" term : command


elab_rules : command
  | `(command| action $nm:declId $br:explicitBinders ? = $act) => do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp := (<- stsExt.get).typ
    unless stateTp != default do throwError "State has not been declared so far"
    let stateTp := mkAppN stateTp vs
    stsExt.modify fun s => { s with typ_vs := stateTp }
    match br with
    | some br =>
      let _ <- elabTerm (<-`(term| fun st1 st2 => exists $br, $act st1 st2)) (<- mkArrow stateTp (<- mkArrow stateTp prop))
    | none =>
      let _ <- elabTerm act (<- mkArrow stateTp (<- mkArrow stateTp prop))
    let stateTp <- PrettyPrinter.delab stateTp
    match br with
    | some br =>                                                            -- TODO: add macro a beta reduction here
       `(@[actDef, actSimp] def $nm $[$vd]* : $stateTp -> $stateTp -> Prop := fun st1 st2 => exists $br, $act st1 st2)
    | _ => do
       `(@[actDef, actSimp] def $nm $[$vd]* : $stateTp -> $stateTp -> Prop := $act)

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
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp := mkAppN (<- stsExt.get).typ vs
    let stateTp <- PrettyPrinter.delab stateTp
    let acts <- combineLemmas ``Or (<- stsExt.get).actions vs "transitions"
    let acts <- PrettyPrinter.delab acts
    `(@[actSimp] def $(mkIdent "Next") $[$vd]* : $stateTp -> $stateTp -> Prop := $acts)


elab "safety" "=" safe:term : command => do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp := (<- stsExt.get).typ
    unless stateTp != default do throwError "State has not been declared so far"
    let stateTp := mkAppN stateTp vs
    let stx <- `(Term.byTactic| by intro st; unhygienic cases st; exact $safe)
    let _ <- elabByTactic stx (<- mkArrow stateTp prop)
    let stateTp <- PrettyPrinter.delab stateTp
    `(@[safeDef, safeSimp] def $(mkIdent "Safety") $[$vd]* : $stateTp -> Prop := $stx: byTactic)

elab "invariant" "=" inv:term : command => do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp := (<- stsExt.get).typ
    unless stateTp != default do throwError "State has not been declared so far"
    let stateTp := mkAppN stateTp vs
    let stx <- `(Term.byTactic| by intro st; unhygienic cases st; exact $inv)
    let _ <- elabByTactic stx (<- mkArrow stateTp prop)
    let stateTp <- PrettyPrinter.delab stateTp
    let num := (<- stsExt.get).invariants.length
    let inv_name := "inv" ++ toString num
    `(@[invDef, invSimp] def $(mkIdent inv_name) $[$vd]* : $stateTp -> Prop := $stx: byTactic)

def assembleInvariant : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp := mkAppN (<- stsExt.get).typ vs
    let stateTp <- PrettyPrinter.delab stateTp
    let invs <- combineLemmas ``And (<- stsExt.get).invariants vs "transitions"
    let invs <- PrettyPrinter.delab invs
    `(@[invSimp] def $(mkIdent "Inv") $[$vd]* : $stateTp -> Prop := $invs)

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
    let safe      := mkAppN (<- mkConst "Safety") vs
    let safe      <- PrettyPrinter.delab safe
    let inv       := mkAppN (<- mkConst "Inv") vs
    let inv       <- PrettyPrinter.delab inv
    liftCommandElabM $ elabCommand $ <-
      `(instance $[$vd]* : RelationalTransitionSystem $stateTp where
          safe := $safe
          init := $initSt
          next := $nextTrans
          inv    := $inv
          )

elab "#gen_spec" : command => instantiateSystem

elab "prove_safety_init" proof:term : command => do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp   := mkAppN (<- stsExt.get).typ vs
    let stateTp   <- PrettyPrinter.delab stateTp
    `(theorem $(mkIdent "safety_init") $[$vd]* : safetyInit (σ := $stateTp) :=
       by unfold safetyInit;
          simp only [initSimp, safeSimp]
          intros $(mkIdent "st");
          exact $proof)

elab "prove_inv_init" proof:term : command => do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp   := mkAppN (<- stsExt.get).typ vs
    let stateTp   <- PrettyPrinter.delab stateTp
    `(theorem $(mkIdent "inv_init") $[$vd]* : invInit (σ := $stateTp) :=
       by unfold invInit
          simp only [initSimp, invSimp]
          intros $(mkIdent "st")
          exact $proof)

elab "prove_inv_inductive" proof:term : command => do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp   := mkAppN (<- stsExt.get).typ vs
    let stateTp   <- PrettyPrinter.delab stateTp
    `(theorem $(mkIdent "inv_inductive") $[$vd]* : invInductive (σ := $stateTp) :=
      by unfold invInductive;
         intros $(mkIdent "st1") $(mkIdent "st2")
         simp only [actSimp, invSimp, safeSimp]
         exact $proof)

attribute [initSimp] RelationalTransitionSystem.init
attribute [invSimp] RelationalTransitionSystem.inv
-- attribute [actSimp] RelationalTransitionSystem.next
attribute [safeSimp] RelationalTransitionSystem.safe



-- action bazz (n m : Nat) := fun (x y) => n > m

-- action bazzz := fun x y => False

-- safety = fun st => 5 = 5
-- invariant = fun st => True
-- invariant = fun st => st.foo = st.foo

-- #gen_spec

-- inv_init_by
--   simp only [invSimp, initSimp]
--   sorry

-- inv_inductive_by
--   simp only [invSimp, actSimp]
--   sorry
