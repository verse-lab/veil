
import Lean
import LeanSts.DSLUtil
import Lean.Parser
import LeanSts.TransitionSystem
import LeanSts.WP
import LeanSts.Tactics
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
/--
  ```lean
  relation R : <Type>
  ```
  `realtion` command saves a `State` structure field declaration
-/
elab "relation" sig:Command.structSimpleBinder : command => do
  match sig with
  | `(Command.structSimpleBinder| $_:ident : $tp:term) =>
    let _ <- runTermElabM fun _ => elabTerm tp none
  | _ => throwErrorAt sig "Unsupported syntax"
  liftTermElabM do stsExt.modify (fun s => { s with rel_sig := s.rel_sig.push sig })

/-- Retrieves the current `State` structure and applies it to
    section variables `vs` -/
def stateTp (vs : Array Expr) : MetaM Expr := do
  let stateTp := (<- stsExt.get).typ
  unless stateTp != default do throwError "State has not been declared so far"
  return mkAppN stateTp vs

def prop := (Lean.Expr.sort (Lean.Level.zero))

def Term.explicitBinderF := Term.explicitBinder (requireType := false)
def Term.implicitBinderF := Term.implicitBinder (requireType := false)

/-- Transforms explicit binder into implicit one -/
def mkImplicitBinders : TSyntax `Lean.Parser.Term.bracketedBinder ->
  CommandElabM (TSyntax `Lean.Parser.Term.bracketedBinder)
  | `(Term.explicitBinderF| ($id:ident : $tp:term)) => do
    `(Term.bracketedBinderF| {$id:ident : $tp:term})
  | stx => return stx

/--
```lean
relation R : <Type>
```
This command defines a ghost relation. This relation will be just a
predicate over state. Here we do not support implicit quantification over
capital letters -/
elab "relation" nm:ident br:(bracketedBinder)* ":=" t:term : command => do
  let vd := (<- getScope).varDecls
  -- As we are going to call this predicate explicitly we want to make all
  -- section binders implicit
  let vd' <- vd.mapM (fun x => mkImplicitBinders x)
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    -- same trick as in "funcases"
    let stx <- `(by unhygienic cases st; exact $t)
    let stateTp <- PrettyPrinter.delab stateTp
                            -- we don't want to pass the state as an argument
                            -- so we use `exact_state` tactic that will assemble
                            -- the state from the context
    `(abbrev $nm $vd'* $br* (st : $stateTp := by exact_state) : Prop := $stx: term)

/--
assembles all declared `relation` predicates into a single `State` -/
def assembleState : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  Command.runTermElabM fun _ => do
    let nms := (<- stsExt.get).rel_sig
    liftCommandElabM $ elabCommand $ <-
      `(@[stateDef] structure $(mkIdent "State") $[$vd]* where $(mkIdent "mk"):ident :: $[$nms]*)

@[inherit_doc assembleState]
elab "#gen_state" : command => assembleState

/-- Declaring the initial state predicate -/
elab "initial" ini:term : command => do
  let vd := (<- getScope).varDecls
  elabCommand <| <- Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    let _ <- elabTerm ini (<- mkArrow stateTp prop)
    let stateTp <- PrettyPrinter.delab stateTp
    `(@[initDef, initSimp] def $(mkIdent "initalState?") $[$vd]* : $stateTp -> Prop := $ini)

/-- Declaring the initial state predicate in the form of a code -/
elab "after_init" "{" l:lang "}" : command => do
   -- Here we want to compute `WP[l]{st, st' = st} : State -> Prop`
   -- where `st'` is a final state. We expand `l` using `[lang1| l]`
   -- where `lang1` syntax will make sure that `WP` doesn't depend
   -- on the prestate state. As  `WP[l]{st, st' = st} : State -> Prop`
   -- doesn't depend on a prestate we can reduce it into `fun _ => Ini(st')`
   -- To get `Ini(st')` we should apply `fun _ => Ini(st')`  to any
   -- state, so we use `st'` as it is the only state we have in the context.
    let act <- `(fun st' => @wp _ (fun st => st' = st) [lang1| $l ] st')
    elabCommand $ <- `(initial $act)

/--
Transition system action definied via a relation
-/
syntax "action" declId (explicitBinders)? "=" term : command

/--
Transition system action definied via a code
All capital letters in `require` and in assigmnets are implicitly quantified
-/
syntax "action" declId (explicitBinders)? "=" "{" lang "}" : command

/--
Desugaring of the transition system action definied via a code, into the one
defined via a relation. Here we just compute the weakest precondition of the
code and then define the action as a relation.

Note: Unlike `after_init` we expand `l` using `[lang| l]` as we want action
to depend on the prestate.
-/
macro_rules
  | `(command| action $nm:declId $br:explicitBinders ? = { $l:lang }) => do
    let act <- `(fun st st' => @wp _ (fun st => st' = st) [lang| $l ] st)
    `(action $nm $br ? = $act)

/--
```lean
action name binders* = act
```
This command defines a transition system action. The action is defined as a relation
`act`, which is existential quantified over the `binders`.
-/
elab_rules : command
  | `(command| action $nm:declId $br:explicitBinders ? = $act) => do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    match br with
    | some br =>
      let _ <- elabTerm (<-`(term| fun st1 st2 => exists $br, $act st1 st2)) (<- mkArrow stateTp (<- mkArrow stateTp prop))
    | none =>
      let _ <- elabTerm act (<- mkArrow stateTp (<- mkArrow stateTp prop))
    let stateTp <- PrettyPrinter.delab stateTp
    match br with
    | some br =>                                                            -- TODO: add macro for a beta reduction here
       `(@[actDef, actSimp] def $nm $[$vd]* : $stateTp -> $stateTp -> Prop := fun st1 st2 => exists $br, $act st1 st2)
    | _ => do
       `(@[actDef, actSimp] def $nm $[$vd]* : $stateTp -> $stateTp -> Prop := $act)


def combineLemmas (op : Name) (exps: List Expr) (vs : Array Expr) (name : String) : MetaM Expr := do
    let exp0 :: exprs := exps
      | throwError ("There are no " ++ name ++ " defined")
    let exp0 <- etaExpand exp0
    let exps <- lambdaTelescope exp0 fun args exp0 => do
      let mut exps := exp0
      for exp in exprs do
        let exp := mkAppN exp args
        exps <- mkAppM op #[exp, exps]
      mkLambdaFVars args exps
    instantiateLambda exps vs

/--
Assembles all declared actions into a `Next` transition relation
-/
def assembleActions : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    let acts <- combineLemmas ``Or (<- stsExt.get).actions vs "transitions"
    let acts <- PrettyPrinter.delab acts
    `(@[actSimp] def $(mkIdent "Next") $[$vd]* : $stateTp -> $stateTp -> Prop := $acts)

/-- Safety property. All capital variables are implicitly quantified -/
elab "safety" safe:term : command => do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    let safe <- liftMacroM $ closeCapitals safe
    let stx <- `(funcases $safe)
    let _ <- elabByTactic stx (<- mkArrow stateTp prop)
    let stateTp <- PrettyPrinter.delab stateTp
    `(@[safeDef, safeSimp] def $(mkIdent "Safety") $[$vd]* : $stateTp -> Prop := $stx: term)

/-- Invariant of the transition system.
    All capital variables are implicitly quantified -/
elab "invariant" inv:term : command => do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    let inv <- liftMacroM $ closeCapitals inv
    let stx <- `(funcases $inv)
    let _ <- elabByTactic stx (<- mkArrow stateTp prop)
    let stateTp <- PrettyPrinter.delab stateTp
    let num := (<- stsExt.get).invariants.length
    let inv_name := "inv" ++ toString num
    `(@[invDef, invSimp] def $(mkIdent inv_name) $[$vd]* : $stateTp -> Prop := $stx: term)

/-- Assembles all declared invariants into a single `Inv` predicate -/
def assembleInvariant : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    let invs <- combineLemmas ``And (<- stsExt.get).invariants vs "invariants"
    let invs <- PrettyPrinter.delab invs
    `(@[invSimp] def $(mkIdent "Inv") $[$vd]* : $stateTp -> Prop := $invs)

/--
Instantiates the `RelationalTransitionSystem` type class with the declared actions, safety and invariant
-/
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
          inv  := $inv
          )

@[inherit_doc instantiateSystem]
elab "#gen_spec" : command => instantiateSystem

elab "prove_safety_init" proof:term : command => do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp   <- PrettyPrinter.delab (<- stateTp vs)
    `(theorem $(mkIdent "safety_init") $[$vd]* : safetyInit (σ := $stateTp) :=
       by unfold safetyInit;
          simp only [initSimp, safeSimp]
          intros $(mkIdent "st");
          exact $proof)

elab "prove_inv_init" proof:term : command => do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp   <- PrettyPrinter.delab (<- stateTp vs)
    `(theorem $(mkIdent "inv_init") $[$vd]* : invInit (σ := $stateTp) :=
       by unfold invInit
          simp only [initSimp, invSimp]
          intros $(mkIdent "st")
          exact $proof)

elab "prove_inv_inductive" proof:term : command => do
  let vd := (<- getScope).varDecls
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp   <- PrettyPrinter.delab (<- stateTp vs)
    `(theorem $(mkIdent "inv_inductive") $[$vd]* : invInductive (σ := $stateTp) :=
      by unfold invInductive;
         intros $(mkIdent "st1") $(mkIdent "st2")
         simp only [actSimp, invSimp, safeSimp]
         exact $proof)

attribute [initSimp] RelationalTransitionSystem.init
attribute [invSimp] RelationalTransitionSystem.inv
attribute [safeSimp] RelationalTransitionSystem.safe
