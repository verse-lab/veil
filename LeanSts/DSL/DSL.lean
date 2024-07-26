import Lean
import Lean.Parser
import LeanSts.TransitionSystem
import LeanSts.Tactic
import LeanSts.DSL.Util
import LeanSts.DSL.WP
import LeanSts.DSL.Tactic
import LeanSts.DSL.Trace
open Lean Elab Command Term Meta Lean.Parser RelationalTransitionSystem

-- Modelled after the Ivy language
-- https://github.com/kenmcmil/ivy/blob/master/doc/language.md

macro "type" id:ident : command => `(variable ($id : Type) [DecidableEq $id])
macro "instantiate" t:term : command => `(variable [$t])
macro "instantiate" nm:ident " : " t:term : command => `(variable [$nm : $t])

elab "state" "=" fs:Command.structFields : command => do
  let vd := (<- getScope).varDecls
  elabCommand $ <-
    `(@[state] structure $(mkIdent `State) $[$vd]* where mk :: $fs)

/-- Defines a constant, relation, or function, validating its type before adding it. -/
def defineStateComponent
  (sig: TSyntax `Lean.Parser.Command.structSimpleBinder)
  (validateTp : Expr → CommandElabM Bool := fun _ => pure true)
  (failureMsg : TSyntax `Lean.Parser.Command.structSimpleBinder → CommandElabM Unit := fun _ => throwErrorAt sig s!"{sig} is not of the expected type")
   : CommandElabM Unit := do
  let tp ← do match sig with
  | `(Command.structSimpleBinder| $_:ident : $tp:term) =>
    runTermElabM fun _ => elabTerm tp none
  | _ => throwErrorAt sig "Unsupported syntax"
  if ← validateTp tp then
    liftTermElabM do stsExt.modify (fun s => { s with sig := s.sig.push sig })
  else
    failureMsg sig

/--
  ```lean
  relation R : <Type>
  ```
  `relation` command saves a `State` structure field declaration
-/
elab "relation" sig:Command.structSimpleBinder : command => do
  defineStateComponent sig
    (fun (tp : Expr) => do
      -- If you need to debug the forallTelescope:
      -- let _ ← Array.mapM (fun x => return s!"{← ppExpr x}")
      let returnsProp ← liftTermElabM $ forallTelescope tp (fun _ b => do return b.isProp)
      return tp.isArrow && returnsProp)
    (fun sig => throwErrorAt sig "Invalid type: relations must return Prop")

/-- `individual` command saves a `State` structure field declaration -/
elab "individual" sig:Command.structSimpleBinder : command => do
  defineStateComponent sig
    (fun (tp : Expr) => return !tp.isArrow)
    (fun sig => throwErrorAt sig "Invalid type: constants must not be arrow types")

/-- `function` command saves a `State` structure field declaration -/
elab "function" sig:Command.structSimpleBinder : command => do
  defineStateComponent sig
    (fun (tp : Expr) => do return tp.isArrow)
    (fun sig => throwErrorAt sig "Invalid type: functions must have arrow type")

/--
```lean
relation R : <Type>
```
This command defines a ghost relation. This relation will be just a
predicate over state. -/
elab "relation" nm:ident br:(bracketedBinder)* ":=" t:term : command => do
  let vd := (<- getScope).varDecls
  -- As we are going to call this predicate explicitly we want to make all
  -- section binders implicit
  let vd' <- vd.mapM (fun x => mkImplicitBinders x)
  elabCommand $ <-  Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    let stateTp <- PrettyPrinter.delab stateTp
    let stx' <- funcasesM t vs
    elabBindersAndCapitals br vs stx' fun _ e => do
      let e <- my_delab e
      `(abbrev $nm $[$vd']* $br* ($(mkIdent `st) : $stateTp := by exact_state) : Prop := $e)

/--
assembles all declared `relation` predicates into a single `State` -/
def assembleState : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  Command.runTermElabM fun _ => do
    let nms := (<- stsExt.get).sig
    let sdef ← `(@[stateDef] structure $(mkIdent `State) $[$vd]* where $(mkIdent `mk):ident :: $[$nms]*)
    let injEqLemma := (mkIdent $ `State ++ `mk ++ `injEq)
    let smtAttr ← `(attribute [smtSimp] $injEqLemma)
    liftCommandElabM $ elabCommand $ sdef
    liftCommandElabM $ elabCommand $ smtAttr

@[inherit_doc assembleState]
elab "#gen_state" : command => assembleState

/-- Declaring the initial state predicate -/
elab "initial" ini:term : command => do
  elabCommand <| <- Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    let _ <- elabTerm ini (<- mkArrow stateTp prop)
    let stateTp <- PrettyPrinter.delab stateTp
    `(@[initDef, initSimp] def $(mkIdent `initalState?) : $stateTp -> Prop := $ini)

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
       `(@[actDef, actSimp] def $nm : $stateTp -> $stateTp -> Prop := fun st1 st2 => exists $br, $act st1 st2)
    | _ => do
       `(@[actDef, actSimp] def $nm : $stateTp -> $stateTp -> Prop := $act)


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
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    let acts <- combineLemmas ``Or (<- stsExt.get).actions vs "transitions"
    let acts <- PrettyPrinter.delab acts
    `(@[actSimp] def $(mkIdent `Next) : $stateTp -> $stateTp -> Prop := $acts)

/-- Safety property. All capital variables are implicitly quantified -/
elab "safety" safe:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    -- let safe <- liftMacroM $ closeCapitals safe
    let stateTp <- PrettyPrinter.delab stateTp
    let stx <- funcasesM safe vs
    elabBindersAndCapitals #[] vs stx fun _ e => do
      let e <- my_delab e
      `(@[safeDef, safeSimp, invSimp] def $(mkIdent `Safety) : $stateTp -> Prop := fun $(mkIdent `st) => $e: term)

/-- Invariant of the transition system.
    All capital variables are implicitly quantified -/
elab "invariant" inv:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    -- let inv <- liftMacroM $ closeCapitals inv
    let stx <- funcasesM inv vs
    let _ <- elabByTactic stx (<- mkArrow stateTp prop)
    let stateTp <- PrettyPrinter.delab stateTp
    let num := (<- stsExt.get).invariants.length
    let inv_name := "inv" ++ toString num
    elabBindersAndCapitals #[] vs stx fun _ e => do
      let e <- my_delab e
      `(@[invDef, invSimp] def $(mkIdent $ Name.mkSimple inv_name) : $stateTp -> Prop := fun $(mkIdent `st) => $e: term)

/-- Assembles all declared invariants into a single `Inv` predicate -/
def assembleInvariant : CommandElabM Unit := do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    let invs <- combineLemmas ``And ((<- stsExt.get).invariants ++ (<- stsExt.get).safeties) vs "invariants"
    let invs <- PrettyPrinter.delab invs
    `(@[invSimp] def $(mkIdent `Inv) : $stateTp -> Prop := $invs)

/--
Instantiates the `RelationalTransitionSystem` type class with the declared actions, safety and invariant
-/
def instantiateSystem (name : Name): CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  assembleActions
  assembleInvariant
  Command.runTermElabM fun vs => do
    let stateTp   := mkAppN (<- stsExt.get).typ vs
    let stateTp   <- PrettyPrinter.delab stateTp
    let initSt    := mkAppN (<- mkConst `initalState?) vs
    let initSt    <- PrettyPrinter.delab initSt
    let nextTrans := mkAppN (<- mkConst `Next) vs
    let nextTrans <- PrettyPrinter.delab nextTrans
    let safe      := mkAppN (<- mkConst `Safety) vs
    let safe      <- PrettyPrinter.delab safe
    let inv       := mkAppN (<- mkConst `Inv) vs
    let inv       <- PrettyPrinter.delab inv
    let stx       <-
      `(instance (priority := low) $(mkIdent name) $[$vd]* : RelationalTransitionSystem $stateTp where
          safe := $safe
          init := $initSt
          next := $nextTrans
          inv  := $inv
          )
    liftCommandElabM $ elabCommand $ stx

@[inherit_doc instantiateSystem]
elab "#gen_spec" name:ident : command => instantiateSystem name.getId

elab "prove_inv_init" proof:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    `(theorem $(mkIdent `inv_init) : invInit (σ := $stateTp) :=
       by unfold invInit
          -- simp only [initSimp, invSimp]
          intros $(mkIdent `st)
          exact $proof)

elab "prove_inv_safe" proof:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp   <- PrettyPrinter.delab (<- stateTp vs)
    `(theorem $(mkIdent `safety_init) : invSafe (σ := $stateTp) :=
       by unfold invSafe;
          -- simp only [initSimp, safeSimp]
          intros $(mkIdent `st);
          exact $proof)

elab "prove_inv_inductive" proof:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp   <- PrettyPrinter.delab (<- stateTp vs)
    `(theorem $(mkIdent `inv_inductive) : invInductive (σ := $stateTp) :=
      by unfold invInductive;
         intros $(mkIdent `st1) $(mkIdent `st2)
        --  simp only [actSimp, invSimp, safeSimp]
         exact $proof)

attribute [initSimp] RelationalTransitionSystem.init
attribute [invSimp] RelationalTransitionSystem.inv
attribute [safeSimp] RelationalTransitionSystem.safe
