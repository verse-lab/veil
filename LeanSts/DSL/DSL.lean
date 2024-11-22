import Lean
import Lean.Parser
import Lean.Meta.Tactic.TryThis

import LeanSts.TransitionSystem
import LeanSts.Tactic
import LeanSts.DSL.Util
import LeanSts.DSL.WP
import LeanSts.DSL.Tactic
import LeanSts.DSL.Trace
import LeanSts.SMT.Preparation

open Lean Elab Command Term Meta Lean.Parser Tactic.TryThis RelationalTransitionSystem

-- Modelled after the Ivy language
-- https://github.com/kenmcmil/ivy/blob/master/doc/language.md

declare_syntax_cat propertyName
syntax "[" ident "]": propertyName

def _root_.Lean.TSyntax.getPropertyName (stx : TSyntax `propertyName) : Name :=
  match stx with
  | `(propertyName| [$id]) => id.getId
  | _ => unreachable!

def getPropertyNameD (stx : Option (TSyntax `propertyName)) (default : Name) :=
  match stx with
  | some stx => stx.getPropertyName
  | none => default

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
    /- e.g. `relation initial_msg : address → address → round → value → Prop` -/
  | `(Command.structSimpleBinder| $_:ident : $tp:term) =>
    runTermElabM fun _ => elabTerm tp none
  | _ => throwErrorAt sig "Unsupported syntax {sig}"
  if ← validateTp tp then
    liftTermElabM do stsExt.modify (fun s => { s with sig := s.sig.push sig })
  else
    failureMsg sig

/-- Declare a relation, giving only the type. Example:
  ```lean
  relation R : address → round → Prop
  ```
-/
elab "relation" sig:Command.structSimpleBinder : command => do
  defineStateComponent sig
    (fun (tp : Expr) => do
      -- If you need to debug the forallTelescope:
      -- let _ ← Array.mapM (fun x => return s!"{← ppExpr x}")
      let returnsProp ← liftTermElabM $ forallTelescope tp (fun _ b => do return b.isProp)
      return tp.isArrow && returnsProp)
    (fun sig => throwErrorAt sig "Invalid type: relations must return Prop")

/-- Declare a relation, giving names to the arguments. Example:
  ```lean
  relation sent (n : address) (r : round)
  ```
-/
elab "relation" nm:ident br:(bracketedBinder)* (":" "Prop")? : command => do
  let types ← br.mapM fun m => match m with
    | `(bracketedBinder| ($_arg:ident : $tp:term)) => return (mkIdent tp.raw.getId)
    | _ => throwError "Invalid syntax"
  -- I'd want this to work, but it doesn't:
  -- let typesStx ← `(term| $[$types]→* → Prop)
  let typeStx ← mkArrowStx types.toList (← `(Prop))
  let rel ← `(relation $nm:ident : $typeStx)
  elabCommand rel

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

/-- Declare a function, giving names to the arguments. Example:
  ```lean
  function currentRound (n : address) : round
  ```
-/
elab "function" nm:ident br:(bracketedBinder)* ":" dom:term: command => do
  let types ← br.mapM fun m => match m with
    | `(bracketedBinder| ($_arg:ident : $tp:term)) => return (mkIdent tp.raw.getId)
    | _ => throwError "Invalid syntax"
  let typeStx ← mkArrowStx types.toList dom
  let rel ← `(function $nm:ident : $typeStx)
  elabCommand rel

/-- Declare a ghost relation, i.e. a predicate over state. Example:
  ```lean
  relation R : <Type> := [definition]
  ```
-/
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
      `(@[actSimp, invSimp] abbrev $nm $[$vd']* $br* ($(mkIdent `st) : $stateTp := by exact_state) : Prop := $e)

/--
assembles all declared `relation` predicates into a single `State` -/
def assembleState : CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  Command.runTermElabM fun vs => do
    let nms := (<- stsExt.get).sig
    let sdef ← `(@[stateDef] structure $(mkIdent `State) $[$vd]* where $(mkIdent `mk):ident :: $[$nms]*)
    let injEqLemma := (mkIdent $ `State ++ `mk ++ `injEq)
    let smtAttr ← `(attribute [smtSimp] $injEqLemma)
    liftCommandElabM $ elabCommand $ sdef
    liftCommandElabM $ elabCommand $ smtAttr

@[inherit_doc assembleState]
elab "#gen_state" : command => assembleState

open Tactic in
elab tk:"conv! " conv:conv " => " e:term : term => do
  let e ← Elab.Term.elabTermAndSynthesize e none
  let (rhs, g) ← Conv.mkConvGoalFor e
  _ ← Tactic.run g.mvarId! (do
    evalTactic conv
    for mvarId in (← getGoals) do
      liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
    pruneSolvedGoals
    let e' ← instantiateMVars rhs
    trace[dsl] "{e'}"
  )
  return rhs

/-- We use this to evaluate `wlp` inside function bodies at definition time.
  Otherwise it has to be evaluated in the kernel during proofs, which is very slow.
  `conv!` applies a tactic to a term. -/
def simplifyTerm (t : TSyntax `term) : TermElabM (TSyntax `term) := do
  let (actSimp, smtSimp) := (mkIdent `actSimp, mkIdent `smtSimp)
  -- Reduce the body of the function
  let t' ← `(term| by
    -- Try simplifying first, but this might fail if there's no `wlp` in the
    -- definition, e.g. for transitions that are not actions.
    -- If that fails, we try to evaluate the term as is.
    -- We do `simp only [and_assoc]` at the end to normalize conjunctions.
    first | (let t := conv! (dsimp only [$actSimp:ident]; simp only [$smtSimp:ident]; simp only [and_assoc]; repeat (pushEqLeft; simp only [quantifierElim])) => $t; exact t) | exact $t)
  return t'

/-- Declaring the initial state predicate -/
elab "initial" ini:term : command => do
  elabCommand <| <- Command.runTermElabM fun vs => do
    let stateTp ← PrettyPrinter.delab $ ← stateTp vs
    let expectedType ← `($stateTp → Prop)
    let ini ←  simplifyTerm ini
    `(@[initDef, initSimp] def $(mkIdent `initialState?) : $expectedType := $ini)

/-- Declaring the initial state predicate in the form of a code -/
elab "after_init" "{" l:lang "}" : command => do
   -- Here we want to compute `WP[l]{st, st' = st} : State -> Prop`
   -- where `st'` is a final state. We expand `l` using `[lang1| l]`
   -- where `lang1` syntax will make sure that `WP` doesn't depend
   -- on the prestate state. As  `WP[l]{st, st' = st} : State -> Prop`
   -- doesn't depend on a prestate we can reduce it into `fun _ => Ini(st')`
   -- To get `Ini(st')` we should apply `fun _ => Ini(st')`  to any
   -- state, so we use `st'` as it is the only state we have in the context.
    let (ret, st, st', wlp) := (mkIdent `ret, mkIdent `st, mkIdent `st', mkIdent ``wlp)
    let act ← Command.runTermElabM fun vs => (do
      let stateTp ← PrettyPrinter.delab $ ← stateTp vs
      `(fun ($st' : $stateTp) => @$wlp _ _ (fun $ret $st => $st' = $st) [lang1| $l ] $st')
    )
    elabCommand $ ← `(initial $act)

/--
Transition defined via a two-state relation.
-/
syntax "transition" ident (explicitBinders)? "=" term : command

/--
Transition defined as an imperative program. We call these "actions".
All capital letters in `require` and in assignments are implicitly quantified.
-/
syntax "action" ident (explicitBinders)? "=" "{" lang "}" : command

/-- `act.fn` : a function that returns a transition relation with return
  value (type `σ → (σ × ρ) → Prop`), universally quantified over `binders`. -/
def elabCallableFn (nm : TSyntax `ident) (br : Option (TSyntax `Lean.explicitBinders)) (l : TSyntax `lang) : CommandElabM Unit := do
  let (originalName, nm) := (nm, toFnIdent nm)
  elabCommand $ ← Command.runTermElabM fun vs => do
    let (ret, st, stret, wlp) := (mkIdent `ret', mkIdent `st, mkIdent `stret, mkIdent ``wlp)
    let stateTp ← PrettyPrinter.delab $ ← stateTp vs
    -- `σ → (σ × ρ) → Prop`, with binders universally quantified
    -- $stret = ($st', $ret')
    let act <- `(fun ($st : $stateTp) $stret =>
      @$wlp _ _ (fun $ret ($st : $stateTp) => (Prod.fst $stret) = $st ∧ $ret = (Prod.snd $stret)) [lang| $l ] $st)
    -- let tp ← `(term|$stateTp -> ($stateTp × $retTp) -> Prop)
    let (st, st') := (mkIdent `st, mkIdent `st')
    match br with
    | some br =>
      let br ← toBracketedBinderArray br
      -- $(← simplifyTerm $ ← `(fun $st $st' => exists $br, $tr $st $st'))
      `(@[actSimp] def $nm $br* := $(← simplifyTerm $ ← `(fun $st $st' => $act $st $st')))
    | _ => do
      `(@[actSimp] def $nm:ident := $(← simplifyTerm act))
  -- Introduce notation to automatically provide the section arguments
  elabCommand $ ← Command.runTermElabM fun vs => do
    let args ← vs.mapM (fun v => do
      let t ← PrettyPrinter.delab v
      let isHygienicName := (extractMacroScopes t.raw.getId).scopes.length > 0
      if isHygienicName then return ← `(term|_) else return t
    )
    let strName ← `(Lean.Parser.Command.notationItem|$(Lean.quote ("!" ++ originalName.getId.toString)):str)
    `(local notation (priority := default) $strName => @$nm $args*)

/--
Desugaring an imperative code action into a two-state transition. Here we compute
the weakest precondition of the program and then define the transition relation.

Note: Unlike `after_init` we expand `l` using `[lang| l]` as we want the transition
to refer to both pre-state and post-state.
-/
elab_rules : command
  | `(command| action $nm:ident $br:explicitBinders ? = { $l:lang }) => do
    let (ret, st, st', wlp) := (mkIdent `ret, mkIdent `st, mkIdent `st', mkIdent ``wlp)
    -- `σ → σ → Prop`, with binders existentially qunatified
    let tr ← Command.runTermElabM fun vs => (do
      let stateTp ← PrettyPrinter.delab $ ← stateTp vs
      `(fun ($st $st' : $stateTp) => @$wlp _ _ (fun $ret $st => $st' = $st) [lang| $l ] $st)
    )
    elabCommand $ ← `(transition $(toTrIdent nm) $br ? = $tr)
    elabCallableFn nm br l

/--
```lean
transition name binders* = tr
```
This command defines:
- `act`: a transition relation `σ → σ → Prop`, existentially quantified over the `binders`.-/
elab_rules : command
  | `(command| transition $nm:ident $br:explicitBinders ? = $tr) => do
 elabCommand $ ← Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    let (st, st') := (mkIdent `st, mkIdent `st')
    let expectedType ← mkArrow stateTp (← mkArrow stateTp prop)
    -- IMPORTANT: we elaborate the term here so we get an error if it doesn't type check
    match br with
    | some br =>
      let _ <- elabTerm (<-`(term| fun $st $st' => exists $br, $tr $st $st')) expectedType
    | none =>
      let _ <- elabTerm tr expectedType
    -- The actual command (not term) elaboration happens here
    let stateTpT <- PrettyPrinter.delab stateTp
    let expectedType <- `($stateTpT -> $stateTpT -> Prop)
    match br with
    | some br =>
      -- TODO: add macro for a beta reduction here
      `(@[actDef, actSimp] def $nm : $expectedType := $(← simplifyTerm $ ← `(fun $st $st' => exists $br, $tr $st $st')))
    | _ => do
      `(@[actDef, actSimp] def $nm:ident : $expectedType := $(← simplifyTerm tr))


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
elab "safety" name:(propertyName)? safe:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    -- let safe <- liftMacroM $ closeCapitals safe
    let stateTp <- PrettyPrinter.delab stateTp
    let stx <- funcasesM safe vs
    let defaultName := Name.mkSimple $ s!"safety_{(<- stsExt.get).safeties.length}"
    let name := getPropertyNameD name defaultName
    elabBindersAndCapitals #[] vs stx fun _ e => do
      let e <- my_delab e
      `(@[safeDef, safeSimp, invSimp] def $(mkIdent name) : $stateTp -> Prop := fun $(mkIdent `st) => $e: term)

/-- Invariant of the transition system.
    All capital variables are implicitly quantified -/
elab "invariant" name:(propertyName)? inv:term : command => do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- stateTp vs
    -- let inv <- liftMacroM $ closeCapitals inv
    let stx <- funcasesM inv vs
    let _ <- elabByTactic stx (<- mkArrow stateTp prop)
    let stateTp <- PrettyPrinter.delab stateTp
    let defaultName := Name.mkSimple $ s!"inv_{(<- stsExt.get).invariants.length}"
    let name := getPropertyNameD name defaultName
    elabBindersAndCapitals #[] vs stx fun _ e => do
      let e <- my_delab e
      `(@[invDef, invSimp] def $(mkIdent name) : $stateTp -> Prop := fun $(mkIdent `st) => $e: term)

/-- Assembles all declared invariants (including safety properties) into a single `Invariant` predicate -/
def assembleInvariant : CommandElabM Unit := do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    let invs <- combineLemmas ``And ((<- stsExt.get).invariants ++ (<- stsExt.get).safeties) vs "invariants"
    let invs <- PrettyPrinter.delab invs
    `(@[invSimp] def $(mkIdent `Invariant) : $stateTp -> Prop := $invs)

/-- Assembles all declared safety properties into a single `Safety` predicate -/
def assembleSafeties : CommandElabM Unit := do
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- PrettyPrinter.delab (<- stateTp vs)
    let safeties <- combineLemmas ``And (<- stsExt.get).safeties vs "safeties"
    let safeties <- PrettyPrinter.delab safeties
    `(@[invSimp] def $(mkIdent `Safety) : $stateTp -> Prop := $safeties)

/--
Instantiates the `RelationalTransitionSystem` type class with the declared actions, safety and invariant
-/
def instantiateSystem (name : Name): CommandElabM Unit := do
  let vd := (<- getScope).varDecls
  assembleActions
  assembleInvariant
  assembleSafeties
  Command.runTermElabM fun vs => do
    -- set the name
    stsExt.modify (fun s => { s with name := name })
    let stateTp   := mkAppN (<- stsExt.get).typ vs
    let stateTp   <- PrettyPrinter.delab stateTp
    let initSt    := mkAppN (<- mkConst `initialState?) vs
    let initSt    <- PrettyPrinter.delab initSt
    let nextTrans := mkAppN (<- mkConst `Next) vs
    let nextTrans <- PrettyPrinter.delab nextTrans
    let safe      := mkAppN (<- mkConst `Safety) vs
    let safe      <- PrettyPrinter.delab safe
    let inv       := mkAppN (<- mkConst `Invariant) vs
    let inv       <- PrettyPrinter.delab inv
    let stx       <-
      `(instance (priority := low) $(mkIdent name) $[$vd]* : RelationalTransitionSystem $stateTp where
          safe := $safe
          init := $initSt
          next := $nextTrans
          inv  := $inv
          )
    liftCommandElabM $ elabCommand $ stx

def setOptionPrintModel : CommandElabM Unit := do
  elabCommand (← `(command|set_option $(mkIdent "trace.sauto.model".toName) true))

@[inherit_doc instantiateSystem]
elab "#gen_spec" name:ident : command => do
  instantiateSystem name.getId

def checkTheorem (theoremName : Name) (cmd : TSyntax `command): CommandElabM Bool := do
  withTraceNode `dsl.perf.checkInvariants (fun _ => return m!"elab {theoremName} definition") do
  let env ← getEnv
  -- FIXME: I think we want to run `elabCommand` without `withLogging`
  elabCommand cmd
  -- Check the `Expr` for the given theorem
  let th ← getConstInfo theoremName
  let isProven ← match th with
    | ConstantInfo.thmInfo attempt => pure <| !attempt.value.hasSyntheticSorry
    | _ => throwError s!"checkTheorem: expected {theoremName} to be a theorem"
  -- We only add the theorem to the environment if it successfully type-checks
  -- i.e. we restore the original environment if the theorem is not proven
  if !isProven then
    setEnv env
  return isProven

def getSystemTpStx (vs : Array Expr) : TermElabM Term := do
  let systemTp ← PrettyPrinter.delab $ mkAppN (mkConst (← stsExt.get).name) vs
  return systemTp

def getStateTpStx (vs : Array Expr) : TermElabM Term := do
  let stateTp ← PrettyPrinter.delab (← stateTp vs)
  return stateTp

inductive CheckType
  | init
  | action (actName : Name)
deriving BEq

/-- Generate the check theorem for the given invariant an `CheckType` (either `init` or `action`) -/
def getCheckFor (invName : Name) (ct : CheckType) (vs : Array Expr) : TermElabM (Name × Name × TSyntax `command × TSyntax `command) := do
  let env ← getEnv
  let .some _ := env.find? invName
    | throwError s!"Invariant {invName} not found"
  let inv ← Term.mkConst invName

  let (systemTp, stateTp, st, st') := (← getSystemTpStx vs, ← getStateTpStx vs, mkIdent `st, mkIdent `st')
  let property ← PrettyPrinter.delab $ mkAppN inv vs

  let (tpStx, thName, proofScript) ← match ct with
  | .init => do
      let initTpStx ← `(∀ ($st : $stateTp), ($systemTp).$(mkIdent `init)  $st → $property $st)
      let initThmName := s!"init_{invName}".toName
      let proofScript ← `(by unhygienic intros; solve_clause [$(mkIdent `initSimp)])
      pure (initTpStx, initThmName, proofScript)
  | .action actName => do
      let .some _ := (← getEnv).find? actName
        | throwError s!"action {actName} not found"
      let act ← Term.mkConst actName
      let actStx ← PrettyPrinter.delab $ mkAppN act vs
      let actTpStx ← `(∀ ($st $st' : $stateTp), ($systemTp).$(mkIdent `inv) $st → $actStx $st $st' → $property $st')
      let actThName := s!"{actName}_{invName}".toName
      let actId := Lean.mkIdent actName
      let proofScript ← `(by unhygienic intros; solve_clause [$actId])
      pure (actTpStx, actThName, proofScript)
  let checkTheorem ← `(@[invProof] theorem $(mkIdent thName) : $tpStx := $proofScript)
  let failedTheorem ← `(@[invProof] theorem $(mkIdent thName) : $tpStx := sorry)
  return (invName, (thName, checkTheorem, failedTheorem))

inductive CheckInvariantsBehaviour
  /-- `#check_invariants` -/
  | checkTheorems
  /-- `#check_invariants?` -/
  | printTheorems
  /-- `#check_invariants!` -/
  | printAndCheckTheorems

/--
  Prints output similar to that of the `ivy_check` command.
-/
def checkInvariants (stx : Syntax) (behaviour : CheckInvariantsBehaviour := .checkTheorems) : CommandElabM Unit := do
  -- Generate theorems to check in the initial state and after each action
  let (initChecks, invChecks) ← Command.runTermElabM fun vs => do
    let invs := ((← stsExt.get).invariants ++ (← stsExt.get).safeties)
    let acts := (<- stsExt.get).actions
    let mut initChecks := #[]
    let mut actChecks := #[]
    -- TODO: extract the generic part of this code out
    -- (1) Collect checks that invariants hold in the initial state
    for inv in invs do
      let invName := inv.constName!
      initChecks := initChecks.push (← getCheckFor invName CheckType.init vs)
    -- (2) Collect checks that invariants hold after each action
    for act in acts do
        let actName := act.constName!
        let mut checks := #[]
        for inv in invs do
          let invName := inv.constName!
          checks := checks.push (← getCheckFor invName (CheckType.action actName) vs)
        actChecks := actChecks.push (actName, checks)
    pure (initChecks, actChecks)

  let mut theorems := #[] -- collect Lean expression to report for `#check_invariants?` and `#check_invariants!`
  match behaviour with
  | .printTheorems =>
    let actInvChecks := Array.flatten $ invChecks.map (fun (_, actChecks) => actChecks)
    for (_, (_, thCmd, _)) in (initChecks ++ actInvChecks) do
      theorems := theorems.push thCmd
    displaySuggestion stx theorems
  | .checkTheorems | .printAndCheckTheorems =>
    let mut msgs := #[]
    msgs := msgs.push "Initialization must establish the invariant:"
    for (invName, (thName, thCmd, sorryThm)) in initChecks do
      let success ← checkTheorem thName thCmd
      msgs := msgs.push s!"  {invName} ... {if success then "✅" else "❌"}"
      let thm := if success then thCmd else sorryThm
      theorems := theorems.push thm
    msgs := msgs.push "The following set of actions must preserve the invariant:"
    for (actName, actChecks) in invChecks do
      msgs := msgs.push s!"  {actName}"
      for (invName, (thName, thCmd, sorryThm)) in actChecks do
        let success ← checkTheorem thName thCmd
        msgs := msgs.push s!"    {invName} ... {if success then "✅" else "❌"}"
        let thm := if success then thCmd else sorryThm
        theorems := theorems.push thm
    let msg := (String.intercalate "\n" msgs.toList) ++ "\n"
    match behaviour with
    | .checkTheorems => dbg_trace msg
    | .printAndCheckTheorems => displaySuggestion stx theorems (preMsg := msg)
    | _ => unreachable!
  where displaySuggestion (stx : Syntax) (theorems : Array (TSyntax `command)) (preMsg : Option String := none) := do
    Command.liftTermElabM do
    let cmd ← constructCommands theorems
    let suggestion : Suggestion := {
      suggestion := cmd
      preInfo? := preMsg
      toCodeActionTitle? := .some (fun _ => "Replace with explicit proofs.")
    }
    addSuggestion stx suggestion (header := "")

/-- Check all invariants and print result of each check. -/
syntax "#check_invariants" : command
/-- Suggest theorems to check all invariants. -/
syntax "#check_invariants?" : command
/-- Check all invariants, print the result of each check, and suggest
theorems corresponding to the result of these checks. Theorems that
could not be proven have their proofs replaced with `sorry`. -/
syntax "#check_invariants!" : command
elab_rules : command
  | `(command| #check_invariants%$tk) => checkInvariants tk (behaviour := .checkTheorems)
  | `(command| #check_invariants?%$tk) => checkInvariants tk (behaviour := .printTheorems)
  | `(command| #check_invariants!%$tk) => checkInvariants tk (behaviour := .printAndCheckTheorems)

open Tactic in
/-- Try to solve the goal using one of the already proven invariant clauses,
    i.e. one of those marked with `@[invProof]` (via `#check_invariants`). -/
elab "already_proven" : tactic => withMainContext do
  let clauses := (← stsExt.get).establishedClauses.toArray
  let tacs ← clauses.mapM (fun cl => `(tactic|(try apply $(mkIdent cl) <;> assumption)))
  let attempt ← `(tactic| solve $[| $tacs:tactic]*)
  evalTactic attempt

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
         intros $(mkIdent `st) $(mkIdent `st')
        --  simp only [actSimp, invSimp, safeSimp]
         exact $proof)

/- This is a bit stupid, but we place these here so `type` doesn't interfere with
  the `Declaration` definition in `checkTheorem` above. -/
macro "type" id:ident : command => `(variable ($id : Type) [DecidableEq $id])
macro "instantiate" t:term : command => `(variable [$t])
macro "instantiate" nm:ident " : " t:term : command => `(variable [$nm : $t])

attribute [initSimp] RelationalTransitionSystem.init
attribute [invSimp] RelationalTransitionSystem.inv
attribute [invSimp] RelationalTransitionSystem.safe
attribute [safeSimp] RelationalTransitionSystem.safe
attribute [actSimp] RelationalTransitionSystem.next
