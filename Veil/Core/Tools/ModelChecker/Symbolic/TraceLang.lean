import Lean
import Lean.Parser
import Veil.Util.Meta
import Veil.Frontend.DSL.Module.Util.Assertions
import Veil.Frontend.DSL.Module.Names
import Veil.Frontend.DSL.Util
import Veil.Core.Tools.ModelChecker.TransitionSystem

/-!
  # Symbolic Trace Language

  This file defines the syntax and elaboration for symbolic model checking
  queries like `sat trace` and `unsat trace`.

  ## Example usage:

  ```lean4
  sat trace [can_elect_leader] {
    any 3 actions
    send
    assert (∃ l, leader l)
  } by { bmc_sat }

  unsat trace {
    any 6 actions
    assert ¬ (leader L → le N L)
  } by { bmc }
  ```
-/

declare_syntax_cat expected_smt_result
syntax (name := expected_sat) "sat" : expected_smt_result
syntax (name := expected_unsat) "unsat" : expected_smt_result

declare_syntax_cat trace_line
syntax (name := any_action_star) "*" : trace_line
syntax (name := any_action) atomic("any" "action") : trace_line
syntax traceAnyAction := any_action_star <|> any_action

syntax (name := traceAnyNActions) "any " num " actions": trace_line

syntax (name := traceActionName) ident : trace_line
syntax traceAction := (traceActionName <|> traceAnyAction <|> traceAnyNActions)

syntax (name := traceAssertion) "assert " term:max : trace_line

syntax traceLine := (traceAction <|> traceAssertion)
syntax traceSpec := (traceLine colEq)*

syntax expected_smt_result "trace" ("[" ident "]")? "{"
  traceSpec
"}" term : command


namespace Veil
open Lean Elab Command Term Meta

/-- A single line in a trace specification -/
inductive TraceSpecLine
  | action : Name → TraceSpecLine
  | anyAction : TraceSpecLine
  | anyNActions : Nat → TraceSpecLine
  | assertion : Term → TraceSpecLine
deriving Inhabited, Repr

instance : ToString TraceSpecLine := ⟨fun
  | TraceSpecLine.action n => s!"action {n}"
  | TraceSpecLine.anyAction => "any action"
  | TraceSpecLine.anyNActions n => s!"any {n} actions"
  | TraceSpecLine.assertion t => s!"assertion {t}"⟩

abbrev TraceSpec := List TraceSpecLine

def parseTraceSpec [Monad m] [MonadExceptOf Exception m] [MonadError m] (stx : Syntax) : m TraceSpec := do
  match stx with
  | `(traceSpec| $[$ts]* ) => do
    let mut ts ← ts.mapM fun t => match t with
      | `(traceLine| any action) | `(traceLine| * ) => return TraceSpecLine.anyAction
      | `(traceLine| any $n:num actions) => do (
        if n.getNat < 2 then
          throwErrorAt stx "any {n} actions: n must be >= 2"
        else
          return TraceSpecLine.anyNActions n.getNat
      )
      | `(traceLine| assert $term) => return TraceSpecLine.assertion term
      | `(traceLine| $id:ident) => return TraceSpecLine.action id.raw.getId
      | _ => throwErrorAt stx "unsupported syntax"
    return ts.toList
  | _ => throwUnsupportedSyntax

open Lean.Parser.Term in

/-- Convert a bracketed binder to an explicit binder for use in existential quantification -/
private def toExplicitBindersForExists (stx : TSyntax `Lean.Parser.Term.bracketedBinder) : TermElabM (TSyntax `Lean.bracketedExplicitBinders) := do
  match stx with
  | `(bracketedBinder| ($id:ident : $tp)) => `(bracketedExplicitBinders| ($(identToBinderIdent id) : $tp))
  | `(bracketedBinder| {$id:ident : $tp}) => `(bracketedExplicitBinders| ($(identToBinderIdent id) : $tp))
  | `(bracketedBinder| [$id:ident : $tp]) => `(bracketedExplicitBinders| ($(identToBinderIdent id) : $tp))
  | `(bracketedBinder| [$tp]) =>
    -- Anonymous typeclass instance - create a fresh name
    let freshId := mkIdent (← mkFreshUserName `inst)
    `(bracketedExplicitBinders| ($(identToBinderIdent freshId) : $tp))
  | _ => throwError s!"toExplicitBindersForExists: unexpected syntax: {stx}"

def elabTraceSpec (r : TSyntax `expected_smt_result) (name : Option (TSyntax `ident)) (spec : TSyntax `traceSpec) (pf : TSyntax `term)
  : CommandElabM Unit := do
  -- Get the current module
  let mod ← getCurrentModule (errMsg := "trace commands can only be used inside a Veil module after #gen_spec")

  -- Check that the spec is finalized
  if !mod.isSpecFinalized then
    throwError "trace commands can only be used after #gen_spec"

  let th ← Command.runTermElabM fun _ => do
    let spec ← parseTraceSpec spec
    let numActions := spec.foldl (fun n s =>
      match s with
      | TraceSpecLine.assertion _ => n
      | TraceSpecLine.anyNActions k => n + k
      | _ => n + 1) 0
    let numStates := numActions + 1
    let stateNames := List.toArray $ (List.range numStates).map fun i => mkIdent (Name.mkSimple s!"st{i}")
    let theoryId := mkIdent `th

    -- Get the sort identifiers
    let sorts ← mod.sortIdents

    -- Construct the types as used by the RTS (mirroring assembleRelationalTransitionSystem)
    let theoryT ← mod.theoryStx  -- Theory node
    let stateT ← `(term| $(mkIdent stateName) ($fieldAbstractDispatcher $sorts*))  -- State (FieldAbstractType node)

    /- Track which state assertions refer to. -/
    let mut currStateId := 0
    /- Which assertions, including state-transitions, does the spec contain. -/
    let mut assertions : Array (TSyntax `term) := #[]
    /- Collect all action parameters for existential quantification -/
    let mut actionParamBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
    let mut actionParamExplicitBinders : Array (TSyntax `Lean.bracketedExplicitBinders) := #[]
    /- Counter for unique action parameter names -/
    let mut trIdx := 1

    -- Get the RTS and add initial assumption + init predicate
    let rtsExpr ← `(term| @$assembledRTS $sorts*)
    assertions := assertions.push (← `(term|
      ($rtsExpr).$(mkIdent `assumptions) $theoryId ∧
      (($rtsExpr).$(mkIdent `init) $theoryId $(stateNames[0]!))))

    for s in spec do
      let currState := stateNames[currStateId]!
      match s with
      | TraceSpecLine.action n => do
        let nextState := stateNames[currStateId + 1]!
        -- Look up the action in the module
        let actionProc := mod.actions.find? (fun a => a.name == n)
        let specificParams ← match actionProc with
          | some proc => do
            let (_, specificParams) ← mod.declarationAllParams proc.name proc.declarationKind
            pure specificParams
          | none => throwError s!"action '{n}' not found in module. Available actions: {mod.actions.map (·.name)}"

        -- Create unique parameter names and collect them for existential quantification
        let mut specificArgIdents : Array Ident := #[]
        let mut argIdx := 0
        for p in specificParams do
          let uniqueName := Name.mkSimple s!"_tr{trIdx}_arg{argIdx}_{p.name}"
          let uniqueId := mkIdent uniqueName
          specificArgIdents := specificArgIdents.push uniqueId
          let ty := p.type
          actionParamBinders := actionParamBinders.push (← `(bracketedBinder| ($uniqueId : $ty)))
          actionParamExplicitBinders := actionParamExplicitBinders.push
            (← `(bracketedExplicitBinders| ($(identToBinderIdent uniqueId) : $ty)))
          argIdx := argIdx + 1

        -- Use rts.tr with Label constructor instead of calling the transition function directly
        -- This avoids issues with generic type parameters
        let labelConstructor := mkIdent $ labelTypeName ++ n
        let labelExpr ← `(term| ($labelConstructor $specificArgIdents*))
        let t ← `(term|(($rtsExpr).$(mkIdent `tr) $theoryId $currState $labelExpr $nextState))
        assertions := assertions.push t
        currStateId := currStateId + 1
        trIdx := trIdx + 1
      | TraceSpecLine.anyAction => do
        let nextState := stateNames[currStateId + 1]!
        let t ← `(term|(($rtsExpr).$(mkIdent `next) $theoryId $currState $nextState))
        assertions := assertions.push t
        currStateId := currStateId + 1
      | TraceSpecLine.anyNActions k => do
        for _ in [0:k] do
          let currState := stateNames[currStateId]!
          let nextState := stateNames[currStateId + 1]!
          let t ← `(term|(($rtsExpr).$(mkIdent `next) $theoryId $currState $nextState))
          assertions := assertions.push t
          currStateId := currStateId + 1
      | TraceSpecLine.assertion t => do
        -- Elaborate assertions using the wrapper with concrete types
        let fieldRepInstance ← `(term| $instAbstractFieldRepresentation $sorts*)
        let stateSortTerm ← `(term| $fieldAbstractDispatcher $sorts*)
        let wrappedTerm ← withTheoryAndStateFn mod (← `(uqc% (($t:term):Prop))) theoryT stateT fieldRepInstance stateSortTerm
        let t ← `(term|($wrappedTerm $theoryId $currState))
        assertions := assertions.push t

    let name : Name ← match name with
    | some n => pure n.getId
    | none => mkFreshUserName `trace

    let th_id := mkIdent name
    let conjunction ← repeatedAnd assertions

    -- Get the sort parameters as binders
    let sortBinders ← mod.sortBinders
    let sortExplicitBinders ← sortBinders.mapM toExplicitBindersForExists

    -- Get Inhabited instances for every sort (required by RTS)
    let inhabitedBinders ← mod.assumeForEverySort ``Inhabited
    let inhabitedExplicitBinders ← inhabitedBinders.mapM toExplicitBindersForExists

    -- Get user-defined typeclass parameters
    let userDefinedParams : Array Parameter := mod.parameters.filter fun p =>
      match p.kind with
      | .moduleTypeclass .userDefined => true
      | _ => false
    let userDefinedBinders ← userDefinedParams.mapM (·.binder)
    let userDefinedExplicitBinders ← userDefinedBinders.mapM toExplicitBindersForExists

    let binderNames : Array (TSyntax ``Lean.binderIdent) := stateNames.map identToBinderIdent

    -- Combine all binders for the quantification
    let allBracketedBinders := sortBinders ++ inhabitedBinders ++ userDefinedBinders
    let allExplicitBinders := sortExplicitBinders ++ inhabitedExplicitBinders ++ userDefinedExplicitBinders

    let assertion ← match r with
    | `(expected_smt_result| unsat) =>
      `(∀ $[$allBracketedBinders]* $[$actionParamBinders]* ($theoryId:ident : $theoryT) ($[$stateNames]* : $stateT), ¬ $conjunction)
    | `(expected_smt_result| sat) =>
      `(∃ $[$allExplicitBinders]* $[$actionParamExplicitBinders]* ($theoryId:ident : $theoryT) ($[$binderNames]* : $stateT), $conjunction)
    | _ => dbg_trace "expected result is neither sat nor unsat!" ; unreachable!
    -- Wrap in `open Classical in` for classical reasoning
    `(open $(mkIdent `Classical):ident in theorem $th_id : $assertion := by exact $pf)
  trace[veil.debug] "{th}"
  elabVeilCommand th

elab_rules : command
  | `(command| $r:expected_smt_result trace [ $name ] { $spec:traceSpec } $pf) => elabTraceSpec r name spec pf
  | `(command| $r:expected_smt_result trace { $spec:traceSpec } $pf) => elabTraceSpec r none spec pf

end Veil
