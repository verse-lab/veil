import Lean

import Veil.DSL.Internals.Attributes
import Veil.DSL.Internals.StateExtensions
import Veil.Util.DSL

open Lean Elab Command Term Meta Lean.Parser

def declareSpecName (n : Name) : CommandElabM Unit := do
  let ctx ← localSpecCtx.get
  let existingName := ctx.spec.name
  if existingName != Name.anonymous && existingName != n then
    throwError s!"Specification already named ({existingName}); cannot rename to {n}!"
  trace[veil.info] "declaring module {n}"
  localSpecCtx.modify (fun s => { s with spec.name := n })

def specName : CommandElabM Name := do
  let ctx ← localSpecCtx.get
  return ctx.spec.name

def declareSpecParameters (vd : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) : CommandElabM Unit := do
  localSpecCtx.modify (fun s => { s with spec.generic.parameters := vd })

def checkModuleExists (id : Name) [Monad m] [MonadEnv m] [MonadError m] : m Unit := do
  let modules := (<- globalSpecCtx.get)
  unless modules.contains id do
    throwError s!"Module {id} does not exist"

def checkCorrectInstantiation (id : Name) (ts : Array Term) : CoreM Unit := do
  checkModuleExists id
  let module := (<- globalSpecCtx.get)[id]!.spec
  let vd := module.generic.parameters
  let vs := ts
  if vd.size != vs.size then
    let sz := (List.range' 1 (max vd.size vs.size)) |>.toArray
    let pairing := Array.zip sz (Array.zipWithAll (fun p a => (p, a)) vd vs)
    let vdStr := "\n".intercalate (Array.toList $ ← pairing.mapM (fun (idx, param, arg) => do
      match param, arg with
      | .some p, .some a => return s!"{idx}. {← ppBracketedBinder p} ⟶ {← ppTerm a}"
      | .some p, .none => return s!"{idx}. {← ppBracketedBinder p} ⟶ no argument provided"
      | .none, .some a => return s!"{idx}. no argument expected ⟶ {← ppTerm a}"
      | .none, .none => return s!""
    ))
    throwError s!"Module {id} has {vd.size} parameters, but {vs.size} were provided:\n{vdStr}"
  -- TODO FIXME: check that the types match


def ModuleDependency.typeMapping [Monad m] [MonadError m] [MonadQuotation m] (dep : ModuleDependency) : m (Array (Term × Term)) := do
  let paramTerms ← bracketedBindersToTerms dep.parameters
  let pairs := paramTerms.zip dep.arguments
  let mapping ← dep.applyGetStateArguments pairs
  return mapping

def errorIfAssumptionsDefined : CoreM Unit := do
  let moduleName ← getCurrNamespace
  if !(← resolveGlobalName (moduleName ++ assumptionsName)).isEmpty then
    throwError "All assumptions must be defined before the after_init declaration!"

def errorIfStateNotDefined : CoreM Unit := do
  let stateName := (← localSpecCtx.get).stateBaseName
  if stateName.isNone then
     throwError "State has not been declared so far: run `#gen_state`"

def errorIfStateAlreadyDefined : CoreM Unit := do
  let stateName := (← localSpecCtx.get).stateBaseName
  if stateName.isSome then
    throwError "You have already run #gen_state for module {stateName.get!}: adding state components is no longer allowed!"

def errorIfSpecNotDefined : CoreM Unit := do
  let specName := (← localSpecCtx.get).spec.name
  let modules := (<- globalSpecCtx.get)
  unless modules.contains specName do
    throwError s!"The specification for module {specName} has not been defined: run `#gen_spec`"

def errorIfSpecAlreadyDefined : CoreM Unit := do
  let specName := (← localSpecCtx.get).spec.name
  let modules := (<- globalSpecCtx.get)
  if modules.contains specName then
    throwError s!"You have already run #gen_spec for module {specName}: adding actions or invariants is no longer allowed!"

def errorIfNoInitialStateDefined : CoreM Unit := do
  if (← resolveGlobalName initialStateName).isEmpty then
    throwError "You have not defined any initial state for this specification: write an `after_init` declaration"

def warnIfNoInvariantsDefined : CoreM Unit := do
  let invariants := (← localSpecCtx.get).spec.invariants
  if invariants.isEmpty then
    logWarning "you have not defined any invariants for this specification; did you forget?"

def warnIfNoActionsDefined : CoreM Unit := do
  let actions := (← localSpecCtx.get).spec.actions
  if actions.isEmpty then
    logWarning "you have not defined any actions for this specification; did you forget?"

def errorOrWarnWhenSpecIsNeeded : CoreM Unit := do
  errorIfStateNotDefined
  errorIfSpecNotDefined
  warnIfNoInvariantsDefined
  warnIfNoActionsDefined

/--Assembles all declared transitions into a `Next` transition relation. -/
def assembleNext : CommandElabM Unit := do
  let vd ← getSystemParameters
  let (nextAct, nextTr, nextLemma) ← Command.runTermElabM fun vs => do
    let sectionArgs ← getSectionArgumentsStx vs
    let spec := (← localSpecCtx.get).spec
    let (rd, st, st') := (mkIdent `st, mkIdent `rd, mkIdent `st')
    let labelTypeBinders ← spec.generic.applyGetStateArguments vd
    let labelTypeArgs ← bracketedBindersToTerms labelTypeBinders
    let labelT ← `(term|$labelIdent $labelTypeArgs*)
    let (Next, NextAct) := (mkIdent `Next, mkIdent `NextAct)
    let acts <- spec.actions.mapM fun s => do
      let name := mkIdent <| toExtName <| s.name
      `(@$name $sectionArgs*)
    let nextAct <- `(
      @[nextSimp, actSimp]
      noncomputable def $NextAct $[$vd]* : $labelT -> VeilM .external $genericReader $genericState Unit :=
        fun (l : $labelT) => l.casesOn $acts*
    )
    let nextTr <- `(
      @[nextSimp, actSimp] def $Next $[$vd]* :=
        fun ($rd : $genericReader) ($st $st' : $genericState) =>
          ∃ (l : $labelT),
          @$(mkIdent `NextAct) $sectionArgs* l |>.toTwoStateDerived $rd $st $st'
    )
    let nextLemma <- `(
      theorem $(mkIdent $ `next_refine) $[$vd]* (rd : $genericReader) (st st' : $genericState) l :
        let next := (@$NextAct $sectionArgs* l)
        ∀ chs : next.choices,
          (next.run chs).operational rd st st' (Except.ok ()) →
          @$Next $sectionArgs* rd st st' := by
        dsimp; intros chs op; exists l
        try cases l <;> simp only [$NextAct:ident, $Next:ident] at *
        all_goals apply VeilM.toTwoStateDerived_complete <;> solve_by_elim
    )
    pure (nextAct, nextTr, nextLemma)
  elabCommand nextAct
  trace[veil.debug] "[assembleActions] {nextTr}"
  elabCommand nextTr
  trace[veil.debug] "[assembleActions] {nextAct}"
  elabCommand nextLemma
  trace[veil.debug] "[assembleActions] {nextLemma}"
  trace[veil.info] "Next transition assembled"


  --   let trs ← (<- localSpecCtx.get).spec.actions.mapM (fun s => do
  --     let nm := mkIdent $ toTrName s.name
  --     `(@$nm $sectionArgs* $rd $st $st'))
  --   -- let _ ← (← localSpecCtx.get).spec.actions.mapM (fun t => do trace[veil.debug] s!"{t}")
  --   let next ← if trs.isEmpty then `(fun (_ : $genericReader) ($st $st' : $genericState) => $st = $st') else
  --             `(fun ($rd : $genericReader) ($st $st' : $genericState) => $(← repeatedOr trs))
  --   trace[veil.debug] "[assembleActions] {next}"
  --   `(@[actSimp] def $(mkIdent $ `Next) $[$vd]* := $next)
  -- trace[veil.info] "Next transition assembled"


def assembleLabelType (name : Name) : CommandElabM Unit := do
  let vd ← getActionParameters
  let generic := (← localSpecCtx.get).spec.generic
  let labelTypeName := labelIdent
  let labelTypeBinders ← generic.applyGetStateArguments vd
  let labelTypeArgs ← bracketedBindersToTerms labelTypeBinders
  let labelT ← `(term|$labelTypeName $labelTypeArgs*)

  let (labelType, alInstance, casesLemma) ← Command.runTermElabM fun _ => do
    let P := mkIdent `P
    let (ctors, altkinds) := Array.unzip $ ← (← localSpecCtx.get).spec.actions.mapM (fun s => do
      let .some decl := s.actionDecl | throwError "[assembleLabelType] {s} is not an action"
      let .some ctor := decl.ctor | throwError "DSL: missing label constructor for action {s.name}"
      let name ← `(term|$(quote decl.name))
      -- for use with `casesOn` to generated the functions of `ActionLabel`
      let alt ← match s.br with
        | some br => `(term|fun $(← toFunBinderArray br)* => $name)
        | none => `(term|$name)
      let kind ← `(term|($name, $(mkIdent decl.kind.toName)))
      let constructor := mkIdent (labelTypeName.getId ++ s.name)
      let ex ← match s.br with
        | some br => `(term| (∃ $br, $P ($constructor $(← explicitBindersIdents br)*)))
        | none => `(term| $P ($constructor))
      pure (ctor, alt, kind, ex))
    let (alts, kindsexs) := Array.unzip altkinds
    let (kinds, exs) := Array.unzip kindsexs
    trace[veil.info] "storing constructors for {name}"
    let labelType ←
      if ctors.isEmpty then
        `(inductive $labelTypeName $labelTypeBinders* where $[$ctors]*)
      else
        `(inductive $labelTypeName $labelTypeBinders* where $[$ctors]* deriving Nonempty)
    let idFn ← `(term|fun (l : $labelT) => l.casesOn $alts*)
    let kindMap ← `(Std.HashMap.ofList [$[$kinds],*])
    let alInstance ← `(command|
    noncomputable
    instance (priority := low) $(mkIdent $ Name.mkSimple s!"{name}_ActionLabel") : ActionLabel $labelT where
      id := $idFn
      kind := $kindMap
    )
    let casesLemma ← `(command|set_option linter.unusedSectionVars false in
      @[nextSimp] theorem $labelCasesIdent ($P : $labelT -> Prop) :
        (∃ l : $labelT, $P l) ↔
        $(← repeatedOr exs) :=
      by
        constructor
        { rintro ⟨l, r⟩; rcases l <;> aesop }
        { aesop }
    )
    trace[veil.debug] "labelType: {labelType}"
    trace[veil.debug] "alInstance: {alInstance}"
    trace[veil.debug] "casesLemma: {casesLemma}"
    pure (labelType, alInstance, casesLemma)
  elabCommand labelType
  elabCommand alInstance
  elabCommand casesLemma
  trace[veil.info] "Label {labelTypeName} type is defined"

def getIOSignatureStx [Monad m] [MonadEnv m] [MonadQuotation m] : m (TSyntax `term) := do
  let actions := (← localSpecCtx.get).spec.actions
  let internals := actions.filterMap (fun (s : ProcedureSpecification) => if s.isInternal then some (quote s.name) else none)
  let inputs := actions.filterMap (fun (s : ProcedureSpecification) => if s.isInput then some (quote s.name) else none)
  let outputs := actions.filterMap (fun (s : ProcedureSpecification) => if s.isOutput then some (quote s.name) else none)
  let stx ← `(term|{internal := Std.HashSet.ofList [$[$internals],*], input := Std.HashSet.ofList [$[$inputs],*], output := Std.HashSet.ofList [$[$outputs],*]})
  return stx

def getIOStepStx (stateTp : TSyntax `term) (labelT : TSyntax `term) (vs : Array Expr) : TermElabM (TSyntax `term) := do
  let spec := (← localSpecCtx.get).spec
  let (st, st') := (mkIdent `st, mkIdent `st')
  let actionArgs ← getSectionArgumentsStx vs
  let alts ← spec.actions.mapM (fun s => do
    let (params, args) ← match s.br with
      | some br => pure (← toFunBinderArray br, ← explicitBindersIdents br)
      | none => pure (#[], #[])
    let actFn := mkIdent $ toOriginalName s.name
    match s.br with
      | some _ => `(term|fun $params* => @$actFn $actionArgs* $args* $st $st')
      | none => `(term|$actFn $st $st')
  )
  let stepStx ← `(term|fun ($st : $stateTp) (a : $labelT) ($st' : $stateTp) => a.casesOn $alts*)
  trace[veil.debug] "stepStx: {stepStx}"
  return stepStx

/-- Assembles all declared invariants (including safety properties) into
a single `Invariant` predicate -/
def assembleInvariant : CommandElabM Unit := do
  let vd ← getAssertionParameters
  elabCommand $ <- Command.runTermElabM fun vs => do
    let allClauses := (<- localSpecCtx.get).spec.invariants
    let exprs := allClauses.toList.map (fun p => p.expr)
    let _ ← allClauses.mapM (fun t => do trace[veil.debug] s!"{t}")
    let invs ← if allClauses.isEmpty then `(fun _ _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "invariants"
    `(@[invSimp, invSimpTopLevel] def $(mkIdent `Invariant) $[$vd]* : $genericReader -> $genericState -> Prop := $invs)
  trace[veil.info] "Invariant assembled"

/-- Assembles all declared safety properties into a single `Safety`
predicate -/
def assembleSafeties : CommandElabM Unit := do
  let vd ← getAssertionParameters
  elabCommand $ <- Command.runTermElabM fun vs => do
    let exprs := (<- localSpecCtx.get).spec.invariants.toList.filterMap (fun p => if p.kind == .safety then p.expr else none)
    let safeties ← if exprs.isEmpty then `(fun _ _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "invariants"
    `(@[invSimp, invSimpTopLevel] def $(mkIdent `Safety) $[$vd]* : $genericReader -> $genericState -> Prop := $safeties)
  trace[veil.info] "Safety assembled"

/-- Assembles all declared `assumption`s into a single `Assumptions`
predicate -/
def assembleAssumptions : CommandElabM Unit := do
  let vd ← getAssumptionParameters
  elabCommand $ <- Command.runTermElabM fun vs => do
    let vs ← getAssumptionArguments vs
    let exprs := (<- localSpecCtx.get).spec.assumptions.toList.map (fun p => p.expr)
    let assumptions ← if exprs.isEmpty then `(fun _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "assumptions"
    let stx ← `(@[invSimp, invSimpTopLevel] def $assumptionsIdent $[$vd]* : $genericReader -> Prop := $assumptions)
    trace[veil.debug] "[assembleAssumptions]\n{stx}"
    pure stx
  trace[veil.info] "Assumptions assembled"
