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
  localSpecCtx.modify (fun s => { s with spec.parameters := vd })

def checkModuleExists (id : Name) [Monad m] [MonadEnv m] [MonadError m] : m Unit := do
  let modules := (<- globalSpecCtx.get)
  unless modules.contains id do
    throwError s!"Module {id} does not exist"

def checkCorrectInstantiation (id : Name) (ts : Array Term) [Monad m] [MonadEnv m] [MonadError m] : m Unit := do
  checkModuleExists id
  let module := (<- globalSpecCtx.get)[id]!.spec
  let vd := module.parameters
  let vs := ts
  if vd.size != vs.size then
    let vdStr := "\n".intercalate (Array.toList $ vd.map (fun x => s!"{x}"))
    throwError s!"Module {id} has {vd.size} parameters, but {vs.size} were provided\nrequired parameters: {vdStr}"
  -- TODO FIXME: check that the types match

/-- Return only those arguments that are used in the state type. -/
def ModuleDependency.stateArguments [Monad m] [MonadError m] (dep : ModuleDependency) : m (Array Term) := do
  getStateArguments dep.parameters dep.arguments

def ModuleDependency.typeMapping [Monad m] [MonadError m] [MonadQuotation m] (dep : ModuleDependency) : m (Array (Term × Term)) := do
  let paramTerms ← bracketedBindersToTerms dep.parameters
  let pairs := paramTerms.zip dep.arguments
  let mapping ← getStateArguments dep.parameters pairs
  return mapping


def errorIfStateNotDefined : CoreM Unit := do
  let stateName := (← localSpecCtx.get).stateBaseName
  if stateName.isNone then
     throwError "State has not been declared so far: run `#gen_state`"

def warnIfNoInvariantsDefined : CoreM Unit := do
  let invariants := (← localSpecCtx.get).spec.invariants
  if invariants.isEmpty then
    logWarning "you have not defined any invariants for this specification; did you forget?"

def warnIfNoActionsDefined : CoreM Unit := do
  let actions := (← localSpecCtx.get).spec.actions
  if actions.isEmpty then
    logWarning "you have not defined any actions for this specification; did you forget?"

/--Assembles all declared transitions into a `Next` transition relation. -/
def assembleNext : CommandElabM Unit := do
  let vd ← getActionParameters
  elabCommand $ ← Command.runTermElabM fun vs => do
    let stateTp ← getStateTpStx
    let sectionArgs ← getSectionArgumentsStx vs
    let (st, st') := (mkIdent `st, mkIdent `st')
    let trs ← (<- localSpecCtx.get).spec.actions.mapM (fun s => do
      let nm := mkIdent $ toTrName s.name
      `(@$nm $sectionArgs* $st $st'))
    -- let _ ← (← localSpecCtx.get).spec.actions.mapM (fun t => do trace[veil.debug] s!"{t}")
    let next ← if trs.isEmpty then `(fun ($st $st' : $stateTp) => $st = $st') else
              `(fun ($st $st' : $stateTp) => $(← repeatedOr trs))
    trace[veil.debug] "[assembleActions] {next}"
    `(@[actSimp] def $(mkIdent $ `Next) $[$vd]* := $next)
  trace[veil.info] "Next transition assembled"


def assembleLabelType (name : Name) : CommandElabM Unit := do
  let vd ← getActionParameters
  let labelTypeName := mkIdent `Label
  let labelTypeBinders := getStateParametersBinders vd
  let labelTypeArgs ← getStateArgumentsStx' vd
  let labelT ← `(term|$labelTypeName $labelTypeArgs*)

  let (labelType, alInstance) ← Command.runTermElabM fun _ => do
    let (ctors, altkinds) := Array.unzip $ ← (← localSpecCtx.get).spec.actions.mapM (fun s => do
      let .some decl := s.actionDecl | throwError "[assembleLabelType] {s} is not an action"
      let .some ctor := decl.ctor | throwError "DSL: missing label constructor for action {s.name}"
      let name ← `(term|$(quote decl.name))
      -- for use with `casesOn` to generated the functions of `ActionLabel`
      let alt ← match s.br with
        | some br => `(term|fun $(← toFunBinderArray br)* => $name)
        | none => `(term|$name)
      let kind ← `(term|($name, $(mkIdent decl.kind.toName)))
      pure (ctor, alt, kind))
    let (alts, kinds) := Array.unzip altkinds
    trace[veil.info] "storing constructors for {name}"
    let labelType ← `(inductive $labelTypeName $labelTypeBinders* where $[$ctors]*)
    let idFn ← `(term|fun (l : $labelT) => l.casesOn $alts*)
    let kindMap ← `(Std.HashMap.ofList [$[$kinds],*])
    let alInstance ← `(command|instance (priority := low) $(mkIdent $ Name.mkSimple s!"{name}_ActionLabel") : ActionLabel $labelT where
      id := $idFn
      kind := $kindMap
    )
    trace[veil.debug] "labelType: {labelType}"
    trace[veil.debug] "alInstance: {alInstance}"
    pure (labelType, alInstance)
  elabCommand labelType
  elabCommand alInstance
  trace[veil.info] "Label {labelTypeName} type is defined"

def getIOSignatureStx [Monad m] [MonadEnv m] [MonadQuotation m] : m (TSyntax `term) := do
  let actions := (← localSpecCtx.get).spec.actions
  let internals := actions.filterMap (fun (s : ProcedureSpecification) => if s.isInternal then some (quote s.name) else none)
  let inputs := actions.filterMap (fun (s : ProcedureSpecification) => if s.isInput then some (quote s.name) else none)
  let outputs := actions.filterMap (fun (s : ProcedureSpecification) => if s.isOutput then some (quote s.name) else none)
  let stx ← `(term|{internal := Std.HashSet.ofList [$[$internals],*], input := Std.HashSet.ofList [$[$inputs],*], output := Std.HashSet.ofList [$[$outputs],*]})
  return stx

def getIOStepStx [Monad m] [MonadEnv m] [MonadError m] [MonadQuotation m] (stateTp : TSyntax `term) (labelT : TSyntax `term) : m (TSyntax `term) := do
  let spec := (← localSpecCtx.get).spec
  let (st, st') := (mkIdent `st, mkIdent `st')
  let alts ← spec.actions.mapM (fun s => do
    let (params, args) ← match s.br with
      | some br => pure (← toFunBinderArray br, ← explicitBindersIdents br)
      | none => pure (#[], #[])
    let actFn := mkIdent $ toFnName s.name
    match s.br with
      | some _ => `(term|fun $params* => $actFn $args* $st $st')
      | none => `(term|$actFn $st $st')
  )
  let stepStx ← `(term|fun ($st : $stateTp) (a : $labelT) ($st' : $stateTp) => a.casesOn $alts*)
  return stepStx

/-- Assembles all declared invariants (including safety properties) into
a single `Invariant` predicate -/
def assembleInvariant : CommandElabM Unit := do
  let vd ← getAssertionParameters
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- getStateTpStx
    let allClauses := (<- localSpecCtx.get).spec.invariants
    let exprs := allClauses.toList.map (fun p => p.expr)
    let _ ← allClauses.mapM (fun t => do trace[veil.debug] s!"{t}")
    let invs ← if allClauses.isEmpty then `(fun _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "invariants"
    `(@[invSimp, invSimpTopLevel] def $(mkIdent `Invariant) $[$vd]* : $stateTp -> Prop := $invs)
  trace[veil.info] "Invariant assembled"

/-- Assembles all declared safety properties into a single `Safety`
predicate -/
def assembleSafeties : CommandElabM Unit := do
  let vd ← getAssertionParameters
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- getStateTpStx
    let exprs := (<- localSpecCtx.get).spec.invariants.toList.filterMap (fun p => if p.kind == .safety then p.expr else none)
    let safeties ← if exprs.isEmpty then `(fun _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "invariants"
    `(@[invSimp, invSimpTopLevel] def $(mkIdent `Safety) $[$vd]* : $stateTp -> Prop := $safeties)
  trace[veil.info] "Safety assembled"

/-- Assembles all declared `assumption`s into a single `Assumptions`
predicate -/
def assembleAssumptions : CommandElabM Unit := do
  let vd ← getAssertionParameters
  elabCommand $ <- Command.runTermElabM fun vs => do
    let stateTp <- getStateTpStx
    let exprs := (<- localSpecCtx.get).spec.assumptions.toList.map (fun p => p.expr)
    let assumptions ← if exprs.isEmpty then `(fun _ => True) else PrettyPrinter.delab $ ← combineLemmas ``And exprs vs "assumptions"
    `(@[invSimp, invSimpTopLevel] def $(mkIdent `Assumptions) $[$vd]* : $stateTp -> Prop := $assumptions)
  trace[veil.info] "Assumptions assembled"
