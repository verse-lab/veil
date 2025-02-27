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
  let module := (<- globalSpecCtx.get)[id]!
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
  let paramIdents : Array Ident ← dep.parameters.mapM bracketedBinderIdent
  let paramTerms ← paramIdents.mapM (fun id => `(term|$id))
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
