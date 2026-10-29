module

public meta import Veil.Frontend.DSL.Module.Util.Basic

public meta section

open Lean Meta Elab Term Command

namespace Veil

/-- Reintroduce source dictionaries as lexical instances in source declaration
order. Lean elaborates and closes these lets, so arbitrary pinned dictionary
expressions are supported without leaking temporary free variables. -/
def Module.wrapSourceInstanceArguments (mod : Module) (body : Term) : TermElabM Term :=
  mod.sourceInstanceArguments.foldrM (fun actual body =>
    `(term| letI := $actual:term; $body:term)) body

/-- Keep every ordinary/class-parameter slot bound to its actual root variable at an
internal call. Search may be restricted while elaborating arguments, and two
occurrences may intentionally carry different instances of the same class. -/
def Module.explicitClassCall [Monad m] [MonadQuotation m]
    (mod : Module) (name : Name) (args : Array Term) : m Term := do
  let classes := mod.parameters.filter fun parameter =>
    parameter.kind == .moduleTypeclass .userDefined ||
      parameter.kind == .moduleTypeclass .sortAssumption || parameter.kind == .userParameter
  let named ← classes.mapM fun parameter => do
    let argument ← parameter.arg
    `(Parser.Term.namedArgument| ($(mkIdent parameter.name) := $argument:term))
  return ⟨mkNode ``Parser.Term.app
    #[mkIdent name, mkNullNode (named.map (·.raw) ++ args.map (·.raw))]⟩

/-- Record only instance declarations introduced by a compiler-owned phase.
The caller brackets state/theory generation, never arbitrary user commands. -/
def generatedInstancesSince (before after : Environment) : Array Name :=
  let previous := instanceExtension.getState before
  (instanceExtension.getState after).instanceNames.foldl
    (fun names name _ => if previous.instanceNames.contains name then names else names.push name) #[]

private def Module.withSourceGlobalInstances (mod : Module) (k : TermElabM α) : TermElabM α := do
  let some scope := mod.sourceCommandScope? | return ← k
  let savedInstances := instanceExtension.getState (← getEnv)
  let savedDefaults := defaultInstanceExtension.getState (← getEnv)
  let sourceInstances := mod.generatedInstanceNames.foldl (fun instances name =>
    match savedInstances.instanceNames.find? name with
    | some entry => addInstanceEntry instances entry
    | none => instances) scope.instances
  let sourceDefaults := savedDefaults.defaultInstances.foldl (fun defaults className entries =>
    entries.foldl (fun defaults (name, priority) =>
      if mod.generatedInstanceNames.contains name then
        addDefaultInstanceEntry defaults { className, instanceName := name, priority }
      else defaults) defaults) scope.defaultInstances
  -- Global instance registries are absent from the synthesis cache key.
  -- Isolate the cache as well as the search tables, then restore only tables:
  -- ordinary declarations produced while elaborating k must survive.
  withOptions (fun _ => scope.options.setBool `Elab.async false) <| withFreshCache do
    modifyEnv fun env => defaultInstanceExtension.modifyState
      (instanceExtension.modifyState env fun _ => sourceInstances) fun _ => sourceDefaults
    try k
    finally
      modifyEnv fun env => defaultInstanceExtension.modifyState
        (instanceExtension.modifyState env fun _ => savedInstances) fun _ => savedDefaults

/-- Elaborate source code with its own explicitly declared class parameters.
Caller-only class parameters remain ordinary variables in the declaration's
signature, but cannot silently change instance search inside an occurrence.
Generated sort, state, and theory instances remain available. -/
def Module.withSourceInstances (mod : Module) (k : TermElabM α) : TermElabM α := do
  let some _ := mod.sourceInstanceNames? | return ← mod.withSourceGlobalInstances k
  let excluded := mod.parameters.filterMap fun parameter =>
    if parameter.kind == .moduleTypeclass .userDefined || parameter.kind == .userParameter then
      some parameter.name
    else none
  let lctx ← getLCtx
  let instances := (← getLocalInstances).filter fun localInstance =>
    !(lctx.find? localInstance.fvar.fvarId!).any (excluded.contains ·.userName)
  withLCtx lctx instances (mod.withSourceGlobalInstances k)

/-- Field openings introduce local instances too. Only fields that were
class-typed in this source occurrence may participate; every field remains
available for explicit reads and for the generated state plumbing. -/
def Module.withSourceFieldInstances [Monad m] [MonadControlT MetaM m]
    (mod : Module) (k : m α) : m α :=
  mapMetaM (fun inner => do
    if mod.sourceInstanceFieldNames?.isNone && mod.instances.isEmpty then return ← inner
    let excluded := mod.signature.filterMap fun field =>
      let allowed := match mod.sourceInstanceFieldNames? with
        | some allowed => allowed.contains field.name
        | none => !mod.instanceNames.any (·.2 == field.name)
      if allowed then none else some field.name
    let lctx ← getLCtx
    let instances := (← getLocalInstances).filter fun localInstance =>
      !(lctx.find? localInstance.fvar.fvarId!).any fun decl =>
        excluded.any fun name =>
          decl.userName == name || decl.userName == name.appendAfter "_conc" ||
          decl.userName == name.appendAfter "'" ||
          decl.userName == mkVeilImplementationDetailName name
    withLCtx lctx instances inner) k

/-- This marker is placed inside generated field binders, after their local
instances exist. The restriction is lexical and survives postponed elaboration. -/
syntax (name := sourceFieldInstances) "veil_source_fields% " term : term

@[term_elab sourceFieldInstances]
def elabSourceFieldInstances : TermElab := fun stx expectedType => do
  let `(veil_source_fields% $body) := stx | throwUnsupportedSyntax
  (← getCurrentModule).withSourceFieldInstances (elabTerm body expectedType)

end Veil
