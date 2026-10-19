module

public meta import Veil.Frontend.DSL.Module.Util.Basic
meta import Veil.Frontend.Std

public meta section

open Lean Meta Elab Term

namespace Veil

/-- The parameters of the module that an `Instantiation` sets or constrains, as the binders of a
`∀`-template `∀ binders, Unit`, each with its role and the syntax declaring it. Instantiating the
template with the concrete values yields the obligations of the `instantiate` constraints, with
the dependencies between them already in place. -/
def Module.instantiationTemplate (mod : Module) : TermElabM (Expr × Array (InstantiationBinder × Syntax)) := do
  -- NOTE: `elabBinders` (used elsewhere in Veil) is deliberately avoided here. It introduces
  -- fvars and registers the `[inst : C ...]` binders as local instances, so the obligations
  -- would have to be built by `replaceFVars` and created under the outer local context, or
  -- the abstract binders could take part in solving the concrete obligations (an `outParam`-only
  -- class `C ?x` unifies with the local instance `C node`). A closed `∀` type adds nothing to
  -- the context, and `forallMetaTelescopeReducing` directly gives mvars in the current context.
  let params := mod.parameters.filter fun p => match p.kind with
    | .sort _ | .userParameter
    | .moduleTypeclass .sortAssumption | .moduleTypeclass .userDefined => true
    | _ => false
  let template ← elabType (← `(∀ $(← params.mapM (·.binder))*, $(mkIdent ``Unit)))
  let binders := params.map fun p =>
    let binder := match p.kind with
      | .sort _ | .userParameter => .field p.name
      | .moduleTypeclass .userDefined => .constraint
      | _ => .sortAssumption
    (binder, p.userSyntax)
  return (template, binders)

/-- The default instances of Veil's containers, which fill the holes of an instantiation (see
`elabInstantiationAgainst`), e.g. `procSet := _` with `OrdList _` for a `TSet` constraint. -/
def containerDefaultInstances : Array DefaultInstanceEntry := #[
  { className := ``TSet, instanceName := ``instTSetOrdList, priority := eval_prio high },
  { className := ``TSet, instanceName := ``instTSetExtTreeSet, priority := eval_prio default },
  { className := ``TSet, instanceName := ``instTSetOrdArray, priority := eval_prio low },
  { className := ``TMultiset, instanceName := ``instTMultiSetWithExtTreeMap, priority := eval_prio default },
  { className := ``TMap, instanceName := ``instTMapExtTreeMap, priority := eval_prio default }]

/-- Elaborate a concrete instantiation `stx` of type `instType`, filling its type holes (e.g.
`procSet := OrdList _`, or a bare `procSet := _`) from the `instantiate` constraints of the
module, given by `template` (see `Module.instantiationTemplate`).

Each `instantiate` declaration becomes an ordinary typeclass obligation on the concrete
instantiation. Lean postpones an obligation whose type still has holes and, once nothing
else makes progress, tries the class's default instances: unifying such an instance
head with the obligation assigns the holes. Veil's container defaults are enabled only
while solving these concrete constraints; other classes opt in with `@[default_instance]`.
Without a default, the hole stays stuck and is reported at the syntax given with the constraint,
or at `stx` if that has no position.
Fully specified instantiations take the ordinary elaboration path and are not checked here;
`template` is only run for instantiations with holes. -/
def elabInstantiationAgainst (instType : Expr) (stx : Term)
    (template : TermElabM (Expr × Array (InstantiationBinder × Syntax))) : TermElabM Expr := do
  let inst ← elabTermEnsuringType stx instType
  let hasTypeHole ← (← getMVars inst).anyM fun hole => do
    return (← whnf (← inferType (mkMVar hole))).isSort
  unless hasTypeHole do
    -- In this case, there is nothing to infer, but the term may still carry non-type mvars:
    -- for example, `NodeSet := Std.ExtTreeSet X`
    -- elaborates to `@ExtTreeSet X ?cmp`, where `?cmp` is the `autoParam` comparator, a pending
    -- tactic goal (`by exact compare`) that Lean normally runs at the end of the enclosing term,
    -- *after trying default instances*.
    -- Settle such problems here instead of at the end. If we left them pending,
    -- `?cmp` would end up inside the model
    -- checker's obligation `TSet X (ExtTreeSet X ?cmp)`; that problem is stuck.
    -- If a matching default instance is enabled, Lean's final loop tries it before
    -- tactic blocks, under `withAssignableSyntheticOpaque`, so e.g. `instTSetExtTreeSet`
    -- could assign `?cmp := compare` itself and the tactic would then fail with "no goals".
    -- Running the tactic now makes `inst` fully concrete before any obligation can mention it.
    synthesizeSyntheticMVarsNoPostponing
    if ← MonadLog.hasErrors then throwAbortTerm
    return ← instantiateMVars inst
  let (template, binders) ← template
  let (vars, _, _) ← forallMetaTelescopeReducing template (kind := .synthetic)
  let mut obligations : Array (Syntax × MVarId) := #[]
  for (binder, ref) in binders, var in vars do
    match binder with
    | .field name =>
      -- Reduce the projection: an unreduced `inst.node` mentions the whole literal, holes
      -- included, so unifying a hole with it would fail the occurs check.
      var.mvarId!.assign (← whnf (← mkProjection inst name))
    | .constraint => obligations := obligations.push (ref, var.mvarId!)
    | .sortAssumption => pure ()
  -- The auto-generated sort assumptions are only needed where a user constraint mentions them.
  for (binder, ref) in binders, var in vars do
    if binder matches .sortAssumption then
      if ← obligations.anyM fun (_, id) => do return (← getMVars (← id.getType)).contains var.mvarId! then
        obligations := obligations.push (ref, var.mvarId!)
  -- Hand the obligations to Lean's standard synthesis loop as typeclass problems; an
  -- obligation that cannot be solved is reported at the syntax of its constraint.
  -- (The previous handling should ensure that `id` is a typeclass goal.)
  for (ref, id) in obligations do
    registerSyntheticMVar (if ref.getPos?.isSome then ref else stx.raw) id (.typeClass none)
  -- `autoParams` (e.g. `ExtTreeSet`'s `cmp`) are pending tactic mvars. Unifying with an instance
  -- head may assign them before their tactic runs, which Lean then reports as an error. Detach
  -- them, let unification decide, and run the tactic afterwards only if still open.
  let mut detached : Array (MVarId × SyntheticMVarDecl) := #[]
  for hole in ← getMVars inst do
    if let some decl ← getSyntheticMVarDecl? hole then
      if decl.kind matches .tactic .. then
        detached := detached.push (hole, decl)
        modify fun s => { s with
          pendingMVars := s.pendingMVars.erase hole
          syntheticMVars := s.syntheticMVars.erase hole }
        -- A tactic goal is `syntheticOpaque`, which `isDefEq` never assigns. With no tactic
        -- in charge any more, make it a plain hole, as if the user had written `_`.
        hole.setKind .natural
  -- This is where the holes get filled. Ordinary synthesis runs at a new mctx depth, so it
  -- cannot assign a hole in a non-outParam position: `TSet (Fin 4) (OrdList ?α)` is stuck.
  -- Once nothing else makes progress, the loop unifies each stuck problem with the heads of
  -- the class's `@[default_instance]`s (`TSet ?β (OrdList ?β)` gives `?α := Fin 4`), keeping
  -- the first one whose premises are then fully solvable. The remaining problems, e.g. the
  -- `Ord ?α` pending since `OrdList _` was elaborated above, follow in later rounds of Lean's
  -- own loop inside this call (`elabInstantiationAgainst` itself does not iterate).
  --
  -- Container defaults must not infer concrete types for the implicit parameters of
  -- ordinary ghost calls. Change only the extension's state, so these temporary
  -- defaults are not exported and elaboration's other environment changes survive.
  let savedDefaults := defaultInstanceExtension.getState (← getEnv)
  try
    modifyEnv fun env => defaultInstanceExtension.setState env
      (containerDefaultInstances.foldl addDefaultInstanceEntry savedDefaults)
    synthesizeSyntheticMVarsNoPostponing
  finally
    modifyEnv fun env => defaultInstanceExtension.setState env savedDefaults
  for (hole, decl) in detached do
    unless ← hole.isAssigned do
      -- Back to a tactic goal: only its tactic may fill it, not a passing unification.
      hole.setKind .syntheticOpaque
      registerSyntheticMVar decl.stx hole decl.kind
  synthesizeSyntheticMVarsNoPostponing
  if ← MonadLog.hasErrors then throwAbortTerm
  instantiateMVars inst

/-- Elaborate a concrete `Instantiation` term of the module, filling its type holes from the
module's `instantiate` constraints (see `elabInstantiationAgainst`). -/
def Module.elabInstantiation (mod : Module) (stx : Term) : TermElabM Expr := do
  elabInstantiationAgainst (← elabTerm instantiationType none) stx mod.instantiationTemplate

/-- Internal wrapper shared by concrete execution entry points. -/
syntax (name := instantiationWithConstraints) "__veil_instantiation% " term : term

@[term_elab instantiationWithConstraints]
def elabInstantiationWithConstraints : TermElab := fun stx _ => do
  let mod ← getCurrentModule
  mod.elabInstantiation ⟨stx[1]⟩

/-- `__veil_instantiation%` for module `X`, declared in this file or in an imported one, from
what `#gen_executable` recorded about it. -/
syntax (name := instantiationOfModule) "__veil_instantiation_of% " ident ppSpace term : term

@[term_elab instantiationOfModule]
def elabInstantiationOfModule : TermElab := fun stx _ => do
  let `(__veil_instantiation_of% $modId:ident $instTerm) := stx | throwUnsupportedSyntax
  let some em ← getExecutableModule? modId.getId
    | throwErrorAt modId "Module {modId.getId} has no executable definitions here."
  -- The declarations of the module are in its namespace, whatever is open here
  let instType ← mkConstWithFreshMVarLevels (em.name ++ instantiationTypeName)
  elabInstantiationAgainst instType instTerm do
    let some (template, binders) := em.instantiationTemplate
      | throwError "The holes of this instantiation of {em.name} cannot be filled here, since \
          its `instantiate` constraints could not be recorded. Give its types in full."
    -- The constraints are reported at the instantiation
    return (template, binders.map (·, .missing))

end Veil
