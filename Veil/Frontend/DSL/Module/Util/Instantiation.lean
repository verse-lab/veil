module

public meta import Veil.Frontend.DSL.Module.Util.Basic

public meta section

open Lean Meta Elab Term

namespace Veil

/-- Elaborate a concrete `Instantiation` term, filling its type holes (e.g.
`procSet := OrdList _`, or a bare `procSet := _`) from the module's `instantiate`
constraints.

Each `instantiate` declaration becomes an ordinary typeclass obligation on the concrete
instantiation. Lean postpones an obligation whose type still has holes and, once nothing
else makes progress, tries the class's `@[default_instance]`s: unifying such an instance
head with the obligation assigns the holes. So holes are only filled for classes whose
instances are marked `@[default_instance]` (Veil's own containers are); for any other
class the hole stays stuck and is reported at the `instantiate` declaration. Fully
specified instantiations take the ordinary elaboration path and are not checked here. -/
def Module.elabInstantiation (mod : Module) (stx : Term) : TermElabM Expr := do
  let instType ← elabTerm instantiationType none
  let inst ← elabTermEnsuringType stx instType
  let hasTypeHole ← (← getMVars inst).anyM fun hole => do
    return (← whnf (← inferType (mkMVar hole))).isSort
  unless hasTypeHole do return inst
  -- The module's parameter binders as a `∀`-template: instantiating it with the concrete
  -- values yields the obligations, with the dependencies between them already in place.
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
  let (vars, _, _) ← forallMetaTelescopeReducing template (kind := .synthetic)
  let mut obligations : Array (Parameter × MVarId) := #[]
  for p in params, var in vars do
    match p.kind with
    | .sort _ | .userParameter =>
      -- Reduce the projection: an unreduced `inst.node` mentions the whole literal, holes
      -- included, so unifying a hole with it would fail the occurs check.
      var.mvarId!.assign (← whnf (← mkProjection inst p.name))
    | .moduleTypeclass .userDefined => obligations := obligations.push (p, var.mvarId!)
    | _ => pure ()
  -- The auto-generated sort assumptions are only needed where a user constraint mentions them.
  for p in params, var in vars do
    if p.kind == .moduleTypeclass .sortAssumption then
      if ← obligations.anyM fun (_, id) => do return (← getMVars (← id.getType)).contains var.mvarId! then
        obligations := obligations.push (p, var.mvarId!)
  -- Hand the obligations to Lean's standard synthesis loop as typeclass problems; an
  -- obligation that cannot be solved is reported at its `instantiate` declaration.
  -- (The previous handling should ensure that `id` is a typeclass goal.)
  for (p, id) in obligations do
    registerSyntheticMVar p.userSyntax id (.typeClass none)
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
  -- own loop inside this call (`elabInstantiation` itself does not iterate).
  synthesizeSyntheticMVarsNoPostponing
  for (hole, decl) in detached do
    unless ← hole.isAssigned do
      -- Back to a tactic goal: only its tactic may fill it, not a passing unification.
      hole.setKind .syntheticOpaque
      registerSyntheticMVar decl.stx hole decl.kind
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars inst

/-- Internal wrapper shared by concrete execution entry points. -/
syntax (name := instantiationWithConstraints) "__veil_instantiation% " term : term

@[term_elab instantiationWithConstraints]
def elabInstantiationWithConstraints : TermElab := fun stx _ => do
  let mod ← getCurrentModule
  mod.elabInstantiation ⟨stx[1]⟩

end Veil
