import Lean
import Veil.Frontend.DSL.Module.Names
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Syntax
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.State
import Veil.Frontend.DSL.Util
import Veil.Frontend.DSL.State.Repr
import Veil.Util.Meta
import Mathlib.Data.FinEnum
import Mathlib.Tactic.ProxyType

open Lean Parser Elab Command Term

/-! ## Background theory and State

Implementation note: despite the fact that many methods in this file
are in the `CommandElabM` monad, you MUST NOT use `elabCommand`,
`elabVeilCommand`, or `modify` the environment from any method in this
file. All the environment-modifying operations should be done in
`Elaborators.lean`!.

Methods in this file must return the changed `Module` and the `Syntax`
to be elaborated. They MUST NOT change the environment themselves. This
is to keep the logic well-encapsulated.
-/

namespace Veil

instance : ToString Mutability where
  toString
    | Mutability.mutable => "mutable"
    | Mutability.immutable => "immutable"
    | Mutability.inherit => "inherit"

 /-- Fields are `mutable` by default. -/
def Mutability.fromStx (m : Option (TSyntax `stateMutability)) : Mutability :=
  if let some stx := m then
    match stx with
    | `(stateMutability|immutable) => Mutability.immutable
    | `(stateMutability|mutable) => Mutability.mutable
    | _ => unreachable!
  else
    Mutability.mutable

instance : ToString StateComponentKind where
  toString
    | StateComponentKind.individual => "individual"
    | StateComponentKind.relation => "relation"
    | StateComponentKind.function => "function"
    | StateComponentKind.module => "module"

def StateComponentKind.fromStx (k : TSyntax `stateComponentKind) : StateComponentKind :=
  match k with
  | `(stateComponentKind|individual) => StateComponentKind.individual
  | `(stateComponentKind|relation) => StateComponentKind.relation
  | `(stateComponentKind|function) => StateComponentKind.function
  | _ => panic! s!"Invalid state component kind: {k}"

instance : ToString StateComponentType where
  toString
    | StateComponentType.simple t => toString t
    | StateComponentType.complex b d  => s!"{b} : {d}"

instance : ToString StateComponent where
  toString sc := s!"{sc.mutability} {sc.kind} {sc.name} {sc.type}"

def StateComponentType.stx [Monad m] [MonadQuotation m] [MonadError m] (sct : StateComponentType) : m (TSyntax `term) := do
    match sct with
    | .simple t => getSimpleBinderType t
    | .complex b d => getSimpleBinderType $ ← complexBinderToSimpleBinder (mkIdent Name.anonymous) b d

/-- Returns, e.g., `initial_msg : address → address → round → value → Prop` -/
def StateComponent.getSimpleBinder [Monad m] [MonadQuotation m] [MonadError m] (sc : StateComponent) : m (TSyntax ``Command.structSimpleBinder) := do
  match sc.type with
  | .simple t => return t
  | .complex b d => return ← complexBinderToSimpleBinder (mkIdent sc.name) b d

def StateComponent.isMutable (sc : StateComponent) : Bool := sc.mutability == Mutability.mutable
def StateComponent.isImmutable (sc : StateComponent) : Bool := sc.mutability == Mutability.immutable

def StateComponent.stx [Monad m] [MonadQuotation m] [MonadError m] (sc : StateComponent) : m Syntax := sc.getSimpleBinder
def StateComponent.typeStx [Monad m] [MonadQuotation m] [MonadError m] (sc : StateComponent) : m Term := sc.type.stx

/-! ## Assertions about state (or background theory) -/

instance : ToString StateAssertionKind where
  toString
    | StateAssertionKind.assumption => "assumption"
    | StateAssertionKind.invariant => "invariant"
    | StateAssertionKind.trustedInvariant => "trusted invariant"
    | StateAssertionKind.safety => "safety"
    | StateAssertionKind.termination => "termination"

instance : ToString StateAssertion where
  toString sa := s!"{sa.kind} [{sa.name}] {sa.term}"

/-! ## Procedure and actions -/

def initializerName : Name := `initializer

def ProcedureKind.isAction (kind : ProcedureInfo) : Bool :=
  match kind with
  | .action _ => true
  | _ => false

def ProcedureInfo.name : ProcedureInfo → Name
  | .action name => name
  | .procedure name => name
  | .initializer => initializerName

def ProcedureSpecification.name (a : ProcedureSpecification) : Name := a.info.name

def Parameter.environmentTheory [Monad m] [MonadQuotation m] : m Parameter :=
  return { kind := .backgroundTheory, name := environmentTheoryName, «type» := ← `(Type), userSyntax := .missing }

def Parameter.environmentState [Monad m] [MonadQuotation m] : m Parameter :=
  return { kind := .environmentState, name := environmentStateName, «type» := ← `(Type), userSyntax := .missing }

def Parameter.mode [Monad m] [MonadQuotation m] : m Parameter :=
  return { kind := .mode, name := veilModeVar.getId, «type» := mkIdent ``Mode, userSyntax := .missing }

def Parameter.fieldConcreteType [Monad m] [MonadQuotation m] : m Parameter :=
  return { kind := .fieldConcreteType, name := fieldConcreteTypeName, «type» := ← `($(structureFieldLabelType stateName) → Type), userSyntax := .missing }

def Parameter.isRelatedToFieldRep (param : Parameter) : Bool :=
  match param.kind with
  | .fieldConcreteType => true
  | .moduleTypeclass .fieldRepresentation | .moduleTypeclass .lawfulFieldRepresentation => true
  | _ => false

def Module.freshWithName [Monad m] [MonadQuotation m] (name : Name) : m Module := do
  let params := #[← Parameter.environmentTheory, ← Parameter.environmentState]
  return { name := name, parameters := params, dependencies := #[], signature := #[], procedures := #[], assertions := #[], _declarations := .emptyWithCapacity, _derivedDefinitions := .emptyWithCapacity }

def Module.isDeclared (mod : Module) (name : Name) : Bool :=
  mod._declarations.contains name

def Module.throwIfAlreadyDeclared [Monad m] [MonadError m] (mod : Module) (name : Name) : m Unit := do
  if mod.isDeclared name then
    throwError s!"{name} is already declared (as a {repr mod._declarations[name]!}) in module {mod.name}. Cannot redeclare it!"

/-- Is the state of this module defined (in the sense that it can no
longer be changed, since some definitions already depend on it)? -/
def Module.isStateDefined (mod : Module) : Bool := mod._stateDefined

def Module.isSpecFinalized (mod : Module) : Bool := mod._specFinalized

def Module.throwIfStateAlreadyDefined [Monad m] [MonadError m] (mod : Module) : m Unit := do
  if mod.isStateDefined then
    throwError s!"The state of module {mod.name} has already been defined. It can no longer be changed!"

def Module.throwIfSpecAlreadyFinalized [Monad m] [MonadError m] (mod : Module) : m Unit := do
  if mod.isSpecFinalized then
    throwError s!"The specification of module {mod.name} has already been finalized. You can no longer add procedures or assertions!"

/-- Convert a `Parameter` to a `bracketedBinder` syntax. -/
def Parameter.binder [Monad m] [MonadQuotation m] (p : Parameter) : m (TSyntax `Lean.Parser.Term.bracketedBinder) :=
  match p.kind with
  | .moduleTypeclass _ | .definitionParameter _ .typeclass =>
    if p.name != Name.anonymous then
      `(bracketedBinder|[$(mkIdent p.name) : $(p.type)])
    else
      `(bracketedBinder|[$(p.type)])
  | .definitionParameter _ .implicit => `(bracketedBinder|{$(mkIdent p.name) : $(p.type)})
  | _ =>
    match p.default with
    | .none => `(bracketedBinder|($(mkIdent p.name) : $(p.type)))
    | .some (.term defValue) => `(bracketedBinder|($(mkIdent p.name) : $(p.type) := $defValue))
    | .some (.tactic tactic) => `(bracketedBinder|($(mkIdent p.name) : $(p.type) := by $tactic:tacticSeq))

def Parameter.bracketedExplicitBinder [Monad m] [MonadQuotation m] [MonadError m] (p : Parameter) : m (TSyntax ``Lean.bracketedExplicitBinders) := do
  match p.kind with
  | .definitionParameter _ .explicit => `(bracketedExplicitBinders|($(identToBinderIdent $ mkIdent p.name) : $(p.type)))
  | _ => throwError "[Parameter.bracketedExplicitBinder]: unexpected parameter kind: {repr p.kind}"

def ProcedureSpecification.binders [Monad m] [MonadQuotation m] [MonadError m] (a : ProcedureSpecification) : m (TSyntaxArray ``Lean.Parser.Term.bracketedBinder) :=
  a.params.mapM (·.binder)

def DerivedDefinition.binders [Monad m] [MonadQuotation m] [MonadError m] (dd : DerivedDefinition) : m (TSyntaxArray ``Lean.Parser.Term.bracketedBinder) :=
  dd.params.mapM (·.binder)

/-- Convert a `Parameter` to a `Term` syntax for the equivalent
argument. Unnamed typeclass instances are left for typeclass inference
(i.e. `_`). -/
def Parameter.arg [Monad m] [MonadQuotation m] (p : Parameter) : m Term := do
  match p.kind with
  | .moduleTypeclass _ | .definitionParameter _ .typeclass =>
    if p.name != Name.anonymous then
      `(term| $(mkIdent p.name))
    else
      `(term| _)
  | _ => `(term| $(mkIdent p.name))

def Parameter.ident [Monad m] [MonadQuotation m] (p : Parameter) : m Ident := return mkIdent p.name

def explicitBindersToParameters [Monad m] [MonadQuotation m] [MonadError m] (stx : Option (TSyntax ``Lean.explicitBinders)) (forDef : Name) : m (Array Parameter) := do
  match stx with
  | .none => pure #[]
  | .some stx => explicitBindersFlatMapM stx fun bi tp => do
      let id ← binderIdentToIdent bi
      pure { kind := .definitionParameter forDef .explicit, name := id.getId, «type» := tp, userSyntax := stx }

def parametersToExplicitBinders [Monad m] [MonadQuotation m] [MonadError m] (params : Array Parameter) : m (TSyntax ``Lean.explicitBinders) := do
  `(explicitBinders| $(← params.mapM (·.bracketedExplicitBinder))*)

def bracketedBinderToParameter [Monad m] [MonadQuotation m] [MonadError m] (stx : TSyntax `Lean.Parser.Term.bracketedBinder) (forDef : Name) : m Parameter := do
  match stx with
  | `(bracketedBinder| ($id:ident : $tp)) => return { kind := .definitionParameter forDef .explicit, name := id.getId, «type» := tp, userSyntax := stx }
  -- explicit binder with default value (provided by either a term or a tactic), e.g. for `th` and `st` in ghost relations
  | `(Term.explicitBinderF| ($id:ident : $tp:term := $defValue:term)) =>
    return { kind := .definitionParameter forDef .explicit, name := id.getId, «type» := tp, default := .some (.term defValue), userSyntax := stx }
  | `(Term.explicitBinderF| ($id:ident : $tp:term := by $tactic:tacticSeq)) =>
    return { kind := .definitionParameter forDef .explicit, name := id.getId, «type» := tp, default := .some (.tactic tactic), userSyntax := stx }
  | `(bracketedBinder| {$id:ident : $tp}) => return { kind := .definitionParameter forDef .implicit, name := id.getId, «type» := tp, userSyntax := stx }
  | `(bracketedBinder| [$id:ident : $tp]) => return { kind := .definitionParameter forDef .typeclass, name := id.getId, «type» := tp, userSyntax := stx }
  | _ => throwError "[bracketedBinderToParameter]: unexpected syntax: {stx}"

def Module.declarationBaseParams [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (k : DeclarationKind) : m (Array Parameter) := do
  match k with
  | .moduleParameter => throwError "[Module.declarationBaseParams]: moduleParameter has no base parameters"
  | .stateComponent _ _ => sortParameters mod
  | .stateAssertion .assumption => pure (theoryParameters mod)
  | .stateAssertion .invariant | .stateAssertion .safety | .stateAssertion .trustedInvariant => pure mod.parameters
  | .stateAssertion .termination => pure mod.parameters -- the same as `invariant`
  | .procedure _ => pure mod.parameters
  | .derivedDefinition k _ => derivedDefinitionBaseParams mod k
where
  sortFilterMapFn {α : Type} (mod : Module) (f : Parameter → m α) : m (Array α) := do
    mod.parameters.filterMapM fun p => do match p.kind with
    | .sort _ => f p
    | _ => pure .none
  sortParameters (mod : Module) : m (Array Parameter) := do
    sortFilterMapFn mod (pure ·)
  theoryParameters (mod : Module) : Array Parameter :=
    mod.parameters.filterMap fun p => match p.kind with
    | .environmentState | .fieldConcreteType => .none
    | .moduleTypeclass kd =>
      match kd with
      | .environmentState | .fieldRepresentation | .lawfulFieldRepresentation => .none
      | _ => .some p
    | _ => .some p
  derivedDefinitionBaseParams (mod : Module) (k : DerivedDefinitionKind) : m (Array Parameter) := do
    match k with
    | .stateLike => sortParameters mod
    | .assumptionLike | .theoryGhost => pure (theoryParameters mod)
    | .invariantLike | .actionLike | .theoremLike | .ghost => pure mod.parameters
    | .actionDoLike => pure $ #[← Parameter.mode] ++ mod.parameters

/-- For an **existing** declaration, return the parameters it needs, split into
three components:
  - base parameters (imposed by the module on this particular definition)
  - "extra" parameters (decidable instances required to make this definition
  executable)
  - actual parameters (the parameters that the definition actually takes)
 -/
def Module.declarationSplitParams [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (forDeclaration : Name) (k : DeclarationKind) : m (Array Parameter × Array Parameter × Array Parameter) := do
  let baseParams ← mod.declarationBaseParams k
  let (extraParams, actualParams) ← (do
    match k with
    | .derivedDefinition _ _ =>
      let .some dd := mod._derivedDefinitions[forDeclaration]?
        | throwError "[Module.declarationSplitParams]: derived definition {forDeclaration} not found"
      pure (dd.extraParams, dd.params)
    | .stateAssertion _ => do
        let .some sa := mod.assertions.find? (fun a => a.name == forDeclaration)
          | throwError "[Module.declarationSplitParams]: assertion {forDeclaration} not found"
        pure (sa.extraParams, #[])
    | .procedure _ => do
        let .some proc := mod.procedures.find? (fun a => a.name == forDeclaration)
          | throwError "[Module.declarationSplitParams]: procedure {forDeclaration} not found"
        pure (proc.extraParams, proc.params)
    | _ => throwError "[Module.declarationSplitParams]: declaration {forDeclaration} has unsupported kind {repr k}")
  -- dbg_trace "declarationSplitParams: {repr k} {forDeclaration} -> baseParams {baseParams.map (·.name)} extraParams {extraParams.map (·.name)}"
  return (baseParams, extraParams, actualParams)

/-- Returns a pair consisting of:
- `modParams`: the parameters that the module imposes on this declaration,
including "extra" parameters (decidable instances)
- `actualParams`: the parameters that the declaration "actually" takes
-/
def Module.declarationAllParams [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (forDeclaration : Name) (k : DeclarationKind) : m (Array Parameter × Array Parameter) := do
  let (baseParams, extraParams, actualParams) ← mod.declarationSplitParams forDeclaration k
  return (baseParams ++ extraParams, actualParams)

def Module.declarationAllParamsMapFn [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (f : Parameter → m α) (forDeclaration : Name) (k : DeclarationKind) : m (Array α × Array Parameter) := do
  let (allModParams, actualParams) ← mod.declarationAllParams forDeclaration k
  return (← allModParams.mapM f, actualParams)

/-- Utility function to get the binders and arguments for a declaration, split
between those imposed by the module and those the declaration "actually" has.
-/
def Module.declarationSplitBindersArgs [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (forDeclaration : Name) (k : DeclarationKind) : m ((Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Array Term) × (Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Array Term)) := do
  let (allModParams, specificParams) ← mod.declarationAllParams forDeclaration k
  let (allModBinders, allModArgs) := (← allModParams.mapM (·.binder), ← allModParams.mapM (·.ident))
  let (specificBinders, specificArgs) := (← specificParams.mapM (·.binder), ← specificParams.mapM (·.arg))
  return ((allModBinders, allModArgs), (specificBinders, specificArgs))

/-- Utility function to get all the binders and arguments for a declaration -/
def Module.declarationAllBindersArgs {m} [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (forDeclaration : Name) (k : DeclarationKind) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Array Term) := do
  let ((allModBinders, allModArgs), (specificBinders, specificArgs)) ← mod.declarationSplitBindersArgs forDeclaration k
  return (allModBinders ++ specificBinders, allModArgs ++ specificArgs)

def Module.declarationAllBinders {m} [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (forDeclaration : Name) (k : DeclarationKind) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let ((allModBinders, _), (specificBinders, _)) ← mod.declarationSplitBindersArgs forDeclaration k
  return allModBinders ++ specificBinders

def Module.declarationAllArgs {m} [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (forDeclaration : Name) (k : DeclarationKind) : m (Array Term) := do
  let ((_, allModArgs), (_, specificArgs)) ← mod.declarationSplitBindersArgs forDeclaration k
  return allModArgs ++ specificArgs

/-- Create parameters for a derived definition which **does not
exist**. FIXME: this is `O(n^2)`-ish, so it might become a bottleneck.
The solution is to also store an index into the appropriate array in
`_declarations`. -/
def Module.mkDerivedDefinitionsParamsMapFn [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (f : Parameter → m α) (k : DeclarationKind) : m (Array α × Array α) := do
  let .derivedDefinition _ derivedFrom := k
    | throwError "[Module.mkDerivedDefinitionsParamsMapFn]: invalid kind"
  let baseParams ← mod.declarationBaseParams k
  let extraParams := Array.flatten $ ← (derivedFrom.toArray).filterMapM (fun dec => do
    let .some dk := mod._declarations[dec]?
      | throwError "[Module.mkDerivedDefinitionsParamsMapFn]: declaration {dec} not found"
    let extraParams ← (match dk with
    -- FIXME: replace these `filterMap` calls with a `find?`, similar to `declarationSplitParams`
    -- TODO: replace all of these with a `O(1)` lookup
    | .stateAssertion _ => return mod.assertions.filterMap (fun a => if dec == a.name then .some a.extraParams else .none)
    | .procedure _ => return mod.procedures.filterMap (fun a => if dec == a.name then .some a.extraParams else .none)
    | .derivedDefinition _ _ => return mod._derivedDefinitions.valuesArray.filterMap (fun a => if dec == a.name then .some a.extraParams else .none)
    | _ => throwError "[Module.mkDerivedDefinitionsParamsMapFn]: declaration {dec} (included in derivedFrom) has unsupported kind")
    pure $ Array.flatten extraParams)
  return (← baseParams.mapM f, ← extraParams.mapM f)

private def Module.sortFilterMapFn [Monad m] [MonadQuotation m] (mod : Module) (f : Parameter → m α) : m (Array α) := do
  mod.parameters.filterMapM fun p => do match p.kind with
  | .sort _ => f p
  | _ => pure .none

def Module.sortBinders [Monad m] [MonadQuotation m] (mod : Module) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  mod.sortFilterMapFn (·.binder)

def Module.sortIdents [Monad m] [MonadQuotation m] (mod : Module) : m (Array Ident) := do
  mod.sortFilterMapFn (·.ident)

/-- Returns sort parameters along with their kind (uninterpreted or enum). -/
def Module.sortParams (mod : Module) : Array (Parameter × SortKind) :=
  mod.parameters.filterMap fun p => match p.kind with
  | .sort k => some (p, k)
  | _ => none

/-- Almost the same as `Module.sortBinders`, but this is _only_ for sort parameters
of theory or states, or their related definitions (e.g., `casesOn` functions). -/
def Module.sortBindersForTheoryOrState [Monad m] [MonadQuotation m] (mod : Module) (forStateWithFieldConcreteType? : Bool := false) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  if forStateWithFieldConcreteType?
  then Parameter.fieldConcreteType >>= Parameter.binder >>= (pure #[·])
  else mod.sortBinders

/-- Almost the same as `Module.sortIdents`, but this is _only_ for sort parameters
of theory or states, or their related definitions (e.g., `casesOn` functions). -/
def Module.sortIdentsForTheoryOrState [Monad m] [MonadQuotation m] (mod : Module) (forStateWithFieldConcreteType? : Bool := false) : m (Array Ident) := do
  if forStateWithFieldConcreteType? then pure #[fieldConcreteType] else mod.sortIdents

def Module.assumptions (mod : Module) : Array StateAssertion :=
  mod.assertions.filter (fun a => a.kind == .assumption)

def Module.actions (mod : Module) : Array ProcedureSpecification :=
  mod.procedures.filter (fun p => match p.info with | .action _ => true | _ => false)

/-- All `invariant`s, `safety`, and `trusted invariant`s.-/
def Module.invariants (mod : Module) : Array StateAssertion :=
  mod.assertions.filter fun a => match a.kind with
  | .invariant | .safety | .trustedInvariant => true
  | .termination => false
  | .assumption => false

def Module.terminations (mod : Module) : Array StateAssertion :=
  mod.assertions.filter fun a => match a.kind with
  | .invariant | .safety | .trustedInvariant => false
  | .termination => true
  | .assumption => false

/-- All `invariant`s and `safety`s.-/
def Module.checkableInvariants (mod : Module) : Array StateAssertion :=
  mod.assertions.filter fun a => match a.kind with
  | .invariant | .safety => true
  | .termination => false
  | .trustedInvariant | .assumption => false

def Module.trustedInvariants (mod : Module) : Array StateAssertion :=
  mod.assertions.filter (fun a => a.kind == .trustedInvariant)

def Module.safeties (mod : Module) : Array StateAssertion :=
  mod.assertions.filter (fun a => a.kind == .safety)

/-- Recursively get all fields that are available in this module
(including fields from child modules). -/
def Module.getFieldsRecursively [Monad m] [MonadEnv m] [MonadError m] (mod : Module) : m (Array Name) := do
  let res ← go mod Name.anonymous
  return res
where
  go (mod : Module) (path : Name) : m (Array Name) := do
    let mut fields := #[]
    for comp in mod.signature do
      match comp.kind with
      | .module =>
        -- FIXME: Not fully sure how to obtain the child module name here.
        -- Maybe need to extend the definition of `StateComponent`?
        /-
        let .some modName := comp.moduleName
          | throwError s!"(internal error) {comp} has no module name in its StateComponent definition"
        let spec' := (← globalSpecCtx.get)[modName]!.spec
        fields := fields ++ (← go spec' (path.push comp.name))
        -/
        pure ()
      | _ => fields := fields.push (path.appendCore comp.name)
    return fields

/-- Throw an error if the field (which we're trying to assign to) was
declared immutable. -/
def Module.throwIfImmutable [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] (mod : Module) (nm : Name) (isTransition : Bool := false) : m Unit := do
  -- NOTE: This code supports two modes of operation:
  -- (a) child modules' state is immutable in the parent
  -- (b) child modules' state mutability annotations are inherited in the parent
  let .some sc := mod.signature.find? (·.name == nm.getRoot)
    | throwError "trying to assign to undeclared state component {nm}"
  if sc.kind == StateComponentKind.module && sc.isImmutable then -- (a)
    throwError "cannot assign to {nm}: child module's ({sc.name}) state is immutable in the parent ({mod.name})"
  else -- (b)
    let (modules, field, innerMostMod) ← getInnerMostModule mod nm
    trace[veil.debug] "{nm} ({sc}) → assigning to field {ppModules modules}.{field} (declared in module {innerMostMod.name})"
    let .some sc' := innerMostMod.signature.find? (·.name == field)
      | throwError "trying to assign to undeclared state component {nm} (fully qualified name: {ppModules modules}.{field})"
    if sc'.isImmutable then
      let msg := if isTransition then "the transition might modify" else "trying to assign to"
      let explanation := if isTransition then s!" (since it mentions its primed version {sc'.name.appendAfter "'"})" else ""
      throwError "{sc'.kind} {sc'.name} in module {innerMostMod.name} was declared immutable, but {msg} it{explanation}!"
where
  ppModules (modules : Array Name) := ".".intercalate $ Array.toList $ modules.map (·.toString)
  getInnerMostModule (mod : Module) (nm : Name) : m (Array Name × Name × Module) := do
    let mut curMod := mod
    let field := nm.updatePrefix .anonymous
    let mut path := nm.components.dropLast
    -- This contains the full names of the modules in the path to the field
    let mut modules : Array Name := #[]
    while true do
      let scName :: path' := path
        | break
      let .some sc := curMod.signature.find? (·.name == scName)
        | throwError "trying to assign to {nm}, but {scName} is not a declared field in {ppModules modules}"
      -- FIXME: Not fully sure how to obtain the child module name here.
      -- Maybe need to extend the definition of `StateComponent`?
      -- let .some subMod := sc.moduleName
      --   | throwError "(internal error) {sc} has no module name in its StateComponent definition"
      -- modules := modules.push topModule
      path := path'
      -- match (← globalSpecCtx.get)[subMod]? with
      -- | .some mod => curMod := mod.spec
      -- | .none => throwError "trying to assign to {nm}, but {subMod} (the module type of {sc} in {path}) is not a declared module"
    return (modules, field, curMod)

def Module.stateStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (withFieldConcreteType? : Bool := false) : m Term :=
  return ← `(term| @$(mkIdent stateName) $(← mod.sortIdentsForTheoryOrState withFieldConcreteType?)*)

def Module.theoryStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Term :=
  return ← `(term| @$(mkIdent theoryName) $(← mod.sortIdents)*)

def Module.declareUninterpretedSort [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (name : Name) (userStx : Syntax) (sortKind : SortKind := .uninterpretedSort) : m Module := do
  mod.throwIfAlreadyDeclared name
  let typeT ← `(term|Type)
  let param : Parameter := { kind := .sort sortKind, name := name, «type» := typeT, userSyntax := userStx }
  let id := mkIdent name
  let dec_eq_type ← `(term|$(mkIdent ``DecidableEq).{1} $id)
  let dec_inhabited_type ← `(term|$(mkIdent ``Inhabited).{1} $id)
  let dec_eq : Parameter := { kind := .moduleTypeclass .sortAssumption, name := Name.mkSimple s!"{name}_dec_eq", «type» := dec_eq_type, userSyntax := userStx }
  let inhabited : Parameter := { kind := .moduleTypeclass .sortAssumption, name := Name.mkSimple s!"{name}_inhabited", «type» := dec_inhabited_type, userSyntax := userStx }
  let params := #[param, dec_eq, inhabited]
  let newDecls := #[(name, DeclarationKind.moduleParameter)] ++ params.map (fun p => (p.name, DeclarationKind.moduleParameter))
  return { mod with parameters := mod.parameters.append params, _declarations := mod._declarations.insertMany newDecls }

def isValidStateComponentType (kind : StateComponentKind) (tp : Expr) : CommandElabM Bool := do
  let (returnsProp, returnsBool) ← liftTermElabM $ Meta.forallTelescope tp (fun _ b => return (b.isProp, b.isBool))
  -- To keep actions executable without requiring `Decidable` instances
  -- for `State` and `Theory` fields, we disallow `Prop` return types.
  if returnsProp then
    return false
  match kind with
  | .individual => return !tp.isArrow
  | .relation => return returnsBool
  | .function => return tp.isArrow
  | .module =>
    -- `tp` must be a structure
    let constName := tp.getAppFn.constName?
    match constName with
    | .some constName => return (isStructure (←  getEnv) constName)
    | .none => return false

def Module.declareStateComponent (mod : Module) (sc : StateComponent) : CommandElabM Module := do
  if sc.kind == StateComponentKind.module || sc.mutability == Mutability.inherit then
    throwErrorAt sc.userSyntax "declareStateComponent called with `module` kind or `inherit` mutability; use `declareChildModule` instead"
  if !sc.name.isAtomic then
    throwErrorAt sc.userSyntax s!"Invalid name: {sc.name} is not an atomic name."
  mod.throwIfAlreadyDeclared sc.name
  let sig ← sc.getSimpleBinder
  let tp ← match sig with
  | `(Command.structSimpleBinder| $_:ident : $tp:term) => liftTermElabMWithBinders (← mod.sortBinders) (fun _ => do Meta.reduceAll $ ← elabTerm tp .none)
  | _ => throwErrorAt sc.userSyntax "Unsupported syntax for state component"
  if !(← isValidStateComponentType sc.kind tp) then
    failureMsg sig sc
  let mod := { mod with signature := mod.signature.push sc, _declarations := mod._declarations.insert sc.name sc.declarationKind }
  return mod
where
  failureMsg (_sig : TSyntax `Lean.Parser.Command.structSimpleBinder) (comp : StateComponent) : CommandElabM Unit := do
    throwErrorAt comp.userSyntax match comp.kind with
    | .individual => m!"Invalid type: individuals must not be arrow types, and cannot be Prop."
    | .relation => m!"Invalid type: relations must return Bool."
    | .function => m!"Invalid type: functions must have arrow type and not return Bool or Prop."
    | .module => m!"Invalid type: module state components must be structures."

def Module.immutableComponents (mod : Module) : Array StateComponent :=
  mod.signature.filter fun sc => sc.mutability == Mutability.immutable

def Module.mutableComponents (mod : Module) : Array StateComponent :=
  mod.signature.filter fun sc => sc.mutability == Mutability.mutable

def Module.getStateComponentTypeStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (name : Name) : m Term := do
  match mod.signature.find? (fun sc => sc.name == name) with
  | some sc => return ← sc.typeStx
  | none => throwErrorAt (← getRef) s!"State component {name} not found in module {mod.name}"

def Module.getTheoryBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  mod.signature.filterMapM fun sc => do
    match sc.mutability with
    | .immutable => return .some $ ← mkBinder sc
    | _ => pure .none
  where
    -- FIXME: this is a workaround for [lean4#10429](https://github.com/leanprover/lean4/pull/10429)
    mkBinder (sc : StateComponent) : m (TSyntax `Lean.Parser.Term.bracketedBinder) := do
      `(bracketedBinder| ($(mkIdent sc.name) : $(← sc.typeStx)))

/-
def Module.getStateBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  mod.signature.filterMapM fun sc => do
    match sc.mutability with
    | .mutable =>
      dbg_trace "getStateBinders: adding binder for state component {sc.name} of type {← sc.typeStx}"
      let (res, base) ← splitForallArgsCodomain (← sc.typeStx)
      dbg_trace "  splitForallArgsCodomain: base = {base}, res = {res}"
      return .some $ ← `(bracketedBinder| ($(mkIdent sc.name) : $(← sc.typeStx)))
    | _ => pure .none
-/

/-- Get binders for assuming that every sort has an instance of `className` (e.g. `Ord node`). -/
private def Module.assumeForEverySort [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (className : Name) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  (← mod.sortIdents).mapM fun sort => do
    -- Special case `TransCmp` and `LawfulEqCmp`
    if #[``Std.TransCmp, ``Std.LawfulEqCmp].contains className then
      `(bracketedBinder|[$(mkIdent className) ($(mkIdent ``Ord.compare) ( $(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $sort) ))])
    else
      `(bracketedBinder|[$(mkIdent className) $sort])

/-- Given a list of state components, return the syntax for a structure
definition including those components. -/
private def structureDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (name : Name) (params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (deriveInstances : Bool := true)
  (fields : Array (TSyntax `Lean.Parser.Command.structSimpleBinder)) : m (Array Syntax) := do
  if deriveInstances then
    let instances := #[``Inhabited, ``Nonempty].map Lean.mkIdent
    let defCmd ← `(structure $(mkIdent name) $params* where
        $(mkIdent `mk):ident :: $[$fields]*
      deriving $[$instances:ident],*)
    return #[defCmd]
  else
    let defCmd ← `(structure $(mkIdent name) $params* where
      $(mkIdent `mk):ident :: $[$fields]*)
    return #[defCmd]

/-- Syntax for *defining* the mutable state of a module as a `structure`. The
syntax for the type is `mod.stateStx`. -/
private def Module.stateDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array Syntax) := do
  let defCmds ← structureDefinitionStx stateName (← mod.sortBindersForTheoryOrState false) (deriveInstances := true)
    (← mod.mutableComponents.mapM fun sc => sc.getSimpleBinder)
  return defCmds ++ #[← `(command| deriving_repr_via_finite_sorts $(mkIdent stateName))]

/-- Similar to `Module.stateDefinitionStx` but each field of `State` is
abstracted by a function from its label to a certain type. Note that
in this case, `deriveInstances` has to be `false`. -/
private def Module.fieldsAbstractedStateDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array Syntax) := do
  let stateLabelTypeName := structureFieldLabelTypeName stateName
  let fields ← mod.mutableComponents.mapM fun sc => do
    let ty ← `($fieldConcreteType $(mkIdent <| stateLabelTypeName ++ sc.name):ident)
    `(Command.structSimpleBinder| $(mkIdent sc.name):ident : $ty)
  let defCmds ← structureDefinitionStx stateName (← mod.sortBindersForTheoryOrState true) (deriveInstances := false) fields
  return defCmds ++ #[← mkInhabitedInstance, ← mkHashableInstance, ← mkBEqInstance, ← mkToJsonInstance, ← `(command| deriving_repr_via_fields $(mkIdent stateName))]
where
  /-- Generate binders of the form `(χ : State.Label → Type) [∀ f : State.Label, C (χ f)]` -/
  mkFieldConcreteTypeBinders (typeclass : Name) : m (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
    let χBinder ← Parameter.fieldConcreteType >>= Parameter.binder
    let f := mkIdent `f
    let stateLabelType := structureFieldLabelType stateName
    let constraint ← `(bracketedBinder| [∀ $f : $stateLabelType, $(mkIdent typeclass) ($fieldConcreteType $f)])
    return #[χBinder, constraint]
  mkInhabitedInstance : m Syntax := do
    let inhabitedTy ← `(term|$(mkIdent ``Inhabited) ($stateIdent ($fieldConcreteDispatcher:ident $(← mod.sortIdents)*)))
    let inhabitedAssumed := #[``Inhabited, ``Ord, ``DecidableEq, ``Enumeration, ``Std.LawfulEqCmp, ``Std.TransCmp]
    let inhabitedBinders := (← mod.sortBinders) ++ (← inhabitedAssumed.flatMapM mod.assumeForEverySort)
    `(instance $[$inhabitedBinders]* : $inhabitedTy := by constructor; constructor <;> dsimp_state_representation <;> exact $(mkIdent ``default))
  mkHashableInstance : m Syntax := do
    let hashableBinders ← mkFieldConcreteTypeBinders ``Hashable
    let hashableTy ← `(term| $(mkIdent ``Hashable) ($stateIdent $fieldConcreteType))
    let s := mkIdent `s
    -- Build the hash body: (hash s.field1) |> mixHash (hash s.field2) |> ...
    let fieldNames := mod.mutableComponents.map (·.name)
    let hashBody ← match fieldNames.toList with
      | [] => `(term| 0)
      | f :: fs =>
        let first ← `(term| $(mkIdent ``hash) ($s.$(mkIdent f)))
        fs.foldlM (init := first) fun acc field => do
          `(term| $acc |> $(mkIdent ``mixHash) ($(mkIdent ``hash) ($s.$(mkIdent field))))
    `(instance $[$hashableBinders]* : $hashableTy where hash := fun $s => $hashBody)
  mkBEqInstance : m Syntax := do
    let beqBinders ← mkFieldConcreteTypeBinders ``BEq
    let beqTy ← `(term| $(mkIdent ``BEq) ($stateIdent $fieldConcreteType))
    let (s1, s2) := (mkIdent `s1, mkIdent `s2)
    -- Build the beq body: s1.field1 == s2.field1 && s1.field2 == s2.field2 && ...
    let fieldNames := mod.mutableComponents.map (·.name)
    let beqBody ← match fieldNames.toList with
      | [] => `(term| true)
      | f :: fs =>
        let first ← `(term| $s1.$(mkIdent f) == $s2.$(mkIdent f))
        fs.foldlM (init := first) fun acc field => do
          `(term| $acc && $s1.$(mkIdent field) == $s2.$(mkIdent field))
    `(instance $[$beqBinders]* : $beqTy where beq := fun $s1 $s2 => $beqBody)
  mkToJsonInstance : m Syntax := do
    let toJsonBinders ← mkFieldConcreteTypeBinders ``Lean.ToJson
    let toJsonTy ← `(term| $(mkIdent ``Lean.ToJson) ($stateIdent $fieldConcreteType))
    let s := mkIdent `s
    -- Build the list of (name, toJson s.field) pairs
    let fieldNames := mod.mutableComponents.map (·.name)
    let jsonPairs ← fieldNames.mapM fun field => do
      let fieldStr := toString field
      `(term| ($(Syntax.mkStrLit fieldStr), $(mkIdent ``Lean.ToJson.toJson) $s.$(mkIdent field)))
    let toJsonBody ← `(term| $(mkIdent ``Lean.Json.mkObj) [$[$jsonPairs],*])
    `(instance $[$toJsonBinders]* : $toJsonTy where toJson := fun $s => $toJsonBody)


/-- Syntax for *defining* the immutable background theory of a module as a
`structure`. The syntax for the type is `mod.theoryStx`. -/
private def Module.theoryDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array Syntax) := do
  let defCmds ← structureDefinitionStx theoryName (← mod.sortBindersForTheoryOrState false) (deriveInstances := true)
    (← mod.immutableComponents.mapM fun sc => sc.getSimpleBinder)
  return defCmds ++ #[← `(command| deriving_repr_via_finite_sorts $(mkIdent theoryName))]

def Module.declareStateStructure [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Module × Array Syntax) := do
  mod.throwIfAlreadyDeclared environmentSubStateName
  let stx ← mod.stateDefinitionStx
  let stateStx ← mod.stateStx
  let substate : Parameter := { kind := .moduleTypeclass .environmentState, name := environmentSubStateName, «type» := ← `($(mkIdent ``IsSubStateOf) $stateStx $environmentState), userSyntax := .missing }
  return ({ mod with parameters := mod.parameters.push substate, _declarations := mod._declarations.insert environmentSubStateName .moduleParameter }, stx)

/-- Declare an inductive type with each constructor corresponding to each
field of `State` (i.e., each `State` component). -/
private def declareStructureFieldLabelType [Monad m] [MonadQuotation m] [MonadError m] (base : Name) (components : Array StateComponent) : m (Name × TSyntax `command) := do
  let fields ← components.mapM fun sc => `(Command.ctor| | $(mkIdent sc.name):ident )
  let name := structureFieldLabelTypeName base
  let res ← `(inductive $(mkIdent name) : Type where $[$fields]*)
  return (name, res)

/-- Helper structure used in the generation of field dispatchers.-/
private structure FieldMetadata where
  sc : StateComponent
  /-- The terms for the domain of the field. -/
  domainTerms : Array Term
  /-- The term for the codomain of the field. -/
  codomainTerm : Term

/-- Given, e.g. `node node`, create `#[node, node]`. -/
private def FieldMetadata.domainArray [Monad m] [MonadQuotation m] (fm : FieldMetadata) : m Term := `([ $[$fm.domainTerms],* ])

/-- Declare dispatchers that given the label for a specific field, returns the
types of its arguments and its codomain, as well as the concrete type of the
field. -/
private def Module.declareFieldDispatchers [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (base : Name) (fieldMetadata : Array FieldMetadata) (params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder))
  : m ((Array (Name × Syntax)) × (Name × Syntax)) := do
  let domainComponents ← fieldMetadata.mapM (·.domainArray)
  let coDomainComponents := fieldMetadata.map (·.codomainTerm)
  let f := mkVeilImplementationDetailIdent `f
  let casesOnName := structureFieldLabelTypeName base ++ `casesOn
  let fieldLabel ← `(bracketedBinder| ($f : $(structureFieldLabelType base)))
  let dParams := params ++ [fieldLabel]
  -- to domain dispatcher
  let todomain ← `(abbrev $(fieldLabelToDomain base) $dParams* : $(mkIdent ``List) Type := $(mkIdent casesOnName) $f $domainComponents*)
  -- to codomain dispatcher
  let tocodomain ← `(abbrev $(fieldLabelToCodomain base) $dParams* : Type := $(mkIdent casesOnName) $f $coDomainComponents*)
  -- concrete field representation dispatcher
  let cParams := params ++ (← mod.assumeForEverySort ``Ord) ++ [fieldLabel]
  let concreteTypes ← fieldMetadata.mapM (fun fm => fieldKindToType mod fm.sc)
  let toconcretetype ← `(abbrev $fieldConcreteDispatcher $cParams* : Type := $(mkIdent casesOnName) $f $concreteTypes*)
  return (#[(fieldLabelToDomainName base, todomain), (fieldLabelToCodomainName base, tocodomain)], (fieldConcreteTypeName, toconcretetype))
  where
  -- Generate the concrete type for a field based on its kind
  fieldKindToType (mod : Module) (sc : StateComponent) : m (TSyntax `term) := do
    let sortIdents ← mod.sortIdents
    let f := mkIdent <| Name.append (structureFieldLabelTypeName base) sc.name
    let domainGetter ← `(term|($(fieldLabelToDomain base):ident $sortIdents*) $f:ident)
    let codomainGetter ← `(term|($(fieldLabelToCodomain base):ident $sortIdents*) $f:ident)
    let (mapKeyTerm, mapValueTerm) := (← `(term| ($(mkIdent ``Veil.IteratedProd') <| $domainGetter)), codomainGetter)
    match sc.kind with
    | .individual => pure codomainGetter
    | .relation => `(term| $(mkIdent ``Std.TreeSet) $mapKeyTerm)
    | .function => `(term| $(mkIdent ``Veil.TotalTreeMap) $mapKeyTerm $mapValueTerm)
    | .module => throwError "[fieldKindToType] module kind is not supported"

/-- For each `sc` in `components`, analyze its type to extract the arguments
(domain) and codomain. -/
private def analyzeTypesOfStateComponents [Monad m] [MonadQuotation m] [MonadError m] (components : Array StateComponent) : m (Array FieldMetadata) := do
  components.mapM fun sc => do
    match sc.type with
    | .simple t =>
      let (domainTerms, codomainTerm) ← getSimpleBinderType t >>= splitForallArgsCodomain
      pure { sc, domainTerms, codomainTerm }
    | .complex b codomainTerm =>
      -- overlapped with `complexBinderToSimpleBinder`
      let domainTerms ← b.mapM fun m => match m with
        | `(bracketedBinder| ($_arg:ident : $tp:term)) => return tp
        | _ => throwError "unable to extract type from binder {m}"
      pure { sc, domainTerms, codomainTerm }

/-- Helper function to generate typeclass instance lifting declarations. -/
@[inline]
private def Module.declareInstanceLifting [Monad m] [MonadQuotation m] [MonadError m]
    (mod : Module) (assumingClasses : Array Name) (fieldLabelIdent : Ident)
    (instanceType : Term) (instanceName : Option Name := .none) (tactic : Option (TSyntax `tactic) := .none) : m Syntax := do
  let tactic := tactic.getD (← `(tactic| infer_instance_for_iterated_prod'))
  let assumedInstances ← assumingClasses.flatMapM fun className => mod.assumeForEverySort className
  let fieldLabel ← `(bracketedBinder|($fieldLabelIdent:ident : $(mkIdent `State.Label)))
  let binders := (← mod.sortBinders) ++ assumedInstances ++ [fieldLabel]
  match instanceName with
  | some name => `(instance $(mkIdent name):ident $[$binders]* : $instanceType := by cases $fieldLabelIdent:ident <;> $tactic)
  | none => `(instance $[$binders]* : $instanceType := by cases $fieldLabelIdent:ident <;> $tactic)

/-- NOTE: This is actually needed.-/
private def Module.declareInstanceLiftingForIteratedProd [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (deriveClass : Name) (assumingClasses : Array Name := #[deriveClass]) (instName : Option Name := .none) : m (Array Syntax) := do
  let (cls, sorts, fieldLabelIdent) := (mkIdent ``Enumeration, ← mod.sortIdents, mkVeilImplementationDetailIdent `f)
  let ty ← `(term | ($(mkIdent ``IteratedProd) <| ($(mkIdent ``List.map) $cls <| ($(fieldLabelToDomain stateName) $sorts*) $fieldLabelIdent)))
  let inst ← mod.declareInstanceLifting assumingClasses fieldLabelIdent ty instName (tactic := (← `(tactic| infer_instance_for_iterated_prod)))
  return #[inst]

/-- States that if every sort has an instance of `className` (e.g. `Ord node`),
then the domain has instances of that class.

[AutomaticallyInferred] NOTE: These typeclass instances can be automatically
inferred if `IteratedProd'`, `toDomain` and `toCodomain` are defined as
`abbrev`. We keep this code for explicitness, in case we want to change the
representation and typeclass inference will then fail. -/
private def Module.declareInstanceLiftingForDomain [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (deriveClass : Name) (assumingClasses : Array Name := #[deriveClass]) (instName : Option Name := .none) : m (Array Syntax) := do
  let (cls, sorts, fieldLabelIdent) := (mkIdent deriveClass, ← mod.sortIdents, mkVeilImplementationDetailIdent `f)
  let domainInst ← mod.declareInstanceLifting assumingClasses fieldLabelIdent (← `(term|$cls ($(mkIdent ``IteratedProd') (($(fieldLabelToDomain stateName) $sorts*) $fieldLabelIdent)))) instName
  return #[domainInst]
/-- States that if every sort has an instance of `className` (e.g. `Ord node`),
then the codomain has instances of that class. See NOTE [AutomaticallyInferred].-/
private def Module.declareInstanceLiftingForCodomain [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (deriveClass : Name) (assumingClasses : Array Name := #[deriveClass]) (instName : Option Name := .none) : m (Array Syntax) := do
  let (cls, sorts, fieldLabelIdent) := (mkIdent deriveClass, ← mod.sortIdents, mkVeilImplementationDetailIdent `f)
  let codomainInst ← mod.declareInstanceLifting assumingClasses fieldLabelIdent (← `(term|$cls (($(fieldLabelToCodomain stateName) $sorts*) $fieldLabelIdent))) instName
  return #[codomainInst]

/-- States that `deriveClass` can be inferred assuming `assumingClasses` for
every concrete type of every field. See NOTE [AutomaticallyInferred]. -/
private def Module.declareInstanceLiftingForConcreteType [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (deriveClass : Name) (assumingClasses : Array Name := #[deriveClass]) (instName : Option Name := .none) : m (Array Syntax) := do
  let (cls, sorts, fieldLabelIdent) := (mkIdent deriveClass, ← mod.sortIdents, mkVeilImplementationDetailIdent `f)
  let inst ← mod.declareInstanceLifting assumingClasses fieldLabelIdent (← `(term|$cls ($fieldConcreteDispatcher $sorts* $fieldLabelIdent))) instName
  return #[inst]

private def Module.mkFieldRepresentationInstances [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array Syntax) := do
  let (sorts, fieldLabelIdent) := (← mod.sortIdents, mkVeilImplementationDetailIdent `f)
  let fieldLabel ← `(bracketedBinder|($fieldLabelIdent:ident : $(mkIdent `State.Label)))
  let toDomainTerm ← `(($(fieldLabelToDomain stateName) $sorts* $fieldLabelIdent))
  let toCodomainTerm ← `(($(fieldLabelToCodomain stateName) $sorts* $fieldLabelIdent))
  let fieldConcreteTypeApplied ← `(($fieldConcreteDispatcher $sorts* $fieldLabelIdent))
  -- Field representation instance
  let fieldRepTy ← `(term|$(mkIdent ``FieldRepresentation) $toDomainTerm $toCodomainTerm $fieldConcreteTypeApplied)
  let fieldRepAssumed := #[``Enumeration, ``Ord, ``Std.TransCmp]
  let fieldRepBinders := (← mod.sortBinders) ++ (← fieldRepAssumed.flatMapM mod.assumeForEverySort) ++ #[fieldLabel]
  let fieldRepStx ← `(instance $instFieldRepresentation:ident $fieldRepBinders* : $fieldRepTy := by $(← mkSolverTactic ``instFinsetLikeAsFieldRep ``instTotalMapLikeAsFieldRep sorts fieldLabelIdent):tactic)
  -- Lawful field representation instance
  let lawfulFieldRepTy ← `(term|$(mkIdent ``LawfulFieldRepresentation) $toDomainTerm $toCodomainTerm $fieldConcreteTypeApplied ($instFieldRepresentation $sorts* $fieldLabelIdent))
  let lawfulAssumed := #[``Enumeration, ``Ord, ``Std.TransCmp, ``Std.LawfulEqCmp]
  let lawfulFieldRepBinders := (← mod.sortBinders) ++ (← lawfulAssumed.flatMapM mod.assumeForEverySort) ++ #[fieldLabel]
  let lawfulFieldRepStx ← `(instance $instLawfulFieldRepresentation:ident $lawfulFieldRepBinders* : $lawfulFieldRepTy := by $(← mkSolverTactic ``instFinsetLikeLawfulFieldRep ``instTotalMapLikeLawfulFieldRep sorts fieldLabelIdent):tactic)
  return #[fieldRepStx, lawfulFieldRepStx]
  where
  mkSolverTactic (relT funT : Name) (sorts : Array Ident) (fieldLabelIdent : Ident) : m (TSyntax `tactic) :=
    `(tactic|cases $fieldLabelIdent:ident <;>
    first
    | infer_instance_for_iterated_prod'
    | (exact $(mkIdent relT) $(mkIdent ``Veil.IteratedProd'.equiv) (($instEnumerationForIteratedProd $sorts*) _))
    | (exact $(mkIdent funT) $(mkIdent ``Veil.IteratedProd'.equiv) (($instEnumerationForIteratedProd $sorts*) _)))

/-- Return the syntax for declaring `State.Label` and dispatchers; also
update the module to include the new parameters for concrete field type,
`FieldRepresentation` and `LawfulFieldRepresentation`. -/
def Module.declareStateFieldLabelTypeAndDispatchers [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Module × Array Syntax) := do
  let components := mod.mutableComponents
  let fieldMetadata ← analyzeTypesOfStateComponents components
  -- this might be useful later, so store it as metadata in the module
  let argTypesAsMap : Std.HashMap Name (Array Term) := Std.HashMap.ofList (components.zipWith (fun sc args => (sc.name, args)) (fieldMetadata.map (·.domainTerms)) |>.toList)
  -- declare field label type
  let (name0, stx0) ← declareStructureFieldLabelType stateName components
  -- declare field dispatchers
  let (dispatchers, (fieldConcreteTypeName, fieldConcreteTypeStx)) ← mod.declareFieldDispatchers stateName fieldMetadata (← mod.sortBinders)
  let (dispacherNames, dispatcherStxs) := Array.unzip dispatchers
  for name in (#[name0, fieldConcreteTypeName] ++ dispacherNames) do
    mod.throwIfAlreadyDeclared name
  -- declare liftings for needed instances
  -- FIXME: this specific instance is really required; the rest can be automatically inferred (see NOTE [AutomaticallyInferred])
  let specificInstances ← #[``Enumeration].flatMapM fun inst => return (← mod.declareInstanceLiftingForIteratedProd inst (instName := instEnumerationForIteratedProdName))
  -- NOTE: not actually needed, but left here for completeness to document what needs to exist
  -- let instances ← #[``Enumeration, ``Ord, ``ToJson].flatMapM fun inst => return (← mod.declareInstanceLiftingForDomain inst) ++ (← mod.declareInstanceLiftingForCodomain inst)
  let instances : Array Syntax := #[]
  let concreteInstances ← #[(``Hashable, #[``DecidableEq, ``Ord, ``Hashable]), (``BEq, #[``DecidableEq, ``Ord]), (``ToJson, #[``ToJson, ``Ord]), (``Repr, #[``Repr, ``Ord])].flatMapM fun (deriveClass, assumingClasses) => mod.declareInstanceLiftingForConcreteType deriveClass assumingClasses
  -- add the `fieldConcreteType` parameter
  let fieldConcreteTypeParam ← Parameter.fieldConcreteType
  -- add the `FieldRepresentation` and `LawfulFieldRepresentation` typeclass parameters
  let f := mkVeilImplementationDetailIdent `f
  let paramsArgs ← mod.sortIdents
  let toDomainTerm ← `(($(fieldLabelToDomain stateName) $paramsArgs* $f))
  let toCodomainTerm ← `(($(fieldLabelToCodomain stateName) $paramsArgs* $f))
  let fieldConcreteTypeApplied ← `(($fieldConcreteType $f))
  let fieldRepType ← `(∀ $f, $(mkIdent ``FieldRepresentation) $toDomainTerm $toCodomainTerm $fieldConcreteTypeApplied)
  let fieldRep : Parameter := { kind := .moduleTypeclass .fieldRepresentation, name := fieldRepresentationName, «type» := fieldRepType, userSyntax := .missing }
  let lawfulFieldRepType ← `(∀ $f, $(mkIdent ``LawfulFieldRepresentation) $toDomainTerm $toCodomainTerm $fieldConcreteTypeApplied ($fieldRepresentation $f))
  let lawfulFieldRep : Parameter := { kind := .moduleTypeclass .lawfulFieldRepresentation, name := lawfulFieldRepresentationName, «type» := lawfulFieldRepType, userSyntax := .missing }
  return ({ mod with parameters := mod.parameters ++ #[fieldConcreteTypeParam, fieldRep, lawfulFieldRep] ,
                     _declarations := mod._declarations.insert fieldConcreteTypeParam.name .moduleParameter ,
                     _fieldRepMetaData := argTypesAsMap }, (#[stx0] ++ dispatcherStxs ++ specificInstances ++ instances ++ #[fieldConcreteTypeStx] ++ concreteInstances))

/-- Similar to `Module.declareStateStructure` but here `FieldRepresentation`
is involved. -/
def Module.declareFieldsAbstractedStateStructure [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Module × (Array Syntax)) := do
  mod.throwIfAlreadyDeclared environmentSubStateName
  let stateDefs ← mod.fieldsAbstractedStateDefinitionStx
  let inhabitedInst ← mod.mkFieldRepresentationInstances
  let stateStx ← mod.stateStx (withFieldConcreteType? := true)
  let substate : Parameter := { kind := .moduleTypeclass .environmentState, name := environmentSubStateName, «type» := ← `($(mkIdent ``IsSubStateOf) $stateStx $environmentState), userSyntax := .missing }
  return ({ mod with parameters := mod.parameters.push substate, _declarations := mod._declarations.insert environmentSubStateName .moduleParameter }, stateDefs ++ inhabitedInst)

def Module.declareTheoryStructure [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Module × Array Syntax) := do
  mod.throwIfAlreadyDeclared environmentSubTheoryName
  let stxs ← mod.theoryDefinitionStx
  let theoryStx ← mod.theoryStx
  let subtheory : Parameter := { kind := .moduleTypeclass .backgroundTheory, name := environmentSubTheoryName, «type» := ← `($(mkIdent ``IsSubReaderOf) $theoryStx $environmentTheory), userSyntax := .missing }
  return ({ mod with parameters := mod.parameters.push subtheory, _declarations := mod._declarations.insert environmentSubTheoryName .moduleParameter }, stxs)

def _root_.Lean.TSyntax.getPropertyName (stx : TSyntax `propertyName) : Name :=
  match stx with
  | `(propertyName| [$id]) => id.getId
  | _ => unreachable!

def Module.mkAssertion [Monad m] (mod : Module) (kind : StateAssertionKind) (name : Option (TSyntax `propertyName)) (prop : Term) (stx : Syntax) : m StateAssertion := do
  let name := nameForAssertion mod kind name
  let defaultSets := Std.HashSet.emptyWithCapacity.insert mod.defaultAssertionSet
  return { kind := kind, name := name, extraParams := #[], term := prop, userSyntax := stx, inSets := defaultSets }
where
  nameForAssertion (mod : Module) (kind : StateAssertionKind) (name : Option (TSyntax `propertyName)) : Name :=
    match name with
    | some name => name.getPropertyName
    | none =>
      let sz := (mod.assertions.filter (·.kind == kind)).size
      Name.mkSimple $ match kind with
      | .safety => s!"safety_{sz}"
      | .invariant => s!"inv_{sz}"
      | .assumption => s!"assumption_{sz}"
      | .trustedInvariant => s!"trusted_inv_{sz}"
      | .termination => s!"termination_{sz}"

private def Module.registerAssertion [Monad m] [MonadError m] (mod : Module) (sc : StateAssertion) : m Module := do
  mod.throwIfAlreadyDeclared sc.name
  let mut mod := { mod with assertions := mod.assertions.push sc, _declarations := mod._declarations.insert sc.name sc.declarationKind }
  for set in sc.inSets do
    let currentAssertions := mod._assertionSets.getD set Std.HashSet.emptyWithCapacity
    mod := { mod with _assertionSets := mod._assertionSets.insert set (currentAssertions.insert sc.name) }
  return mod

section AssertionElab

syntax (name := veil_exact_theory) "veil_exact_theory" : tactic
syntax (name := veil_exact_state) "veil_exact_state" : tactic

open Tactic in
/-- Reconstruct a `Theory` term from the hypotheses in the context. -/
def elabExactTheory : TacticM Unit := do
  let mod ← getCurrentModule
  let comp := mod.immutableComponents.map (Lean.mkIdent ·.name)
  let constr <- `(term| (⟨$[$comp],*⟩ : $(← mod.theoryStx)))
  trace[veil.debug] "theory constr: {constr}"
  Tactic.evalTactic $ ← `(tactic| exact $constr)

open Tactic in
def elabExactState : TacticM Unit := withMainContext do
  let mod ← getCurrentModule
  let comp := mod.mutableComponents.map (·.name)
  -- find all available state components in the local context
  let lctx ← getLCtx
  let some ldecls := comp.mapM (m := Option) lctx.findFromUserName?
    | throwError "not all state components are available in the local context"
  let actualFields : Array Term ← if mod._useFieldRepTC
    then
      -- find the concrete field from the _values_ of `ldecls`
      -- here, only use some simple heuristics to do the matching
      ldecls.mapM fun ldecl => do
        let some v := ldecl.value? true
          | throwError "state component {ldecl.userName} has no value in the local context"
        let v := match_expr v with
          | id _ vv => vv | _ => v
        match_expr v with
        | Veil.FieldRepresentation.get _ _ _ _ cf =>
          if let .fvar fv := cf
          then let nm ← fv.getUserName ; `(term| $(mkIdent nm) )
          else delabVeilExpr cf
        | _ => throwError "unable to extract concrete field from state component {ldecl.userName}"
    else
      ldecls.mapM fun a => `(term| $(mkIdent a.userName) )
  -- NOTE: It is very weird that if not doing it using `exact`
  -- (e.g., instead constructing the state `Expr` and using
  -- `closeMainGoalUsing`), then some meta-variable (e.g.,
  -- `IsSubStateOf` arguments) synthesis will fail.
  let constr ← `(term| (⟨$[$actualFields],*⟩ : $(← mod.stateStx mod._useFieldRepTC)))
  trace[veil.debug] "state constr: {constr}"
  Tactic.evalTactic $ ← `(tactic| exact $constr)

elab_rules : tactic
  | `(tactic| veil_exact_theory) => elabExactTheory
  | `(tactic| veil_exact_state) => elabExactState

inductive TheoryAndStateTermTemplateArgKind where
  | theory
  /-- When the concrete field representation is not used,
  `suffix` is the suffix to append to each field after
  destructing a state.

  When the concrete field representation is used,
  `suffixConc` is the suffix to append to each field after
  destructing a state, and `suffix` is the suffix appended to
  each field's _original name_ (i.e., not the one after appending
  `suffixConc`) after applying `FieldRepresentation.get` to
  the concrete field.

  When either is `none`, no suffix is appended in the corresponding case. -/
  | state (suffix suffixConc : Option String)

/-- Given `t : Prop` which accesses fields of theory and/or state,
returns the proper "wrapper" term which pattern-matches over theory
and/or and state, thus making all their fields accessible in `t`.
`t` can depend on the field names of theory and state. The pattern-matches
are generated according to `targets`. -/
def Module.withTheoryAndStateTermTemplate (mod : Module) (targets : List (TheoryAndStateTermTemplateArgKind × Ident))
  (t : Array Ident /- field names of theory -/ →
       Array Ident /- field names of state -/ →
       MetaM (TSyntax `term))
  : MetaM (TSyntax `term) := do
  let motive := mkIdent `motive
  let (theoryName, stateName) := (mod.name ++ theoryName, mod.name ++ stateName)
  let casesOnTheory := theoryName ++ `casesOn
  let casesOnState := stateName ++ `casesOn
  let theoryFields ← getFieldIdentsForStruct theoryName
  let stateFields ← getFieldIdentsForStruct stateName
  let stateFieldsWithSuffix suf : Array Ident :=
    stateFields.map fun (f : Ident) => f.getId.appendAfter suf |> Lean.mkIdent
  let t ← t theoryFields stateFields
  targets.foldrM (init := t) fun (kind, i) body => do
    match kind with
    | .theory =>
      let tmp ← mkFunSyntax theoryFields body
      `(term|
        @$(mkIdent casesOnTheory) $(← mod.sortIdents)*
        ($motive := fun _ => Prop)
        ($(mkIdent ``readFrom) $i)
        ($tmp))
    | .state suffix suffixConc =>
      let sfs := suffix.elim stateFields stateFieldsWithSuffix
      let sfsConc := suffixConc.elim stateFields stateFieldsWithSuffix
      let body' ← if !mod._useFieldRepTC then pure body else
        -- annotate types here, otherwise there can be issues like: for `f a`
        -- where `f` has a complicated type but definitionally equal to `node → Bool`,
        -- coercions will not be inserted to make `f a` into `Prop`
        -- (notice that `decide` expects a `Prop` argument here)
        let fieldTypes ← mod.mutableComponents.mapM (·.typeStx)
        let bundled := sfs.zip fieldTypes |>.zip sfsConc
        bundled.foldrM (init := body) fun ((f, ty), fConc) b => do
          `(let $f:ident : $ty := ($fieldRepresentation _).$(mkIdent `get) $fConc:ident ; $b)
      let tmp ← mkFunSyntax (if !mod._useFieldRepTC then sfs else sfsConc) body'
      `(term|
        @$(mkIdent casesOnState) $(← mod.sortIdentsForTheoryOrState mod._useFieldRepTC)*
        ($motive := fun _ => Prop)
        ($(mkIdent ``getFrom) $i)
        ($tmp))

/-- This is used wherever we want to define a predicate over the
background theory (e.g. in `assumption` definitions). Instead of
writing `fun th => Pred`, this will pattern-match over the theory and
make all its fields accessible for `Pred`. -/
def withTheory (t : Term) :  MetaM (Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Term) := do
  let mut mod ← getCurrentModule
  let th := mkIdent `th
  let fn ← do
    let tmp ← mod.withTheoryAndStateTermTemplate [(.theory, th)] (fun _ _ => pure t)
    `(term| (fun ($th : $environmentTheory) => $tmp))
  -- See NOTE(SUBTLE) to see why this is not actually ill-typed.
  let binders := #[← `(bracketedBinder| ($th : $environmentTheory := by veil_exact_theory))]
  return (binders, ← `(term|$fn $th))

/-- This is used wherever we want to define a predicate over the
background theory and the mutable state (e.g. in `invariant`
definitions). Instead of writing `fun th st => Pred`, this will
pattern-match over the theory and state and make all their fields
accessible for `Pred`. This was previously called `funcasesM`. -/
def withTheoryAndState (t : Term) : MetaM (Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Term) := do
  let mut mod ← getCurrentModule
  let (th, st) := (mkIdent `th, mkIdent `st)
  let fn ← do
    let tmp ← mod.withTheoryAndStateTermTemplate [(.theory, th), (.state .none "_conc", st)] (fun _ _ => pure t)
    `(term| (fun ($th : $environmentTheory) ($st : $environmentState) => $tmp))
  -- NOTE(SUBTLE): `by veil_exact_theory` and `by veil_exact_state` work in a
  -- counter-intuitive way when applied to assertions. Concretely, these tactics
  -- always construct a term of type `Theory` and `State` respectively (rather
  -- than `ρ` or `σ` — the generic types). In other words, `$th :
  -- $environmentTheory := by veil_exact_theory` is ILL TYPED. However, since in
  -- `defineAssertion` we make the `ρ` and `σ` arguments _implicit_, and these
  -- binders are _explicit_ (and thus evaluated first), `by veil_exact_theory`
  -- effectively "forces" the `ρ` and `σ` arguments to be instantiated with the
  -- _concrete_ `Theory` and `State`. Basically, whenever these default arguments
  -- are evaluated (i.e. not provided explicitly), the assertion is forced to be
  -- evaluated with `ρ := Theory` and `σ := State`.
  let binders := #[← `(bracketedBinder| ($th : $environmentTheory := by veil_exact_theory)), ← `(bracketedBinder| ($st : $environmentState := by veil_exact_state))]
  return (binders, ← `(term|$fn $th $st))

/-- Implicitly quantifies capital variables and elaborates the term with all
state and theory variables bound (or just theory if `justTheory` is true). -/
private def Module.mkVeilTerm (mod : Module) (name : Name) (dk : DeclarationKind) (params : Option (TSyntax `Lean.explicitBinders)) (term : Term) (justTheory : Bool := false) : TermElabM (Array Parameter × Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Term × Term) := do
  let baseParams ← mod.declarationBaseParams dk
  let binders ← baseParams.mapM (·.binder)
  let paramBinders ← Option.stxArrMapM params toBracketedBinderArray
  -- We don't `universallyQuantifyCapitals` after `withTheory` /
  -- `withTheoryAndState` because we want to have the universal
  -- quantification as deeply inside the term as possible, rather than above
  -- the binders for `rd` and `st` introduced below.
  let body ← `(uqc% ($term:term))
  let (thstBinders, term') ← if justTheory then withTheory body else withTheoryAndState body
  let term' := Syntax.inheritSourceSpanFrom term' term
  -- Record the `Decidable` instances that are needed for the assertion.
  let (insts, _) ← elabBinders (binders ++ paramBinders ++ thstBinders) $ fun _ => getRequiredDecidableInstances term'
  trace[veil.debug] "insts: {insts.map (·.1)}"
  let extraParams : Array Parameter := insts.mapIdx (fun i (decT, _) => { kind := .definitionParameter name .typeclass, name := Name.mkSimple s!"{name}_dec_{i}", «type» := decT, userSyntax := .missing })
  return (extraParams, thstBinders, term', body)

end AssertionElab

/-- Declare the `LocalRProp` typeclass for the module.
Its general form is:
```lean
class LocalRPropTC /- module parameters -/ {α : Type} (post : RProp α ρ σ)
where
  core : α →
    /- types of fields of `Theory`, connected with `→` -/ →
    /- types of _canonical_ fields of `State`, connected with `→` -/ → Prop
  core_eq : ∀ (a : α) (th : ρ) (st : σ),
    post a th st = core a /- fields of `Theory` -/ /- _canonical_ fields of `State` -/
```
-/
def Module.declareLocalRPropTC (mod : Module) : MetaM (Command × Command) := do
  -- this can be given fewer parameters, but for simplicity we give it all of them
  let params := mod.parameters
  let mut binders ← params.mapM (·.binder)
  -- build binders
  let α ← Lean.mkIdent <$> mkFreshUserName `α
  let post ← Lean.mkIdent <$> mkFreshUserName `post
  let core := mkIdent `core ; let core_eq := mkIdent `core_eq
  binders := binders.push (← `(bracketedBinder| {$α : Type} ))
  binders := binders.push (← `(bracketedBinder| ($post : $(mkIdent ``RProp) $α $environmentTheory $environmentState) ))
  -- build the type of `core`
  let coreType ← do
    let theoryFields ← mod.immutableComponents.mapM (·.getSimpleBinder >>= getSimpleBinderType)
    let stateFields ← mod.mutableComponents.mapM (·.getSimpleBinder >>= getSimpleBinderType)
    mkArrowStx (α :: (theoryFields ++ stateFields).toList) (← `(term| Prop ))
  -- build the type of `core_eq`
  let a ← Lean.mkIdent <$> mkFreshUserName `a
  let th ← Lean.mkIdent <$> mkFreshUserName `th
  let st ← Lean.mkIdent <$> mkFreshUserName `st
  let coreEqType ← do
    let body ← mod.withTheoryAndStateTermTemplate [(.theory, th), (.state .none "_conc", st)] fun theoryFieldNames stateFieldNames =>
      pure <| Syntax.mkApp core (#[a] ++ theoryFieldNames ++ stateFieldNames)
    `(term| ∀ ($a : $α) ($th : $environmentTheory) ($st : $environmentState),
    $post $a $th $st = $body)
  let cmd1 ← `(command| class $localRPropTC $[$binders]* where
      $core:ident : $coreType
      $core_eq:ident : $coreEqType)
  let cmd2 ← `(command| attribute [$(mkIdent `wpSimp):ident] $(mkIdent <| localRPropTCName ++ `core):ident)
  return (cmd1, cmd2)

open Meta in
/-- This `dsimproc` attempts to replace assertions that have associated
`LocalRProp` instances with their `core` definitions. -/
dsimproc_decl replaceLocalRProp (_) := fun e => do
  let f := e.getAppFn'
  let args := e.getAppArgs'
  unless f.isConst && args.size ≥ 4 do return .continue
  -- search for the `LocalRProp` instance of `nm`
  -- NOTE: The following code relies on some hacks
  try
    let targetInstType ← do
      let targetInstName ← resolveGlobalConstNoOverloadCore localRPropTCName
      let targetInstInfo ← getConstInfo targetInstName
      let mut argsMore := args.take (targetInstInfo.type.getForallArity - 2)    -- the 2 is also a magic number here
      argsMore := argsMore.push (mkConst ``Unit)
      let self ← do
        let ρ := args[0]! ; let σ := args[1]!
        -- remove the arguments representing theory and state from `args`,
        -- by a heuristic
        let args' := args.reverse
        let some thPos ← args'.findIdxM? fun a => do isDefEq (← inferType a) ρ
          | return .continue
        let thPos := args.size - 1 - thPos
        let some stPos ← args'.findIdxM? fun a => do isDefEq (← inferType a) σ
          | return .continue
        let stPos := args.size - 1 - stPos
        -- a special check: see the comment below
        if thPos == args.size - 2 && stPos == args.size - 1 then
          pure <| mkAppN f (args.pop.pop)
        else
          let thName ← mkFreshUserName `th ; let stName ← mkFreshUserName `st
          withLocalDeclsDND #[(thName, ρ.consumeMData), (stName, σ.consumeMData)] fun ldecls => do
            let argsAbstracted := args.set! thPos ldecls[0]! |>.set! stPos ldecls[1]!
            mkLambdaFVars ldecls <| mkAppN f argsAbstracted
      argsMore := argsMore.push (← mkFunUnit self)
      mkAppOptM targetInstName (argsMore.map Option.some)
    let e ← synthInstance targetInstType
    let coreFn ← Meta.mkProjection e `core
    let coreApp ← do
      -- relying on `mod` to find the field variables by their
      -- "canonical names" in the local context
      let lctx ← getLCtx
      let mod ← getCurrentModule
      let scs := mod.immutableComponents ++ mod.mutableComponents
      let fieldVars ← scs.mapM fun sc => do
        let nm := sc.name
        let some ldecl := lctx.findFromUserName? nm
          | throwError "unable to find theory field {nm} in the local context"
        pure ldecl.toExpr
      pure <| mkAppN coreFn (#[Lean.mkConst (``Unit.unit)] ++ fieldVars)
    return .done coreApp
  catch _ =>
    return .continue

open Meta in
/-- Construct a `LocalRProp` term for the given state predicate `nm`,
including assertions and ghost relations. This is done at the level of
`Expr` to avoid uncertainty introduced by, for example, the use of
`veil_exact_state` tactics. Also, this should provide more useful
error message.

This function returns the instance. Its error message shall be handled
by the caller. -/
def Module.proveLocalityForStatePredicateCore (mod : Module) (nm : Name) : MetaM Expr := do
  let nmFull ← resolveGlobalConstNoOverloadCore nm
  let info ← getConstInfoDefn nmFull
  -- exploit the shape of `info.value`
  let inst ← lambdaTelescope info.value fun xs body => do
    let f := body.getAppFn'
    let [th, st] := body.getAppArgs'.toList
      | throwError "unexpected shape of state predicate {nm}: unable to extract theory and state arguments"
    let ρ ← inferType th
    let σ ← inferType st
    let f := f.instantiateLambdasOrApps #[th, st]
    -- `f` should be like `Theory.casesOn ...`
    let theoryCasesOnBody := f.getAppArgs'.back!
    lambdaTelescope theoryCasesOnBody fun theoryFields body => do
      -- `body` should be like `State.casesOn ...`
      let stateCasesOnBody := body.getAppArgs'.back!
      lambdaTelescope stateCasesOnBody fun stateFieldsConc body => do
        -- now, `body` should be the actual body of the predicate
        letBoundedTelescope body (.some <| if mod._useFieldRepTC then stateFieldsConc.size else 0) fun stateFields body => do
          let stateFieldsInUse := if mod._useFieldRepTC then stateFields else stateFieldsConc
          -- construct and simplify the `core`
          let core ← do
            /-
            let tmp ← mkLambdaFVars (theoryFields ++ stateFieldsInUse) body >>= mkFunUnit
            (Simp.dsimp #[``replaceLocalRProp]) tmp
            -/
            let tmp ← (Simp.dsimp #[``replaceLocalRProp]) body
            let res ← mkLambdaFVars (theoryFields ++ stateFieldsInUse) tmp.expr
            -- pure (← mkFunUnit res, ← tmp.getProof)
            mkFunUnit res
          trace[veil.debug] "core for LocalRProp instance of {nm}: {core}"
          -- the `core_eq` should have `proof` inside
          let coreEq ← do
            let a ← mkFreshUserName `a ; let thName ← mkFreshUserName `th ; let stName ← mkFreshUserName `st
            withLocalDeclsDND #[(a, (mkConst ``Unit)), (thName, ρ.consumeMData), (stName, σ.consumeMData)] fun ldecls => do
              let xs' := xs.replace th ldecls[1]! |>.replace st ldecls[2]!
              let self ← mkAppOptM nmFull (xs'.map Option.some)
              let eqrefl ← mkEqRefl self
              mkLambdaFVars ldecls eqrefl
          -- now, build the instance
          let targetInstName ← resolveGlobalConstNoOverloadCore localRPropTCName
          let some ctor := getStructureLikeCtor? (← getEnv) targetInstName
            | throwError "unexpected error: unable to find constructor for {localRPropTCName}"
          let ctorArgs ← do
            let targetInstInfo ← getConstInfo targetInstName
            let mut argsMore := xs.take (targetInstInfo.type.getForallArity - 2)    -- the 2 is also a magic number here
            argsMore := argsMore.push (mkConst ``Unit)
            -- `self` is the definition `nmFull` applied to all arguments except `th` and `st`,
            -- so do a special check: if `th` and `st` are at the tail position, then just pop them;
            -- otherwise use `mkLambdaFVars` to build it
            let self ← do
              let thPos := xs.idxOf th
              let stPos := xs.idxOf st
              if thPos == xs.size - 2 && stPos == xs.size - 1 then
                mkAppOptM nmFull (xs.pop.pop |>.map Option.some)
              else
                let tmp ← mkAppOptM nmFull (xs.map Option.some)
                mkLambdaFVars #[th, st] tmp
            argsMore := argsMore.push (← Meta.mkFunUnit self)
            pure argsMore
          let inst ← Meta.mkAppOptM ctor.name (ctorArgs |>.push core |>.push coreEq |>.map Option.some)
          mkLambdaFVars xs inst (usedOnly := true)
  check inst
  let inst ← instantiateMVars inst
  trace[veil.debug] "LocalRProp instance for {nm}: {inst}"
  return inst

/-- Prove locality for the state predicate `nm`, and register
the corresponding `LocalRProp` instance in the module. Any error
will be caught and logged as a warning. -/
def Module.proveLocalityForStatePredicate (mod : Module) (nm : Name) (stx : Syntax) : TermElabM Unit := do
  try
    let inst ← mod.proveLocalityForStatePredicateCore nm
    let attrs ← do
      let tmp ← `(Parser.Term.attrInstance| instance)
      elabAttrs (#[tmp])
    let _ ← addVeilDefinition (generateLocalRPropInstName nm) inst (attr := attrs)
  catch ex =>
    logWarningAt stx s!"unable to prove locality for state predicate {nm}: {← ex.toMessageData.toString}"
where
  generateLocalRPropInstName (nm : Name) : Name :=
    Name.mkSimple <| "instLocalRProp" ++ nm.capitalize.toString

/-- Register the assertion (and any optional `Decidable` instances)
in the module, and return the syntax to elaborate. -/
def Module.defineAssertion (mod : Module) (base : StateAssertion) : CommandElabM (Command × Module) := do
  mod.throwIfAlreadyDeclared base.name
  let mut mod := mod
  let justTheory := match base.kind with | .assumption => true | _ => false
  let (extraParams, thstBinders, term, _) ← liftTermElabM $ mod.mkVeilTerm base.name base.declarationKind (params := .none) base.term (justTheory := justTheory)
  mod ← mod.registerAssertion { base with extraParams := extraParams }
  -- This includes the required `Decidable` instances
  let (binders, _) ← mod.declarationAllParamsMapFn (·.binder) base.name base.declarationKind
  -- NOTE(SUBTLE): we do something counter-intuitive here. Making the `ρ` and `σ`
  -- arguments implicit ensures that whenever the default values for `thstBinders`
  -- are evaluated (i.e. not provided explicitly), the assertion is forced to be
  -- evaluated with `ρ := Theory` and `σ := State`. This makes it possible to do
  -- things like `assert invariant` in action without having to provide any
  -- explicit arguments.
  let preBinders ← binders.mapM mkImplicitBinder
  let binders := preBinders ++ thstBinders
  let attrs ← #[`invSimp].mapM (fun attr => `(attrInstance| $(Lean.mkIdent attr):ident))
  let stx ← `(@[$attrs,*] abbrev $(mkIdent base.name) $[$binders]* := $term)
  return (stx, mod)

def Module.registerDerivedDefinition [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (ddef : DerivedDefinition) : m Module := do
  mod.throwIfAlreadyDeclared ddef.name
  return { mod with _declarations := mod._declarations.insert ddef.name ddef.declarationKind, _derivedDefinitions := mod._derivedDefinitions.insert ddef.name ddef }

def Module.defineGhostRelation (mod : Module) (name : Name) (params : Option (TSyntax `Lean.explicitBinders)) (term : Term) (justTheory : Bool := false) : CommandElabM (Command × Module) := do
  mod.throwIfAlreadyDeclared name
  let kind? := .stateAssertion .invariant -- a ghost relation is a predicate that depends on the state
  let ddKind : DerivedDefinitionKind := if justTheory then .theoryGhost else .ghost
  let dk : DeclarationKind := .derivedDefinition ddKind (Std.HashSet.emptyWithCapacity 0)
  let (baseParams, _) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) dk
  let (extraParams, thstBinders, term, _) ← liftTermElabM $ mod.mkVeilTerm name kind? params term justTheory
  let params := (← explicitBindersToParameters params name) ++ (← thstBinders.mapM (bracketedBinderToParameter · name))
  let baseBinders ← (baseParams ).mapM (·.binder)
  -- FIXME: for the following line, we implicitly assume that this is the order in
  -- which binders get generated for the definition. We should instead first
  -- create a definition without `stx`, use the relevant functions to get the
  -- binders, and then create the syntax.
  -- See NOTE(SUBTLE).
  let binders := (← baseBinders.mapM mkImplicitBinder) ++ (← params.mapM (·.binder)) ++ (← extraParams.mapM (·.binder))
  let attrs ← #[(if justTheory then `invSimp else `ghostRelSimp)].mapM (fun attr => `(attrInstance| $(Lean.mkIdent attr):ident))
  let stx ← `(@[$attrs,*] abbrev $(mkIdent name) $[$binders]* := $term)
  trace[veil.debug] "stx: {stx}"
  let ddef : DerivedDefinition := { name := name, kind := ddKind, params := params, extraParams := extraParams, derivedFrom := Std.HashSet.emptyWithCapacity 0, stx := stx }
  let mod ← mod.registerDerivedDefinition ddef
  return (stx, mod)

private def Module.assembleAssertions [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (kind : DerivedDefinitionKind) (assembledName : Name) (specificBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (onlySafety : Bool := false) : m (Command × Module) := do
  mod.throwIfAlreadyDeclared assembledName
  let assertions ← match kind with
    | .assumptionLike => pure mod.assumptions
    | .invariantLike => pure (if onlySafety then mod.safeties else mod.invariants)
    | _ => throwError s!"[Module.assembleAssertions] invalid kind: {repr kind}"
  let conjunctsSet := Std.HashSet.ofArray $ assertions.map (·.name)
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition kind conjunctsSet)
  let specificArgs ← bracketedBindersToTerms specificBinders
  let apps ← assertions.mapM (fun a => do
    let (params, _) ← mod.declarationAllParams a.name a.declarationKind
    let args ← params.mapM (·.arg)
    `(term| @$(mkIdent a.name):ident $args* $specificArgs*))
  let body ← repeatedAnd apps
  let binders ← (baseParams ++ extraParams).mapM (·.binder)
  -- The `reducible` is needed such that we can apply lemmas like
  -- `triple_strengthen_postcondition` without unfolding the definition of
  -- `Invariants`. Note that for this to work, the definition must return
  -- `Prop` rather than `Bool`. TODO: a Bool-specific weakening?
  let attrs ← #[`derivedInvSimp, `invSimp, `reducible].mapM (fun attr => `(attrInstance| $(Lean.mkIdent attr):ident))
  let cmd ← `(command|@[$attrs,*] def $(mkIdent assembledName) $[$(binders)]* $specificBinders* : Prop := $body)
  let derivedDef : DerivedDefinition := { name := assembledName, kind := kind, params := #[], extraParams := extraParams, derivedFrom := conjunctsSet, stx := cmd }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (cmd, mod)

/-- Syntax for the conjunction of all `invariant`, `safety`, and
`trusted invariant` clauses. This modifies the `Module` to record which
parameters are necessary for this definition. -/
def Module.assembleInvariants [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Command × Module) := do
  let binders := #[← `(bracketedBinder| ($(mkIdent `rd) : $environmentTheory)), ← `(bracketedBinder| ($(mkIdent `st) : $environmentState))]
  mod.assembleAssertions .invariantLike assembledInvariantsName binders

def Module.assembleAssumptions [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Command × Module) := do
  let binders := #[← `(bracketedBinder| ($(mkIdent `rd) : $environmentTheory))]
  mod.assembleAssertions .assumptionLike assembledAssumptionsName binders

def Module.assembleSafeties [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Command × Module) := do
  let binders := #[← `(bracketedBinder| ($(mkIdent `rd) : $environmentTheory)), ← `(bracketedBinder| ($(mkIdent `st) : $environmentState))]
  mod.assembleAssertions .invariantLike assembledSafetiesName binders (onlySafety := true)

def Module.labelTypeStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Term := do
  `(term|$labelType $(← mod.sortIdents)*)

private def Module.assembleLabelDef [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Command × Module) := do
  mod.throwIfAlreadyDeclared labelTypeName
  let labelT ← mod.labelTypeStx
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let ctors ← mod.actions.mapM (fun a => do
    `(Command.ctor| | $(mkIdent a.name):ident $(← a.binders)* : $labelT ))
  let labelDef ← do
    let instances := #[``DecidableEq,``Repr, ``ToJson].map Lean.mkIdent
    if ctors.isEmpty then
      `(inductive $labelType $(← mod.sortBinders)* where $[$ctors]* deriving $[$instances:ident],*)
    else
      let instances := instances ++ #[``Inhabited, ``Nonempty].map Lean.mkIdent
      `(inductive $labelType $(← mod.sortBinders)* where $[$ctors]* deriving $[$instances:ident],*)
  let derivedDef : DerivedDefinition := { name := labelTypeName, kind := .stateLike, params := #[], extraParams := #[], derivedFrom := actionNames, stx := labelDef }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (labelDef, mod)

private def Module.assembleLabelCasesLemma [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Command × Module) := do
  mod.throwIfAlreadyDeclared labelCasesName
  let P := mkIdent `P
  let labelT ← mod.labelTypeStx
  let exs ← mod.actions.mapM (fun a => do
    let constructor := Lean.mkIdent $ labelTypeName ++ a.name
    match a.params with
    | #[] => `(term| $P ($constructor))
    | params =>
      let br ← parametersToExplicitBinders params
      `(term| (∃ $br, $P ($constructor $(← explicitBindersToTerms br)*))))
  let label := mkIdent `label
  let casesLemma ← `(command|set_option linter.unusedSectionVars false in
    theorem $labelCases ($P : $labelT -> Prop) :
      (∃ $label:ident : $labelT, $P $label) ↔
      $(← repeatedOr exs) :=
    by
      constructor
      { rintro ⟨$(mkIdent `l), $(mkIdent `r)⟩; rcases $(mkIdent `l):ident <;> aesop }
      { aesop })
  let derivedDef : DerivedDefinition := { name := labelCasesName, kind := .stateLike, params := #[], extraParams := #[], derivedFrom := {labelTypeName}, stx := casesLemma }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (casesLemma, mod)

def Module.mkLabelEnumeration [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Command := do
  let binders := (← mod.sortBinders) ++ (← #[``DecidableEq, ``FinEnum].flatMapM mod.assumeForEverySort)
  let labelT ← mod.labelTypeStx
  `(instance $[$binders]* : $(mkIdent ``Veil.Enumeration) ($labelT) where
    $(mkIdent `allValues):ident := ($(mkIdent ``FinEnum.ofEquiv) _ ($(mkIdent ``Equiv.symm) (proxy_equiv% ($labelT)))).toList
    $(mkIdent `complete):ident := by simp)

def Module.mkInstantiationStructure [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Command := do
  let sortParams := mod.sortParams
  let fields ← sortParams.mapM fun (param, sortKind) => do
    let sort ← param.ident
    match sortKind with
    | .enumSort =>
      -- Enum type: add default value of SortName_IndT
      let defaultType := Ident.toEnumConcreteType sort
      `(Command.structSimpleBinder| $sort:ident : Type := $defaultType)
    | .uninterpretedSort =>
      -- Regular sort: no default
      `(Command.structSimpleBinder| $sort:ident : Type)
  let instances := #[``Inhabited, ``Repr].map Lean.mkIdent
  `(structure $instantiationType where $[$fields]* deriving $[$instances:ident],*)

def Module.assembleLabel [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array Command × Module) := do
  let (labelDef, mod) ← mod.assembleLabelDef
  let (casesLemma, mod) ← mod.assembleLabelCasesLemma
  let labelEnumeration ← mod.mkLabelEnumeration
  return (#[labelDef, casesLemma, labelEnumeration], mod)

def Module.assembleNext [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] (mod : Module) : m (Command × Module) := do
  mod.throwIfAlreadyDeclared assembledNextActName
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .actionLike actionNames)
  let binders ← (baseParams ++ extraParams).mapM (·.binder)
  let acts ← mod.actions.mapM (fun s => do
    let name := Lean.mkIdent $ toExtName s.name
    let (params, _) ← mod.declarationAllParams s.name s.declarationKind
    let args ← params.mapM (·.arg)
    `(@$name $args*))
  let labelT ← mod.labelTypeStx
  let nextT ← `(term|$labelT → $(mkIdent ``VeilM) $(mkIdent ``Mode.external) $environmentTheory $environmentState $(mkIdent ``Unit))
  let label := mkIdent `label
  let casesOn := mkIdent $ Name.append label.getId `casesOn
  let nextDef ← `(command|def $assembledNextAct $[$(binders)]* : $nextT := fun ($label : $labelT) => $casesOn $acts*)
  let nextParam := { kind := .definitionParameter assembledNextActName .explicit, name := label.getId, «type» := labelT, userSyntax := .missing }
  let derivedDef : DerivedDefinition := { name := assembledNextActName, kind := .actionLike, params := #[nextParam], extraParams := extraParams, derivedFrom := actionNames, stx := nextDef }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (nextDef, mod)



end Veil
