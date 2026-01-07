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

/-! ## Type Instances & Basic Conversions -/

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

/-! ## Procedure Info Utilities -/

def initializerName : Name := `initializer

def ProcedureInfo.isAction (kind : ProcedureInfo) : Bool :=
  match kind with
  | .action _ (definedViaTransition := false) => true
  | _ => false

def ProcedureInfo.isTransition (pi : ProcedureInfo) : Bool :=
  match pi with
  | .action _ true => true
  | _ => false

def ProcedureInfo.name : ProcedureInfo → Name
  | .action name _ => name
  | .procedure name => name
  | .initializer => initializerName

def ProcedureSpecification.name (a : ProcedureSpecification) : Name := a.info.name

/-! ## Parameter Constructors & Queries -/

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

/-! ## Module State Management -/

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

def Module.isSpecFinalized (mod : Module) : Bool := mod._specFinalizedAt.isSome

def Module.specFinalizedAtStx (mod : Module) : Option Syntax := mod._specFinalizedAt

def Module.throwIfStateAlreadyDefined [Monad m] [MonadError m] (mod : Module) : m Unit := do
  if mod.isStateDefined then
    throwError s!"The state of module {mod.name} has already been defined. It can no longer be changed!"

def Module.throwIfSpecAlreadyFinalized [Monad m] [MonadError m] (mod : Module) : m Unit := do
  if mod.isSpecFinalized then
    throwError s!"The specification of module {mod.name} has already been finalized. You can no longer add procedures or assertions!"

def Module.throwIfSpecNotFinalized [Monad m] [MonadError m] (mod : Module) : m Unit := do
  if !mod.isSpecFinalized then
    throwError s!"The specification of module {mod.name} has not been finalized. Please call #gen_spec first!"

/-! ## Parameter Conversion (Binders & Args) -/

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

/-! ## Binder/Parameter Conversions -/

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

/-! ## Declaration Parameter Queries -/

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

/-! ## Sort Parameter Utilities -/

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

/-! ## Assertion & Procedure Filters -/

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

/-! ## Field Utilities -/

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
      let .some _sc := curMod.signature.find? (·.name == scName)
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

/-! ## Syntax Generation -/

def Module.stateStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (withFieldConcreteType? : Bool := false) : m Term :=
  return ← `(term| @$(mkIdent stateName) $(← mod.sortIdentsForTheoryOrState withFieldConcreteType?)*)

def Module.theoryStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Term :=
  return ← `(term| @$(mkIdent theoryName) $(← mod.sortIdents)*)

end Veil
