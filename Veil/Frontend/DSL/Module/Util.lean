import Lean
import Veil.Frontend.DSL.Module.Names
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Syntax
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Infra.State
import Veil.Frontend.DSL.Infra.GenericInterface
import Veil.Frontend.DSL.Util
import Veil.Util.Meta

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

def ProcedureSpecification.binders [Monad m] [MonadQuotation m] [MonadError m] (a : ProcedureSpecification) : m (TSyntaxArray ``Lean.Parser.Term.bracketedBinder) :=
  Option.stxArrMapM a.params toBracketedBinderArray

def DerivedDefinition.binders [Monad m] [MonadQuotation m] [MonadError m] (dd : DerivedDefinition) : m (TSyntaxArray ``Lean.Parser.Term.bracketedBinder) :=
  Option.stxArrMapM dd.params toBracketedBinderArray

def Parameter.environmentTheory [Monad m] [MonadQuotation m] : m Parameter :=
  return { kind := .backgroundTheory, name := environmentTheoryName, «type» := ← `(Type), userSyntax := .missing }

def Parameter.environmentState [Monad m] [MonadQuotation m] : m Parameter :=
  return { kind := .environmentState, name := environmentStateName, «type» := ← `(Type), userSyntax := .missing }

def Parameter.mode [Monad m] [MonadQuotation m] : m Parameter :=
  return { kind := .mode, name := veilModeVar.getId, «type» := mkIdent ``Mode, userSyntax := .missing }

def Parameter.fieldConcreteType [Monad m] [MonadQuotation m] : m Parameter :=
  return { kind := .fieldConcreteType, name := fieldConcreteTypeName, «type» := ← `($(structureFieldLabelType stateName) → Type), userSyntax := .missing }

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
  | .moduleTypeclass _ | .definitionTypeclass _ =>
  if p.name != Name.anonymous then
    `(bracketedBinder|[$(mkIdent p.name) : $(p.type)])
  else
    `(bracketedBinder|[$(p.type)])
  | _ => `(bracketedBinder|($(mkIdent p.name) : $(p.type)))

/-- Convert a `Parameter` to a `Term` syntax for the equivalent
argument. Unnamed typeclass instances are left for typeclass inference
(i.e. `_`). -/
def Parameter.arg [Monad m] [MonadQuotation m] (p : Parameter) : m Term := do
  match p.kind with
  | .moduleTypeclass _ | .definitionTypeclass _ =>
    if p.name != Name.anonymous then
      `(term| $(mkIdent p.name))
    else
      `(term| _)
  | _ => `(term| $(mkIdent p.name))

def Parameter.ident [Monad m] [MonadQuotation m] (p : Parameter) : m Ident := return mkIdent p.name

def Module.declarationBaseParams [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (k : DeclarationKind) : m (Array Parameter) := do
  match k with
  | .moduleParameter => throwError "[Module.declarationBaseParams]: moduleParameter has no base parameters"
  | .stateComponent _ _ => sortParameters mod
  | .stateAssertion .assumption => pure (theoryParameters mod)
  | .stateAssertion .invariant | .stateAssertion .safety | .stateAssertion .trustedInvariant => pure mod.parameters
  | .procedure _ => pure mod.parameters
  | .derivedDefinition k _ => derivedDefinitionBaseParams mod k
where
  sortFilterMapFn {α : Type} (mod : Module) (f : Parameter → m α) : m (Array α) := do
    mod.parameters.filterMapM fun p => do match p.kind with
    | .uninterpretedSort => f p
    | _ => pure .none
  sortParameters (mod : Module) : m (Array Parameter) := do
    sortFilterMapFn mod (pure ·)
  theoryParameters (mod : Module) : Array Parameter :=
    mod.parameters.filterMap fun p => match p.kind with
    | .environmentState | .moduleTypeclass .environmentState => .none
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
def Module.declarationSplitParams [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (forDeclaration : Name) (k : DeclarationKind) : m (Array Parameter × Array Parameter × Option (TSyntax `Lean.explicitBinders)) := do
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
        pure (sa.extraParams, .none)
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
def Module.declarationAllParams [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (forDeclaration : Name) (k : DeclarationKind) : m (Array Parameter × Option (TSyntax `Lean.explicitBinders)) := do
  let (baseParams, extraParams, actualParams) ← mod.declarationSplitParams forDeclaration k
  return (baseParams ++ extraParams, actualParams)

def Module.declarationAllParamsMapFn [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (f : Parameter → m α) (forDeclaration : Name) (k : DeclarationKind) : m (Array α × Option (TSyntax `Lean.explicitBinders)) := do
  let (allModParams, actualParams) ← mod.declarationAllParams forDeclaration k
  return (← allModParams.mapM f, actualParams)

/-- Utility function to get the binders and arguments for a declaration, split
between those imposed by the module and those the declaration "actually" has.
-/
def Module.declarationSplitBindersArgs [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (forDeclaration : Name) (k : DeclarationKind) : m ((Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Array Term) × (Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Array Term)) := do
  let (allModParams, specificParams) ← mod.declarationAllParams forDeclaration k
  let (allModBinders, allModArgs) := (← allModParams.mapM (·.binder), ← allModParams.mapM (·.ident))
  let (specificBinders, specificArgs) := (← Option.stxArrMapM specificParams toBracketedBinderArray, ← Option.stxArrMapM specificParams explicitBindersToTerms)
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
  | .uninterpretedSort => f p
  | _ => pure .none

def Module.sortBinders [Monad m] [MonadQuotation m] (mod : Module) (withFieldConcreteType? : Bool := false) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  mod.sortFilterMapFn (·.binder) >>= (fun x => if withFieldConcreteType? then
    Parameter.fieldConcreteType >>= Parameter.binder >>= (pure <| x.push ·)
  else pure x)

def Module.sortIdents [Monad m] [MonadQuotation m] (mod : Module) (withFieldConcreteType? : Bool := false) : m (Array Ident) := do
  mod.sortFilterMapFn (·.ident) >>= (fun x =>
    pure (if withFieldConcreteType? then x.push fieldConcreteType else x))

def Module.assumptions (mod : Module) : Array StateAssertion :=
  mod.assertions.filter (fun a => a.kind == .assumption)

def Module.actions (mod : Module) : Array ProcedureSpecification :=
  mod.procedures.filter (fun p => match p.info with | .action _ => true | _ => false)

/-- All `invariant`s, `safety`, and `trusted invariant`s.-/
def Module.invariants (mod : Module) : Array StateAssertion :=
  mod.assertions.filter fun a => match a.kind with
  | .invariant | .safety | .trustedInvariant => true
  | .assumption => false

/-- All `invariant`s and `safety`s.-/
def Module.checkableInvariants (mod : Module) : Array StateAssertion :=
  mod.assertions.filter fun a => match a.kind with
  | .invariant | .safety => true
  | .trustedInvariant | .assumption => false

def Module.trustedInvariants (mod : Module) : Array StateAssertion :=
  mod.assertions.filter (fun a => a.kind == .trustedInvariant)

def Module.safeties (mod : Module) : Array StateAssertion :=
  mod.assertions.filter (fun a => a.kind == .safety)

def Module.stateStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (withFieldConcreteType? : Bool := false) : m Term :=
  return ← `(term| @$(mkIdent stateName) $(← mod.sortIdents withFieldConcreteType?)*)

def Module.theoryStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Term :=
  return ← `(term| @$(mkIdent theoryName) $(← mod.sortIdents)*)

def Module.declareUninterpretedSort [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (name : Name) (userStx : Syntax): m Module := do
  mod.throwIfAlreadyDeclared name
  let typeT ← `(term|Type)
  let param : Parameter := { kind := .uninterpretedSort, name := name, «type» := typeT, userSyntax := userStx }
  let id := mkIdent name
  let dec_eq_type ← `(term|$(mkIdent ``DecidableEq).{1} $id)
  let dec_inhabited_type ← `(term|$(mkIdent ``Inhabited).{1} $id)
  let dec_eq : Parameter := { kind := .moduleTypeclass .backgroundTheory, name := Name.mkSimple s!"{name}_dec_eq", «type» := dec_eq_type, userSyntax := userStx }
  let inhabited : Parameter := { kind := .moduleTypeclass .backgroundTheory, name := Name.mkSimple s!"{name}_inhabited", «type» := dec_inhabited_type, userSyntax := userStx }
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

def Module.getStateBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  mod.signature.filterMapM fun sc => do
    match sc.mutability with
    | .mutable => return .some $ ← `(bracketedBinder| ($(mkIdent sc.name) : $(← sc.typeStx)))
    | _ => pure .none

/-- Given a list of state components, return the syntax for a structure
definition including those components. -/
private def structureDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (name : Name) (params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (deriveInstances : Bool := true)
  (fields : Array (TSyntax `Lean.Parser.Command.structSimpleBinder)) : m Syntax := do
  if deriveInstances then
    `(structure $(mkIdent name) $params* where
        $(mkIdent `mk):ident :: $[$fields]*
      deriving $(mkIdent ``Inhabited), $(mkIdent ``Nonempty))
  else
    `(structure $(mkIdent name) $params* where
      $(mkIdent `mk):ident :: $[$fields]*)

/-- Syntax for *defining* the mutable state of a module as a `structure`. The
syntax for the type is `mod.stateStx`. -/
private def Module.stateDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Syntax := do
  structureDefinitionStx stateName (← mod.sortBinders) (deriveInstances := true)
    (← mod.mutableComponents.mapM fun sc => sc.getSimpleBinder)

/-- Similar to `Module.stateDefinitionStx` but each field of `State` is
abstracted by a function from its label to a certain type. -/
private def Module.fieldsAbstractedStateDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Syntax := do
  let stateLabelTypeName := structureFieldLabelTypeName stateName
  let fields ← mod.mutableComponents.mapM fun sc => do
    let ty ← `($fieldConcreteType $(mkIdent <| stateLabelTypeName ++ sc.name):ident)
    `(Command.structSimpleBinder| $(mkIdent sc.name):ident : $ty)
  structureDefinitionStx stateName (← mod.sortBinders true) (deriveInstances := false) fields

/-- Syntax for *defining* the immutable background theory of a module as a
`structure`. The syntax for the type is `mod.theoryStx`. -/
private def Module.theoryDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Syntax := do
  structureDefinitionStx theoryName (← mod.sortBinders) (deriveInstances := false)
    (← mod.immutableComponents.mapM fun sc => sc.getSimpleBinder)

def Module.declareStateStructure [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Module × Syntax) := do
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

/-- Declare dispatchers that given the label for a specific field, returns
the types of its arguments and its codomain. -/
private def declareFieldDispatchers [Monad m] [MonadQuotation m] [MonadError m] (base : Name) (argTypes : Array (Array Term)) (bases : Array Term) (params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) : m ((Name × TSyntax `command) × (Name × TSyntax `command)) := do
  let components ← argTypes.mapM fun tps => `([ $[$tps],* ])
  let l := mkIdent `l
  let casesOnName := structureFieldLabelTypeName base ++ `casesOn
  let params := params.push (← `(bracketedBinder| ($l : $(structureFieldLabelType base))))
  let stx1 ← `(def $(fieldToComponents base) $params* : List Type :=
    $(mkIdent casesOnName) $l $components*)
  let stx2 ← `(def $(fieldToBase base) $params* : Type :=
    $(mkIdent casesOnName) $l $bases*)
  return ((fieldToComponentsName base, stx1), (fieldToBaseName base, stx2))

private def analyzeTypesOfStateComponents [Monad m] [MonadQuotation m] [MonadError m] (components : Array StateComponent) : m (Array (Array Term × Term)) := do
  components.mapM fun sc => do
    match sc.type with
    | .simple t => getSimpleBinderType t >>= splitForallArgsCodomain
    | .complex b d =>
      -- overlapped with `complexBinderToSimpleBinder`
      let res ← b.mapM fun m => match m with
        | `(bracketedBinder| ($_arg:ident : $tp:term)) => return tp
        | _ => throwError "unable to extract type from binder {m}"
      pure (res, d)

def Module.declareStateFieldLabelTypeAndDispatchers [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Module × Array Syntax) := do
  let components := mod.mutableComponents
  let (argTypes, bases) ← Array.unzip <$> analyzeTypesOfStateComponents components
  let argTypesAsMap : Std.HashMap Name (Array Term) := Std.HashMap.ofList (components.zipWith (fun sc args => (sc.name, args)) argTypes |>.toList)
  let (name0, stx0) ← declareStructureFieldLabelType stateName components
  let ((name1, stx1), (name2, stx2)) ← declareFieldDispatchers stateName argTypes bases (← mod.sortBinders)
  for name in [name0, name1, name2] do
    mod.throwIfAlreadyDeclared name
  -- add the `fieldConcreteType` parameter
  let fieldConcreteTypeParam ← Parameter.fieldConcreteType
  -- add the related typeclasses
  let f := mkIdent `f
  let paramsArgs ← mod.sortIdents
  let toComponentsTerm ← `(($(mkIdent name1) $paramsArgs* $f))
  let toBaseTerm ← `(($(mkIdent name2) $paramsArgs* $f))
  let fieldConcreteTypeApplied ← `(($fieldConcreteType $f))
  let fieldRepType ← `(∀ $f, $(mkIdent ``FieldRepresentation) $toComponentsTerm $toBaseTerm $fieldConcreteTypeApplied)
  let fieldRep : Parameter := { kind := .moduleTypeclass .fieldRepresentation, name := fieldRepresentationName, «type» := fieldRepType, userSyntax := .missing }
  let lawfulFieldRepType ← `(∀ $f, $(mkIdent ``LawfulFieldRepresentation) $toComponentsTerm $toBaseTerm $fieldConcreteTypeApplied ($fieldRepresentation $f))
  let lawfulFieldRep : Parameter := { kind := .moduleTypeclass .lawfulFieldRepresentation, name := lawfulFieldRepresentationName, «type» := lawfulFieldRepType, userSyntax := .missing }
  return ({ mod with parameters := mod.parameters ++ #[fieldConcreteTypeParam, fieldRep, lawfulFieldRep] ,
                     _declarations := mod._declarations.insert fieldConcreteTypeParam.name .moduleParameter ,
                     _fieldRepMetaData := argTypesAsMap }, #[stx0, stx1, stx2])

def Module.declareFieldsAbstractedStateStructure [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Module × Syntax) := do
  mod.throwIfAlreadyDeclared environmentSubStateName
  let stx ← mod.fieldsAbstractedStateDefinitionStx
  let stateStx ← mod.stateStx true
  let substate : Parameter := { kind := .moduleTypeclass .environmentState, name := environmentSubStateName, «type» := ← `($(mkIdent ``IsSubStateOf) $stateStx $environmentState), userSyntax := .missing }
  return ({ mod with parameters := mod.parameters.push substate, _declarations := mod._declarations.insert environmentSubStateName .moduleParameter }, stx)

def Module.declareTheoryStructure [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Module × Syntax) := do
  mod.throwIfAlreadyDeclared environmentSubTheoryName
  let stx ← mod.theoryDefinitionStx
  let theoryStx ← mod.theoryStx
  let subtheory : Parameter := { kind := .moduleTypeclass .backgroundTheory, name := environmentSubTheoryName, «type» := ← `($(mkIdent ``IsSubReaderOf) $theoryStx $environmentTheory), userSyntax := .missing }
  return ({ mod with parameters := mod.parameters.push subtheory, _declarations := mod._declarations.insert environmentSubTheoryName .moduleParameter }, stx)

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
def elabExactState : TacticM Unit := do
  let mod ← getCurrentModule
  let comp := mod.mutableComponents.map (Lean.mkIdent ·.name)
  let constr <- `(term| (⟨$[$comp],*⟩ : $(← mod.stateStx)))
  trace[veil.debug] "state constr: {constr}"
  Tactic.evalTactic $ ← `(tactic| exact $constr)

elab_rules : tactic
  | `(tactic| veil_exact_theory) => elabExactTheory
  | `(tactic| veil_exact_state) => elabExactState

/-- This is used wherever we want to define a predicate over the
background theory (e.g. in `assumption` definitions). Instead of
writing `fun th => Pred`, this will pattern-match over the theory and
make all its fields accessible for `Pred`. -/
def withTheory (t : Term) :  MetaM (Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Term) := do
  let mut mod ← getCurrentModule
  let theoryName := mod.name ++ theoryName
  let casesOnTheory ← delabVeilExpr $ mkConst $ (theoryName ++ `casesOn)
  let (th, motive) := (mkIdent `th, mkIdent `motive)
  let fn ← `(term|(fun ($th : $environmentTheory) =>
    @$(casesOnTheory)
    $(← mod.sortIdents)*
    ($motive := fun _ => Prop)
    ($(mkIdent ``readFrom) $th)
    (fun $[$(← getFieldIdentsForStruct theoryName)]* => $t)))
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
  let (theoryName, stateName) := (mod.name ++ theoryName, mod.name ++ stateName)
  let casesOnTheory ← delabVeilExpr $ mkConst $ (theoryName ++ `casesOn)
  let casesOnState ← delabVeilExpr $ mkConst $ (stateName ++ `casesOn)
  let (th, st, motive) := (mkIdent `th, mkIdent `st, mkIdent `motive)
  let body ← if !mod._useStateRepTC then pure t else
    let fields ← getFieldIdentsForStruct stateName
    fields.foldrM (init := t) fun f b => do
      `(let $f:ident := ($fieldRepresentation _).$(mkIdent `get) $f:ident ; $b)
  let fn ← `(term|(fun ($th : $environmentTheory) ($st : $environmentState) =>
    @$(casesOnTheory) $(← mod.sortIdents)*
    ($motive := fun _ => Prop)
    ($(mkIdent ``readFrom) $th) <|
    (fun $[$(← getFieldIdentsForStruct theoryName)]* =>
      @$(casesOnState) $(← mod.sortIdents mod._useStateRepTC)*
      ($motive := fun _ => Prop)
      ($(mkIdent ``getFrom) $st)
      (fun $[$(← getFieldIdentsForStruct stateName)]* => ($body)))))
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
private def Module.mkVeilTerm (mod : Module) (name : Name) (dk : DeclarationKind) (params : Option (TSyntax `Lean.explicitBinders)) (term : Term) (justTheory : Bool := false) : TermElabM (Array Parameter × Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Term) := do
  let baseParams ← mod.declarationBaseParams dk
  let binders ← baseParams.mapM (·.binder)
  let paramBinders ← Option.stxArrMapM params toBracketedBinderArray
  -- We need to universally quantify capital variables, but for that to work, the
  -- term needs to be well-typed, so all term's parameters, as well as the theory
  -- and state variables (i.e. the fields) have to be bound first.
  -- trace[veil.debug] "before UQC (paramBinders: {paramBinders}): {term}"
  let term' ← elabBinders (binders ++ paramBinders ++ (← mod.getTheoryBinders) ++ (← mod.getStateBinders)) $ fun _ => univerallyQuantifyCapitals term
  -- We don't `universallyQuantifyCapitals` after `withTheory` /
  -- `withTheoryAndState` because we want to have the universal
  -- quantification as deeply inside the term as possible, rather than above
  -- the binders for `rd` and `st` introduced below.
  let (thstBinders, term') ← if justTheory then withTheory term' else withTheoryAndState term'
  let term' := Syntax.inheritSourceSpanFrom term' term
  -- Record the `Decidable` instances that are needed for the assertion.
  let (insts, _) ← elabBinders (binders ++ paramBinders ++ thstBinders) $ fun _ => getRequiredDecidableInstances term'
  trace[veil.debug] "insts: {insts.map (·.1)}"
  let extraParams : Array Parameter := insts.mapIdx (fun i (decT, _) => { kind := .definitionTypeclass name, name := Name.mkSimple s!"{name}_dec_{i}", «type» := decT, userSyntax := .missing })
  return (extraParams, thstBinders, term')

end AssertionElab

/-- Register the assertion (and any optional `Decidable` instances)
in the module, and return the syntax to elaborate. -/
def Module.defineAssertion (mod : Module) (base : StateAssertion) : CommandElabM (Command × Module) := do
  mod.throwIfAlreadyDeclared base.name
  let mut mod := mod
  let justTheory := match base.kind with | .assumption => true | _ => false
  let (extraParams, thstBinders, term) ← liftTermElabM $ mod.mkVeilTerm base.name base.declarationKind (params := .none) base.term (justTheory := justTheory)
  mod ← mod.registerAssertion { base with extraParams := extraParams }
  -- This includes the required `Decidable` instances
  let (binders, _) ← mod.declarationAllParamsMapFn (·.binder) base.name base.declarationKind
  -- NOTE(SUBTLE): we do something counter-intuitive here. Making the `ρ` and `σ`
  -- arguments implicit ensures that whenever the default values for `thstBinders`
  -- are evaluated (i.e. not provided explicitly), the assertion is forced to be
  -- evaluated with `ρ := Theory` and `σ := State`. This makes it possible to do
  -- things like `assert invariant` in action without having to provide any
  -- explicit arguments.
  let binders := (← binders.mapM mkImplicitBinder) ++ thstBinders
  let attrs ← #[`invSimp].mapM (fun attr => `(attrInstance| $(Lean.mkIdent attr):ident))
  let stx ← `(@[$attrs,*] def $(mkIdent base.name) $[$binders]* := $term)
  return (stx, mod)

def Module.registerDerivedDefinition [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (ddef : DerivedDefinition) : m Module := do
  mod.throwIfAlreadyDeclared ddef.name
  return { mod with _declarations := mod._declarations.insert ddef.name ddef.declarationKind, _derivedDefinitions := mod._derivedDefinitions.insert ddef.name ddef }

def Module.defineGhostRelation (mod : Module) (name : Name) (params : Option (TSyntax `Lean.explicitBinders)) (term : Term) (justTheory : Bool := false) : CommandElabM (Command × Module) := do
  mod.throwIfAlreadyDeclared name
  let kind? := .stateAssertion .invariant -- a ghost relation is a predicate that depends on the state
  let ddKind := .derivedDefinition (if justTheory then .theoryGhost else .ghost) (Std.HashSet.emptyWithCapacity 0)
  let (baseParams, _) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) ddKind
  let paramBinders ← Option.stxArrMapM params toBracketedBinderArray
  let (extraParams, thstBinders, term) ← liftTermElabM $ mod.mkVeilTerm name kind? params term justTheory
  -- See NOTE(SUBTLE).
  let baseBinders ← (baseParams ).mapM (·.binder)
  let binders := (← baseBinders.mapM mkImplicitBinder) ++ paramBinders ++ thstBinders ++ (← extraParams.mapM (·.binder))
  let attrs ← #[`invSimp].mapM (fun attr => `(attrInstance| $(Lean.mkIdent attr):ident))
  let stx ← `(@[$attrs,*] abbrev $(mkIdent name) $[$binders]* := $term)
  trace[veil.debug] "stx: {stx}"
  -- FIXME: we should probably add `thstBinders` to `params`?
  let ddef : DerivedDefinition := { name := name, kind := .ghost, params := params, extraParams := extraParams, derivedFrom := Std.HashSet.emptyWithCapacity 0, stx := stx }
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
  let derivedDef : DerivedDefinition := { name := assembledName, kind := kind, params := none, extraParams := extraParams, derivedFrom := conjunctsSet, stx := cmd }
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

private def Module.labelTypeStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Term := do
  `(term|$labelType $(← mod.sortIdents)*)

private def Module.assembleLabelDef [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Command × Module) := do
  mod.throwIfAlreadyDeclared labelTypeName
  let labelT ← mod.labelTypeStx
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let ctors ← mod.actions.mapM (fun a => do
    `(Command.ctor| | $(mkIdent a.name):ident $(← a.binders)* : $labelT ))
  let labelDef ←
    if ctors.isEmpty then
      `(inductive $labelType $(← mod.sortBinders)* where $[$ctors]*)
    else
      `(inductive $labelType $(← mod.sortBinders)* where $[$ctors]* deriving $(mkIdent ``Inhabited), $(mkIdent ``Nonempty))
  let derivedDef : DerivedDefinition := { name := labelTypeName, kind := .stateLike, params := none, extraParams := #[], derivedFrom := actionNames, stx := labelDef }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (labelDef, mod)

private def Module.assembleLabelCasesLemma [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Command × Module) := do
  mod.throwIfAlreadyDeclared labelCasesName
  let P := mkIdent `P
  let labelT ← mod.labelTypeStx
  let exs ← mod.actions.mapM (fun a => do
    let constructor := Lean.mkIdent $ labelTypeName ++ a.name
    match a.params with
    | some br => `(term| (∃ $br, $P ($constructor $(← explicitBindersToTerms br)*)))
    | none => `(term| $P ($constructor)))
  let label := mkIdent `label
  let casesLemma ← `(command|set_option linter.unusedSectionVars false in
    theorem $labelCases ($P : $labelT -> Prop) :
      (∃ $label:ident : $labelT, $P $label) ↔
      $(← repeatedOr exs) :=
    by
      constructor
      { rintro ⟨$(mkIdent `l), $(mkIdent `r)⟩; rcases $(mkIdent `l):ident <;> aesop }
      { aesop })
  let derivedDef : DerivedDefinition := { name := labelCasesName, kind := .stateLike, params := none, extraParams := #[], derivedFrom := {labelTypeName}, stx := casesLemma }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (casesLemma, mod)

def Module.assembleLabel [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array Command × Module) := do
  let (labelDef, mod) ← mod.assembleLabelDef
  let (casesLemma, mod) ← mod.assembleLabelCasesLemma
  return (#[labelDef, casesLemma], mod)

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
  let nextParam ← `(explicitBinders| ($label:ident : $labelT))
  let derivedDef : DerivedDefinition := { name := assembledNextActName, kind := .actionLike, params := nextParam, extraParams := extraParams, derivedFrom := actionNames, stx := nextDef }
  let mod ← mod.registerDerivedDefinition derivedDef
  return (nextDef, mod)

end Veil
