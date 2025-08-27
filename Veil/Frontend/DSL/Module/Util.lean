import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Syntax
import Veil.Util.Meta
import Veil.Frontend.DSL.Util
import Veil.Frontend.DSL.State

open Lean Parser Elab Command Term

/-! ## Background theory and State -/

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
  toString sa := match sa.term with
    | some term => s!"{sa.kind} [{sa.name}] {term}"
    | none => s!"{sa.kind} [{sa.name}]"

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

/-- Name of the generic/environment background theory (i.e. `Reader` monad state)
variable. -/
def environmentTheoryName : Name := `ρ
def environmentTheory : Ident := mkIdent environmentTheoryName
def environmentSubTheoryName : Name := `ρ_sub
def environmentSubTheory : Ident := mkIdent environmentSubTheoryName

/-- Name of the environment state (for the `State` monad) variable. -/
def environmentStateName : Name := `σ
def environmentState : Ident := mkIdent environmentStateName
def environmentSubStateName : Name := `σ_sub
def environmentSubState : Ident := mkIdent environmentSubStateName

def stateName : Name := `State
def theoryName : Name := `Theory

def subStateInstIdent (id : Ident): Ident := mkIdent $ Name.mkSimple s!"{id.getId}_substate"
def environmentSubStateIdent : Ident := subStateInstIdent environmentState

def subReaderInstIdent (id : Ident): Ident := mkIdent $ Name.mkSimple s!"{id.getId}_reader"
def environmentSubReaderIdent : Ident := subReaderInstIdent environmentTheory

def Parameter.environmentTheory [Monad m] [MonadQuotation m] : m Parameter :=
  return { kind := .backgroundTheory, name := environmentTheoryName, «type» := ← `(Type), userSyntax := .missing }

def Parameter.environmentState [Monad m] [MonadQuotation m] : m Parameter :=
  return { kind := .environmentState, name := environmentStateName, «type» := ← `(Type), userSyntax := .missing }

def Module.freshWithName [Monad m] [MonadQuotation m] (name : Name) : m Module := do
  let params := #[← Parameter.environmentTheory, ← Parameter.environmentState]
  return { name := name, parameters := params, dependencies := #[], signature := #[], procedures := #[], assertions := #[], _declarations := .emptyWithCapacity }

def Module.isDeclared (mod : Module) (name : Name) : Bool :=
  mod._declarations.contains name

def Module.throwIfAlreadyDeclared [Monad m] [MonadError m] (mod : Module) (name : Name) : m Unit := do
  if mod.isDeclared name then
    throwError s!"{name} is already declared in module {mod.name}. Cannot redeclare it!"

/-- Is the state of this module defined (in the sense that it can no
longer be changed, since some definitions already depend on it)? -/
def Module.isStateDefined (mod : Module) : Bool := mod._stateDefined

def Module.throwIfStateAlreadyDefined [Monad m] [MonadError m] (mod : Module) : m Unit := do
  if mod.isStateDefined then
    throwError s!"The state of module {mod.name} has already been defined. It can no longer be changed!"

/-- Convert a `Parameter` to a `bracketedBinder` syntax. -/
def Parameter.binder [Monad m] [MonadQuotation m] (p : Parameter) : m (TSyntax `Lean.Parser.Term.bracketedBinder) :=
  match p.kind with
  | .moduleTypeclass | .definitionTypeclass _ =>
  if p.name != Name.anonymous then
    `(bracketedBinder|[$(mkIdent p.name) : $(p.type)])
  else
    `(bracketedBinder|[$(p.type)])
  | _ => `(bracketedBinder|($(mkIdent p.name) : $(p.type)))

def Parameter.ident [Monad m] [MonadQuotation m] (p : Parameter) : m Ident := return mkIdent p.name

def Module.sortMapFn [Monad m] [MonadQuotation m] (mod : Module) (f : Parameter → m α) : m (Array α) := do
  mod.parameters.filterMapM fun p => do match p.kind with
  | .uninterpretedSort => f p
  | _ => pure .none

def Module.actionMapFn [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (f : Parameter → m α) (forAct : Option Name := .none) : m (Array α) := do
  let act := mod.procedures.find? (fun p => forAct == .some p.name)
  let extraParams := match act with
  | some act => act.extraParams
  | none => #[]
  let allParams := mod.parameters ++ extraParams
  allParams.filterMapM fun p => do
    match p.kind with
    | .definitionTypeclass defName => if forAct == .some defName then f p else pure .none
    | _ => f p

def Module.sortBinders [Monad m] [MonadQuotation m] (mod : Module) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  mod.sortMapFn (·.binder)

def Module.sortIdents [Monad m] [MonadQuotation m] (mod : Module) : m (Array Ident) := do
  mod.sortMapFn (·.ident)

def Module.actionBinders [Monad m] [MonadError m] [MonadQuotation m] (mod : Module) (forAct : Option Name := .none) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  mod.actionMapFn (·.binder) forAct

def Module.stateStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Term :=
  return ← `(term| @$(mkIdent stateName) $(← mod.sortIdents)*)

def Module.theoryStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Term :=
  return ← `(term| @$(mkIdent theoryName) $(← mod.sortIdents)*)

def Module.declareUninterpretedSort [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) (name : Name) (userStx : Syntax): m Module := do
  mod.throwIfAlreadyDeclared name
  let typeT ← `(term|Type)
  let param : Parameter := { kind := .uninterpretedSort, name := name, «type» := typeT, userSyntax := userStx }
  let id := mkIdent name
  let dec_eq_type ← `(term|$(mkIdent ``DecidableEq) $id)
  let dec_inhabited_type ← `(term|$(mkIdent ``Inhabited) $id)
  let dec_eq : Parameter := { kind := .moduleTypeclass, name := Name.mkSimple s!"{name}_dec_eq", «type» := dec_eq_type, userSyntax := userStx }
  let inhabited : Parameter := { kind := .moduleTypeclass, name := Name.mkSimple s!"{name}_inhabited", «type» := dec_inhabited_type, userSyntax := userStx }
  let params := #[param, dec_eq, inhabited]
  return { mod with parameters := mod.parameters.append params, _declarations := mod._declarations.insert name }

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
  let mod := { mod with signature := mod.signature.push sc, _declarations := mod._declarations.insert sc.name }
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

/-- Given a list of state components, return the syntax for a structure
definition including those components. -/
private def structureDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (name : Name) (params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (components : Array StateComponent) (deriveInstances : Bool := true): m Syntax := do
  let fields ← components.mapM StateComponent.getSimpleBinder
  if deriveInstances then
    `(structure $(mkIdent name) $params* where
        $(mkIdent `mk):ident :: $[$fields]*
      deriving $(mkIdent ``Inhabited), $(mkIdent ``Nonempty))
  else
    `(structure $(mkIdent name) $params* where
      $(mkIdent `mk):ident :: $[$fields]*)

/-- Syntax for defining the mutable state of a module as a `structure`. -/
private def Module.stateDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Syntax := do
  structureDefinitionStx stateName (← mod.sortBinders) mod.mutableComponents (deriveInstances := true)

/-- Syntax for defining the immutable background theory of a module as a `structure`. -/
private def Module.theoryDefinitionStx [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m Syntax := do
  structureDefinitionStx theoryName (← mod.sortBinders) mod.immutableComponents (deriveInstances := false)

def Module.declareStateStructure [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Module × Syntax) := do
  let stx ← mod.stateDefinitionStx
  let stateStx ← mod.stateStx
  let substate : Parameter := { kind := .moduleTypeclass, name := environmentSubStateName, «type» := ← `($(mkIdent ``IsSubStateOf) $stateStx $environmentState), userSyntax := .missing }
  return ({ mod with parameters := mod.parameters.push substate }, stx)

def Module.declareTheoryStructure [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Module × Syntax) := do
  let stx ← mod.theoryDefinitionStx
  let theoryStx ← mod.theoryStx
  let subtheory : Parameter := { kind := .moduleTypeclass, name := environmentSubTheoryName, «type» := ← `($(mkIdent ``IsSubReaderOf) $theoryStx $environmentTheory), userSyntax := .missing }
  return ({ mod with parameters := mod.parameters.push subtheory }, stx)

/-- Crystallizes the state of the module, i.e. it defines it as a Lean
`structure` definition, if that hasn't already happened. -/
def Module.ensureStateIsDefined (mod : Module) : CommandElabM Module := do
  if mod.isStateDefined then
    return mod
  let (mod, stateStx) ← mod.declareStateStructure
  let (mod, theoryStx) ← mod.declareTheoryStructure
  elabVeilCommand stateStx
  elabVeilCommand theoryStx
  generateIgnoreFn mod
  return { mod with _stateDefined := true }
where
  /-- Instruct the linter to not mark state variables as unused in our
  `after_init` and `action` definitions. -/
  generateIgnoreFn (mod : Module) : CommandElabM Unit := do
    let cmd ← Command.runTermElabM fun _ => do
      let fnIdents ← mod.mutableComponents.mapM (fun sc => `($(quote sc.name)))
      let namesArrStx ← `(#[$[$fnIdents],*])
      let id := mkIdent `id
      let fnStx ← `(fun $id $(mkIdent `stack) _ => $(mkIdent ``Array.contains) ($namesArrStx) ($(mkIdent ``Lean.Syntax.getId) $id) /-&& isActionSyntax stack-/)
      let nm := mkIdent `ignoreStateFields
      let ignoreFnStx ← `(@[$(mkIdent `unused_variables_ignore_fn):ident] def $nm : $(mkIdent ``Lean.Linter.IgnoreFunction) := $fnStx)
      return ignoreFnStx
    elabVeilCommand cmd

def _root_.Lean.TSyntax.getPropertyName (stx : TSyntax `propertyName) : Name :=
  match stx with
  | `(propertyName| [$id]) => id.getId
  | _ => unreachable!

def Module.mkAssertion [Monad m] (mod : Module) (kind : StateAssertionKind) (name : Option (TSyntax `propertyName)) (prop : Term) (stx : Syntax) : m StateAssertion := do
  let name := nameForAssertion mod kind name
  let defaultSets := Std.HashSet.emptyWithCapacity.insert mod.defaultAssertionSet
  return { kind := kind, name := name, term := prop, userSyntax := stx, inSets := defaultSets }
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

def Module.registerAssertion [Monad m] [MonadError m] (mod : Module) (sc : StateAssertion) : m Module := do
  mod.throwIfAlreadyDeclared sc.name
  let mut mod := { mod with assertions := mod.assertions.push sc }
  for set in sc.inSets do
    let currentAssertions := mod._assertionSets.getD set Std.HashSet.emptyWithCapacity
    mod := { mod with _assertionSets := mod._assertionSets.insert set (currentAssertions.insert sc.name) }
  return mod

end Veil
