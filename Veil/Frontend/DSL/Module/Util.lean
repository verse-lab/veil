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
    | none => s!"{sa.kind} [{sa.name}] {sa.expr}"

/-! ## Procedure and actions -/

def initializerName : Name := `initializer

def ProcedureKind.isAction (kind : ProcedureInfo) : Bool :=
  match kind with
  | .action _ => true
  | _ => false

def ProcedureKind.actionDecl (kind : ProcedureInfo) : Option ActionDeclaration :=
  match kind with
  | .action decl => some decl
  | _ => none

def ProcedureKind.procedureDecl (kind : ProcedureInfo) : Option ProcedureDeclaration :=
  match kind with
  | .procedure decl => some decl
  | _ => none

def ProcedureSpecification.name (a : ProcedureSpecification) : Name :=
  match a.info with
  | .action decl => decl.name
  | .procedure decl => decl.name
  | .initializer => initializerName

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

/-- Convert a `Parameter` to a `bracketedBinder` syntax. -/
def Parameter.binder [Monad m] [MonadQuotation m] (p : Parameter) : m (TSyntax `Lean.Parser.Term.bracketedBinder) :=
  match p.kind with
  | .typeclass _ => `(bracketedBinder|[$(mkIdent p.name) : $(p.type)])
  | _ => `(bracketedBinder|($(mkIdent p.name) : $(p.type)))

def Parameter.ident [Monad m] [MonadQuotation m] (p : Parameter) : m Ident := do
  match p.kind with
  | .typeclass _ => return mkIdent p.name
  | _ => return mkIdent p.name

def Module.sortMapFn [Monad m] [MonadQuotation m] (mod : Module) (f : Parameter → m α) : m (Array α) := do
  mod.parameters.filterMapM fun p => do match p.kind with
  | .uninterpretedSort => f p
  | _ => pure .none

def Module.actionMapFn [Monad m] [MonadQuotation m] (mod : Module) (f : Parameter → m α) : m (Array α) := do
  mod.parameters.filterMapM fun p => do match p.kind with
  | _ => f p

def Module.sortBinders [Monad m] [MonadQuotation m] (mod : Module) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  mod.sortMapFn (·.binder)

def Module.sortIdents [Monad m] [MonadQuotation m] (mod : Module) : m (Array Ident) := do
  mod.sortMapFn (·.ident)

def Module.actionBinders [Monad m] [MonadQuotation m] (mod : Module) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  mod.actionMapFn (·.binder)

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
  -- let finenum_type ← `(term|$(mkIdent ``FinEnum) $id)
  let dec_eq : Parameter := { kind := .typeclass .alwaysRequired, name := Name.mkSimple s!"{name}_dec_eq", «type» := dec_eq_type, userSyntax := userStx }
  let inhabited : Parameter := { kind := .typeclass .alwaysRequired, name := Name.mkSimple s!"{name}_inhabited", «type» := dec_inhabited_type, userSyntax := userStx }
  -- let finenum : Parameter := { kind := .typeclass .requiredForExecution, name := Name.mkSimple s!"{name}_finenum", «type» := finenum_type, userSyntax := userStx }
  let params := #[param, dec_eq, inhabited, /- finenum -/]
  return { mod with parameters := mod.parameters.append params, _declarations := mod._declarations.insert name }

def isValidStateComponentType (kind : StateComponentKind) (tp : Expr) : CommandElabM Bool := do
  let returnsProp ← liftTermElabM $ Meta.forallTelescope tp (fun _ b => return b.isProp || b.isBool)
  match kind with
  | .individual => return !tp.isArrow
  | .relation => return returnsProp
  | .function => return tp.isArrow && !returnsProp
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
  -- TODO: add `Decidable` instances for the state component type (only if it's immutable??)
  let mod ← addDecidableInstanceIfNeeded mod sc tp
  return mod
where
  failureMsg (_sig : TSyntax `Lean.Parser.Command.structSimpleBinder) (comp : StateComponent) : CommandElabM Unit := do
    throwErrorAt comp.userSyntax match comp.kind with
    | .individual => m!"Invalid type: individuals must not be arrow types."
    | .relation => m!"Invalid type: relations must return Prop or Bool."
    | .function => m!"Invalid type: functions must have arrow type and not return Prop or Bool."
    | .module => m!"Invalid type: module state components must be structures."
  stateComponentForDecidableInstance (decName : Name) (relName : Name) (tp : Expr) : CommandElabM StateComponent := do
    let numRelArgs := tp.getForallArityExplicitBinders
    let decTp ← `(Command.structSimpleBinder|$(mkIdent decName):ident : $(← decidableNStx numRelArgs relName))
    return { mutability := sc.mutability, kind := StateComponentKind.individual, name := decName, «type» := StateComponentType.simple decTp, userSyntax := .missing }
  addDecidableInstanceIfNeeded (mod : Module) (sc : StateComponent) (tp : Expr) : CommandElabM Module := do
    if sc.mutability == Mutability.mutable then
      return mod
    let mut mod := mod
    let env ← getEnv
    let returnsProp (t : Expr) : TermElabM Bool := Meta.forallTelescope t (fun _ b => return b.isProp)
    match tp.getAppFn.constName? with
    | .none => do
      if (← liftTermElabM $ returnsProp tp) then
        let decName := Name.mkSimple s!"_{sc.name}_dec"
        let sc' ← stateComponentForDecidableInstance decName sc.name tp
        mod := { mod with signature := mod.signature.push sc' }
    | .some className =>
      let .some si := getStructureInfo? env className
        | throwErrorAt sc.userSyntax s!"{className} is not a structure"
      -- Decide whether to add a `Decidable` instance for each field of the structure
      for fi in si.fieldInfo do
        let .some proj := env.find? fi.projFn
          | throwErrorAt sc.userSyntax s!"{fi.projFn} is not a valid projection function"
        let shouldAddDecidableInstance ← liftTermElabM $ (do
          let isProp ← Meta.isProp proj.type
          return !isProp && (← returnsProp proj.type))
        if shouldAddDecidableInstance then
          let decName := Name.mkSimple s!"_{sc.name}_{fi.fieldName}_dec"
          let relName := s!"{sc.name}.{fi.fieldName}".toName
          let sc' ← stateComponentForDecidableInstance decName relName proj.type
          mod := { mod with signature := mod.signature.push sc' }
    return mod

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
  let substate : Parameter := { kind := .typeclass .alwaysRequired, name := environmentSubStateName, «type» := ← `($(mkIdent ``IsSubStateOf) $stateStx $environmentState), userSyntax := .missing }
  return ({ mod with parameters := mod.parameters.push substate }, stx)

def Module.declareTheoryStructure [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Module × Syntax) := do
  let stx ← mod.theoryDefinitionStx
  let theoryStx ← mod.theoryStx
  let subtheory : Parameter := { kind := .typeclass .alwaysRequired, name := environmentSubTheoryName, «type» := ← `($(mkIdent ``IsSubReaderOf) $theoryStx $environmentTheory), userSyntax := .missing }
  return ({ mod with parameters := mod.parameters.push subtheory }, stx)

end Veil
