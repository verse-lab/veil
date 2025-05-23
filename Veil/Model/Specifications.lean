import Lean
import Veil.Model.IOAutomata
import Veil.Util.Meta

open Lean Parser

inductive StateComponentKind where
  | individual
  | relation
  | function
deriving Inhabited

instance : ToString StateComponentKind where
  toString
    | StateComponentKind.individual => "individual"
    | StateComponentKind.relation => "relation"
    | StateComponentKind.function => "function"

inductive StateComponentType where
  /-- e.g. `name : Int -> vertex -> Prop` -/
  | simple (t : TSyntax ``Command.structSimpleBinder)
  /-- e.g. `(r : Int) (v : vertex)` and `Prop` -/
  | complex (binders : TSyntaxArray ``Term.bracketedBinder) (dom : TSyntax `term)
deriving Inhabited

instance : ToString StateComponentType where
  toString
    | StateComponentType.simple t => toString t
    | StateComponentType.complex b d  => s!"{b} : {d}"

def StateComponentType.stx (sct : StateComponentType) : CoreM (TSyntax `term) := do
  match sct with
  | .simple t => getSimpleBinderType t
  | .complex b d => getSimpleBinderType $ ← complexBinderToSimpleBinder (mkIdent Name.anonymous) b d

inductive Mutability
  | mutable
  | immutable
deriving Inhabited, BEq

instance : ToString Mutability where
  toString
    | Mutability.mutable => "mutable"
    | Mutability.immutable => "immutable"

structure StateComponent where
  /-- Is this state component mutable or immutable? -/
  mutability : Mutability
  /-- Is this an `individual`, a `relation`, or ` function`?-/
  kind       : StateComponentKind
  name       : Name
  /-- The Lean syntax that declares the type of this state component -/
  type       : StateComponentType
  /-- If it is an inherited module, the name of this module -/
  moduleName : Option Name := none
deriving Inhabited

instance : ToString StateComponent where
  toString sc := s!"{sc.mutability} {sc.kind} {sc.name} {sc.type}"

def StateComponent.isMutable (sc : StateComponent) : Bool := sc.mutability == Mutability.mutable
def StateComponent.isImmutable (sc : StateComponent) : Bool := sc.mutability == Mutability.immutable

def StateComponent.getSimpleBinder (sc : StateComponent) : CoreM (TSyntax ``Command.structSimpleBinder) := do
  match sc.type with
  | .simple t => return t
  | .complex b d => return ← complexBinderToSimpleBinder (mkIdent sc.name) b d

def StateComponent.stx (sc : StateComponent) : CoreM Syntax := sc.getSimpleBinder

def StateComponent.typeStx (sc : StateComponent) : CoreM Term := sc.type.stx

structure StateSpecification where
  name : Name
  /-- DSL expression for this predicate -/
  lang : Option (TSyntax ``Term.doSeq)
  /-- Lean `Expr` for this predicate; this is usually a constant in the
  environment, *without* having applied the section variables. -/
  expr : Expr
deriving Inhabited, BEq

instance : ToString StateSpecification where
  toString sp := match sp.lang with
    | some lang => s!"{sp.name} : {lang}"
    | none => s!"{sp.name} : {sp.expr}"

structure ProcedureDeclaration where
  name: Lean.Name
  ctor : Option (TSyntax `Lean.Parser.Command.ctor)
deriving BEq, Inhabited


inductive ProcedureKind
  /-- Callable by the environment -/
  | action (decl : ActionDeclaration)
  /-- Not callable by the environment -/
  | procedure (decl : ProcedureDeclaration)
deriving Inhabited, BEq

def ProcedureKind.isAction (kind : ProcedureKind) : Bool :=
  match kind with
  | .action _ => true
  | .procedure _ => false

def ProcedureKind.actionDecl (kind : ProcedureKind) : Option ActionDeclaration :=
  match kind with
  | .action decl => some decl
  | .procedure _ => none

def ProcedureKind.procedureDecl (kind : ProcedureKind) : Option ProcedureDeclaration :=
  match kind with
  | .action _ => none
  | .procedure decl => some decl

structure ProcedureSpecification where
  kind : ProcedureKind
  /-- DSL expression for this action -/
  lang : Option (TSyntax ``Term.doSeq)
  /-- DSL expression for the specificarion of this action -/
  spec : Option (TSyntax ``Term.doSeq)
  /-- Arguments of the current action -/
  br   : Option (TSyntax ``Lean.explicitBinders) := none
  /-- Lean `Expr` for this action; this is usually a constant in the
  environment, *without* having applied the section variables. -/
  expr : Expr
deriving Inhabited, BEq

instance : ToString ProcedureSpecification where
  toString a := match a.kind with
    | .action decl => match a.lang with
      | some lang => s!"{decl.kind} {decl.name} [defined via lang] {lang}"
      | none => s!"{decl.kind} {decl.name} [defined via expr] {a.expr}"
    | .procedure decl => match a.lang with
      | some lang => s!"procedure {decl.name} [defined via lang] {lang}"
      | none => s!"procedure {decl.name} [defined via expr] {a.expr}"

def ProcedureSpecification.kindString (proc : ProcedureSpecification) : String :=
  match proc.kind with
  | .action _ => "action"
  | .procedure _ => "procedure"

def ProcedureSpecification.actionDecl (proc : ProcedureSpecification) : Option ActionDeclaration :=
  match proc.kind with
  | .action decl => some decl
  | .procedure _ => none

def ProcedureSpecification.hasSpec (proc : ProcedureSpecification) : Bool :=
  proc.spec.isSome

/-- Make an action specification without any DSL-specific information. -/
def ActionSpecification.mkPlain (type : ActionKind) (name : Name) (expr : Expr) : ProcedureSpecification := {
  kind := .action { kind := type, name := name, ctor := none },
  lang := none,
  spec := none,
  expr := expr
}

/-- Make a procedure specification without any DSL-specific information. -/
def ProcedureSpecification.mkPlain (name : Name) (expr : Expr) : ProcedureSpecification := {
  kind := .procedure { name := name, ctor := none },
  lang := none,
  spec := none,
  expr := expr
}

/-- Enhance a given `ActionSpecification` with DSL-specific information. -/
def ProcedureSpecification.addDSLInfo (a : ProcedureSpecification) (lang : TSyntax ``Term.doSeq) (ctor : TSyntax `Lean.Parser.Command.ctor) : ProcedureSpecification :=
  match a.kind with
  | .action decl => { a with lang := some lang, kind := .action { decl with ctor := some ctor } }
  | .procedure decl => { a with lang := some lang, kind := .procedure { decl with ctor := some ctor } }

def ProcedureSpecification.name (a : ProcedureSpecification) : Name :=
  match a.kind with
  | .action decl => decl.name
  | .procedure decl => decl.name

def ProcedureSpecification.label (a : ProcedureSpecification) : Option (ActionLabel Name) :=
  match a.kind with
  | .action decl => some decl.label
  | .procedure _ => none

/-- `invariant` and `safety` mean the same thing, but `safety` is as a
convention used to denote the main, top-level properties of the system,
whereas `invariant` clauses are supporting the main safety property. -/
inductive StateAssertionKind
  | assumption
  | invariant
  /-- An invariant is different from an assumption in that it can refer
  to `mutable` state. It still gets collected into the `assumptions`
  definitions, however. -/
  | trustedInvariant
  | safety
deriving BEq, Hashable

instance : Inhabited StateAssertionKind where
  default := StateAssertionKind.invariant

instance : ToString StateAssertionKind where
  toString
    | StateAssertionKind.assumption => "assumption"
    | StateAssertionKind.invariant => "invariant"
    | StateAssertionKind.trustedInvariant => "trusted invariant"
    | StateAssertionKind.safety => "safety"

structure StateAssertion where
  kind : StateAssertionKind
  name : Name
  /-- Set of isolates that were open when this invariant was defined -/
  isolates : List Name := []
  /-- Lean term for this predicate -/
  term : Option (TSyntax `term)
  /-- Lean `Expr` for this predicate; this is usually a constant in the
  environment, *without* having applied the section variables. -/
  expr : Expr
deriving Inhabited, BEq

structure IsolatesInfo where
  /-- Set of isolates opened at the moment -/
  openIsolates : List Name
  /-- Mapping from isolates to their invariants -/
  isolateStore : Std.HashMap Name (Std.HashSet Name)
deriving Inhabited

instance : ToString StateAssertion where
  toString sa := match sa.term with
    | some term => s!"{sa.kind} [{sa.name}] {term}"
    | none => s!"{sa.kind} [{sa.name}] {sa.expr}"


/-- Modules can depend on other modules, which must be fully-instantiated with
type (and typeclass) arguments provided for all variables. -/
structure ModuleDependency where
  name       : Name
  /-- Module parameters-/
  parameters : Array (TSyntax `Lean.Parser.Term.bracketedBinder)
  /-- Instantiations of the module's parameters, i.e. the arguments
  passed to the module when it is instantiated. -/
  arguments  : Array Term

abbrev Alias := Name

/-- A cleaned-up version of `StsState`, this gets generated on `#gen_spec` and stored in the global state. -/
structure ModuleSpecification : Type where
  /-- Name of the specification -/
  name         : Name
  /-- Parameters of this module : type variables and typeclass variables. -/
  parameters   : Array (TSyntax `Lean.Parser.Term.bracketedBinder)
  /-- Modules that this module depends on (instantiates) -/
  dependencies : Array (Alias × ModuleDependency)
  /-- Expression representing the type of the transition system state,
  *without* having applied the section variables. -/
  stateType    : Expr
  /-- Expression representing the syntax type of the transition system state,
  *with* having applied the section variables. -/
  stateStx     : Term
  /-- Signatures of all constants, relations, and functions that compose
  the state. This basically defines a FOL signature. -/
  signature    : Array StateComponent
  /-- Axioms/assumptions that hold on the signature. Every state
  component mentioned in an axiom must be marked `immutable`. -/
  assumptions  : Array StateAssertion
  /-- Initial state predicate -/
  init         : StateSpecification
  /-- Procedures of the system, some of which are marked as `action`s,
  i.e. procedures that can be called by the environment. -/
  procedures    : Array ProcedureSpecification
  /-- Invariants -/
  invariants   : Array StateAssertion
deriving Inhabited

/-- Syntax for the arguments of this module. Typeclasses that are not named are
replaced with `_`, to be inferred. -/
def ModuleSpecification.arguments [Monad m] [MonadError m] [MonadQuotation m] (spec : ModuleSpecification) : m (Array Term) :=
  bracketedBindersToTerms spec.parameters

def ModuleSpecification.getStateComponent (spec : ModuleSpecification) (name : Name) : Option StateComponent :=
  spec.signature.find? (fun sc => sc.name == name)

def ModuleSpecification.getStateComponentTypeStx (spec : ModuleSpecification) (name : Name) : CoreM (Option Term) := do
  match spec.getStateComponent name with
  | some sc => return some (← sc.typeStx)
  | none => return none

def ModuleSpecification.immutableComponents (spec : ModuleSpecification) : Array StateComponent :=
  spec.signature.filter (fun sc => sc.isImmutable)

def ModuleSpecification.mutableComponents (spec : ModuleSpecification) : Array StateComponent :=
  spec.signature.filter (fun sc => sc.isMutable)

/-- Actions are those procedures that can be called by the environment. -/
def ModuleSpecification.actions (spec : ModuleSpecification) : Array ProcedureSpecification :=
  spec.procedures.filter (fun proc => match proc.kind with
    | .action _ => true
    | .procedure _ => false)

/-- Every DSL-specified transition gets a 'constructor' that corresponds
to the transition's signature. This is used to build up a `Label` type
for this specification, which encodes its IO Automata signature. -/
def ModuleSpecification.transitionCtors (spec : ModuleSpecification) : CoreM (Array (TSyntax `Lean.Parser.Command.ctor)) := do
  spec.procedures.mapM (fun t => do match t.kind with
    | .action decl => match decl.ctor with
      | some ctor => return ctor
      | none => throwError "DSL: missing constructor for transition {t.name}"
    | .procedure _ => throwError "DSL: missing constructor for procedure {t.name}"
  )

instance : ToString ModuleSpecification where
  toString spec := s!"ModuleSpecification {spec.name}"
