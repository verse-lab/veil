import Veil.Frontend.DSL.Module.Util.Assertions
import Veil.Util.ReplacingInstances
import Veil.Util.Meta

open Lean Parser Elab Command Term Meta Tactic

namespace Veil

/-! ## Abstract-State Utilities -/

def Module.toAbstractStateBodyStx (mod : Module) (scrutinee abstractStateSortTerm : Term) : TermElabM Term := do
  mod.withTheoryAndStateTermTemplate
    [(.state .none "_conc", scrutinee, false)]
    (some (← `($stateIdent $abstractStateSortTerm)))
    (fun _ stateFields => `(⟨$[$stateFields],*⟩))

/-- A meta-level construction for turning a `x : State χ` into
`State FieldAbstractType`. -/
def Module.toAbstractStateFun (mod : Module) (abstractStateSortTerm : Term)
    (stateType abstractStateTypeExpr : Expr) : TermElabM Expr := do
  let stIdent := mkVeilImplementationDetailIdent `st
  let body ← mod.toAbstractStateBodyStx stIdent abstractStateSortTerm
  let argTy ← `($stateIdent $fieldConcreteType)
  let funTerm ← `(fun ($stIdent : $argTy) => $body)
  let funTypeExpr ← mkArrow stateType abstractStateTypeExpr
  withoutErrToSorry $ elabTermAndSynthesize funTerm (some funTypeExpr)

def Module.getAbstractStateRelated (mod : Module) (stateType : Expr) : TermElabM (Term × Expr × Expr) := do
  let sortIdents ← mod.uninterpretedParamIdents
  -- NOTE: If possible, the following should be changed into `Expr`-level manipulation
  let abstractStateSortTerm ← `($fieldAbstractDispatcher $sortIdents*)
  let abstractStateSortExpr ← withoutErrToSorry $ elabTermAndSynthesize abstractStateSortTerm none
  -- kind of hacky here
  let abstractStateTypeExpr := mkApp stateType.getAppFn' abstractStateSortExpr
  pure (abstractStateSortTerm, abstractStateSortExpr, abstractStateTypeExpr)

/-- Parameters that are introduced only to quantify over a concrete
theory/state/field-representation environment.

When a generated artifact has already been specialized to the module's
abstract state, these parameters should usually disappear from the saved
definition/theorem interface; keeping them around exposes irrelevant plumbing
such as `ρ`, `σ`, `χ`, `IsSubStateOf`, `IsSubReaderOf`, and field
representation instances. -/
def isAbstractStateLocalParam (p : Parameter) : Bool :=
  match p.kind with
  | .backgroundTheory | .environmentState | .fieldConcreteType => true
  | .moduleTypeclass .fieldRepresentation
  | .moduleTypeclass .lawfulFieldRepresentation
  | .moduleTypeclass .environmentState
  | .moduleTypeclass .backgroundTheory => true
  | _ => false

/-- Filter an argument array using the corresponding `Parameter` metadata. -/
def filterArgsByParams [Monad m] (params : Array Parameter) (args : Array α)
    (keep : Parameter → α → m Bool) : m (Array α) := do
  let args ← params.zipWithM (bs := args) fun p arg => do
    if ← keep p arg then pure (some arg) else pure none
  pure <| args.filterMap id

private def isDecidableType (ty : Expr) : Bool :=
  ty.getForallBody.getAppFn'.isConstOf ``Decidable

def isDecidableDefParameter (p : Parameter) (v : Expr) : MetaM Bool := do
  match p.kind with
  | .definitionParameter _ .typeclass =>
    let ty ← inferType v
    pure <| isDecidableType ty
  | _ => pure false

def specializeArgForStateχ (p : Parameter) (v theoryType stateType : Expr) : TermElabM (Option Expr) := do
  match p.kind with
  | .backgroundTheory => pure <| some theoryType        -- NOTE: Without this, there seems to be some unification issue
  | .environmentState => pure <| some stateType
  | .moduleTypeclass .backgroundTheory | .moduleTypeclass .environmentState => pure none
  | _ => if ← isDecidableDefParameter p v then pure none else pure <| some v

def specializeArgsForStateχ (params : Array Parameter) (args : Array Expr)
    (theoryType stateType : Expr) : TermElabM (Array (Option Expr)) := do
  unless params.size == args.size do
    throwError "specializeArgsForStateχ: parameter/argument length mismatch"
  params.zipWithM (bs := args) fun p v =>
    specializeArgForStateχ p v theoryType stateType

def specializeArgForStateAbstract (p : Parameter) (v theoryType abstractStateTypeExpr abstractStateSortExpr : Expr)
    : TermElabM (Option Expr) := do
  match p.kind with
  | .backgroundTheory => pure <| some theoryType
  | .environmentState => pure <| some abstractStateTypeExpr
  | .fieldConcreteType => pure <| some abstractStateSortExpr
  | .moduleTypeclass .fieldRepresentation
  | .moduleTypeclass .lawfulFieldRepresentation
  | .moduleTypeclass .backgroundTheory
  | .moduleTypeclass .environmentState => pure none
  | _ => if ← isDecidableDefParameter p v then pure none else pure <| some v

def specializeArgsForStateAbstract (params : Array Parameter) (args : Array Expr)
    (theoryType abstractStateTypeExpr abstractStateSortExpr : Expr) : TermElabM (Array (Option Expr)) := do
  unless params.size == args.size do
    throwError "specializeArgsForStateAbstract: parameter/argument length mismatch"
  params.zipWithM (bs := args) fun p v =>
    specializeArgForStateAbstract p v theoryType abstractStateTypeExpr abstractStateSortExpr

/-- Try to prove equality after replacing runtime `Decidable` arguments by
`Classical.propDecidable`. This is intentionally proof-producing so callers can
compose it with simplification proofs instead of relying on a tactic side
effect. -/
def proveEqModuloDecidableInstances? (e1 e2 : Expr) : MetaM (Option Expr) := do
  let e1 ← whnf e1
  let e2 ← whnf e2
  let r1 ← (Simp.simp #[``Veil.Util.neutralizeDecidableInstGeneral]) e1
  let r2 ← (Simp.simp #[``Veil.Util.neutralizeDecidableInstGeneral]) e2
  if ← withBackwardsCompatibility (isDefEq r1.expr r2.expr) then
    -- Return the proof that `e1` = `e2`
    -- `r1.proof : e1 = r1.expr, r2.proof : e2 = r2.expr`
    -- So `Eq.trans (r1.proof) (Eq.symm (r2.proof)) : e1 = e2`
    let pf1 ← r1.getProof
    let pf2 ← r2.getProof >>= mkEqSymm
    return some (← mkEqTrans pf1 pf2)
  return none

def isDefEqModuloDecidableInstances (e1 e2 : Expr) : MetaM (Option <| Option Expr) := do
  if ← withBackwardsCompatibility (isDefEq e1 e2) then
    return some none
  match ← proveEqModuloDecidableInstances? e1 e2 with
  | some pf => return some (some pf)
  | none => return none

end Veil
