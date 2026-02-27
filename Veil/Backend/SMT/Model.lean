import Lean
import Smt
import ProofWidgets.Compat
import Veil.Frontend.DSL.Module.Util.Basic

/-! ## Helper Functions -/

/-- Check if an expression is the `Nat` type. -/
def Lean.Expr.isNat (e : Lean.Expr) : Bool :=
  e.isConstOf ``Nat

/-- Check if an expression is the `Int` type. -/
def Lean.Expr.isInt (e : Lean.Expr) : Bool :=
  e.isConstOf ``Int

namespace Veil
open Lean Elab Meta Smt

private def runModelMeta (ctx : ModelContext) (expr : Expr) (f : Expr → MetaM α) : IO α :=
  ({ ci := ctx.ci, lctx := ctx.lctx, linsts := ctx.linsts, expr } : ProofWidgets.ExprWithCtx).runMetaM f

/-- Enum sort adaptation metadata used to convert between SMT `Fin`-based
representations and user-facing enum concrete types. -/
structure EnumSortAdaptation where
  /-- Type used by SMT (typically `Fin n`). -/
  smtType : Expr
  /-- Enum concrete type (e.g. `LocType_IndT`). -/
  enumType : Expr
  /-- Mapping from SMT index to enum constructor expression. -/
  indexToCtor : Array (Nat × Expr)

/-- Evaluate an expression to JSON by dynamically synthesizing the `ToJson`
instance. This function works without knowing the type at compile time. -/
unsafe def evalExprToJson (typeExpr : Expr) (valueExpr : Expr) : MetaM Json := do
  let toJsonType ← Meta.mkAppM ``ToJson #[typeExpr]
  let toJsonInst ← Meta.synthInstance toJsonType
  let jsonExpr ← Meta.mkAppOptM ``toJson #[some typeExpr, some toJsonInst, some valueExpr]
  Meta.evalExpr Json (mkConst ``Json) jsonExpr

/-- Extract a Nat value from a Fin expression.
    Handles `OfNat.ofNat α n inst` and `Fin.mk bound val proof` forms. -/
def extractFinValue (ctx : ModelContext) (e : Expr) : IO (Option Nat) :=
  runModelMeta ctx e fun e => do
    let e ← Meta.whnf e
    -- Check if it's a Nat literal directly
    if let .lit (.natVal n) := e then
      return some n
    let args := e.getAppArgs
    -- Check if it's OfNat.ofNat α n inst - value is at index 1
    if e.isAppOf ``OfNat.ofNat && args.size >= 2 then
      let valArg ← Meta.whnf args[1]!
      if let .lit (.natVal n) := valArg then
        return some n
    -- Check if it's Fin.mk bound val proof - value is at index 1
    if e.isAppOf ``Fin.mk && args.size >= 2 then
      let valArg ← Meta.whnf args[1]!
      if let .lit (.natVal n) := valArg then
        return some n
    return none

private def mkSmtNatLiteral (smtType : Expr) (n : Nat) : MetaM Expr :=
  Meta.mkAppOptM ``OfNat.ofNat #[some smtType, some (mkNatLit n), none]

private def mkIte (resultType cond thenExpr elseExpr : Expr) : MetaM Expr :=
  Meta.mkAppOptM ``ite #[some resultType, some cond, none, some thenExpr, some elseExpr]

private def findEnumAdaptation? (enumAdapts : Array EnumSortAdaptation)
    (sourceType targetType : Expr) : MetaM (Option EnumSortAdaptation) := do
  for adapt in enumAdapts do
    if (← Meta.isDefEq sourceType adapt.smtType) && (← Meta.isDefEq targetType adapt.enumType) then
      return some adapt
  return none

private def findReverseEnumAdaptation? (enumAdapts : Array EnumSortAdaptation)
    (sourceType targetType : Expr) : MetaM (Option EnumSortAdaptation) := do
  for adapt in enumAdapts do
    if (← Meta.isDefEq sourceType adapt.enumType) && (← Meta.isDefEq targetType adapt.smtType) then
      return some adapt
  return none

private def convertSmtToEnum? (smtExpr smtType enumType : Expr)
    (enumAdapts : Array EnumSortAdaptation) : MetaM (Option Expr) := do
  let some adapt ← findEnumAdaptation? enumAdapts smtType enumType | return none
  let some (_, fallbackCtor) := adapt.indexToCtor[0]? | return none
  let mut converted := fallbackCtor
  for (idx, ctorExpr) in adapt.indexToCtor.reverse do
    let idxExpr ← mkSmtNatLiteral adapt.smtType idx
    let cond ← Meta.mkEq smtExpr idxExpr
    converted ← mkIte adapt.enumType cond ctorExpr converted
  return some converted

private def convertEnumToSmt? (enumExpr enumType smtType : Expr)
    (enumAdapts : Array EnumSortAdaptation) : MetaM (Option Expr) := do
  let some adapt ← findReverseEnumAdaptation? enumAdapts enumType smtType | return none
  let some (fallbackIdx, _) := adapt.indexToCtor[0]? | return none
  let mut converted ← mkSmtNatLiteral adapt.smtType fallbackIdx
  for (idx, ctorExpr) in adapt.indexToCtor.reverse do
    let idxExpr ← mkSmtNatLiteral adapt.smtType idx
    let cond ← Meta.mkEq enumExpr ctorExpr
    converted ← mkIte adapt.smtType cond idxExpr converted
  return some converted

/-- Convert an SMT model function to match the expected Lean type.

  SMT models may convert types during embedding:
  - `Bool` → `Prop`
  - `Nat` → `Int`

  This function adapts the SMT expression back to the expected type by inserting
  appropriate conversions for both arguments and return types.

  For example:
  - A relation `r : node → Bool → Bool` might be returned as `r_smt : node → Prop → Prop`
  - A function `f : Nat → Nat` might be returned as `f_smt : Int → Int`

  TODO: upstream this to `lean-smt` -/
def adaptSmtExprType (smtExpr : Expr) (expectedType : Expr)
    (enumAdapts : Array EnumSortAdaptation := #[]) : MetaM Expr := do
  -- Reduce types for accurate comparison
  let expectedType ← Meta.reduceAll expectedType
  let smtType ← Meta.reduceAll (← Meta.inferType smtExpr)

  if ← Meta.isDefEq smtType expectedType then
    return smtExpr

  Meta.forallTelescope expectedType fun expectedArgs expectedRetTy =>
  Meta.forallTelescope smtType fun smtArgs smtRetTy => do
    let smtArgTypes ← smtArgs.mapM fun smtArg => do
      Meta.reduceAll (← Meta.inferType smtArg)

    -- Build application, converting args where needed
    let mut app := smtExpr
    for i in [:expectedArgs.size] do
      let arg := expectedArgs[i]!
      let argTy ← Meta.reduceAll (← Meta.inferType arg)
      let smtArgTy := smtArgTypes[i]!
      let convertedArg ←
        -- Bool → Prop: convert `b` to `b = true`
        if argTy.isBool && smtArgTy.isProp then
          Meta.mkAppM ``Eq #[arg, mkConst ``Bool.true]
        -- Nat → Int: convert via `Int.ofNat`
        else if argTy.isNat && smtArgTy.isInt then
          Meta.mkAppM ``Int.ofNat #[arg]
        -- Enum concrete type → SMT sort (typically `Fin n`)
        else if let some converted ← convertEnumToSmt? arg argTy smtArgTy enumAdapts then
          pure converted
        else
          pure arg
      app := mkApp app convertedArg

    -- Convert return type if needed
    let result ←
      -- Prop → Bool: use `decide`
      if expectedRetTy.isBool && smtRetTy.isProp then
        Meta.mkAppOptM ``decide #[some app, none]
      -- Int → Nat: use `Int.toNat` (returns 0 for negative values, but SMT model
      -- should always return valid non-negative values for Nat-typed results)
      else if expectedRetTy.isNat && smtRetTy.isInt then
        Meta.mkAppM ``Int.toNat #[app]
      -- SMT sort (typically `Fin n`) → enum concrete type
      else if let some converted ← convertSmtToEnum? app smtRetTy expectedRetTy enumAdapts then
        pure converted
      else
        pure app

    Meta.mkLambdaFVars expectedArgs result

end Veil
