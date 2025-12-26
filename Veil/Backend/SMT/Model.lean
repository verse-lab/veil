import Lean
import Smt
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
def adaptSmtExprType (smtExpr : Expr) (expectedType : Expr) : MetaM Expr := do
  -- Reduce types for accurate comparison
  let expectedType ← Meta.reduceAll expectedType
  let smtType ← Meta.reduceAll (← Meta.inferType smtExpr)

  if ← Meta.isDefEq smtType expectedType then
    return smtExpr

  Meta.forallTelescope expectedType fun expectedArgs expectedRetTy =>
  Meta.forallTelescope smtType fun smtArgs smtRetTy => do
    let smtArgTypes ← smtArgs.mapM Meta.inferType

    -- Build application, converting args where needed
    let mut app := smtExpr
    for i in [:expectedArgs.size] do
      let arg := expectedArgs[i]!
      let argTy ← Meta.inferType arg
      let smtArgTy := smtArgTypes[i]!
      let convertedArg ←
        -- Bool → Prop: convert `b` to `b = true`
        if argTy.isBool && smtArgTy.isProp then
          Meta.mkAppM ``Eq #[arg, mkConst ``Bool.true]
        -- Nat → Int: convert via `Int.ofNat`
        else if argTy.isNat && smtArgTy.isInt then
          Meta.mkAppM ``Int.ofNat #[arg]
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
      else
        pure app

    Meta.mkLambdaFVars expectedArgs result

end Veil
