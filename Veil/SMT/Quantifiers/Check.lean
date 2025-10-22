import Lean
import Batteries.Lean.Meta.UnusedNames
import Lean.Util.ForEachExpr

import Veil.Base
import Veil.Util.DSL
import Veil.SMT.Preparation
import Veil.Util.Quantifiers

open Lean Meta Elab Tactic

variable {n : Type → Type}  [Monad n] [MonadControlT MetaM n] [MonadLiftT MetaM n]

namespace Veil

private def higherOrderQuantifiedTypes' (e : Expr) (existentialOnly? : Bool := false) : QuantElimM (n := n) (Array (QuantType × Name × Expr)) := do
  let _ ← forEachExprSane e (fun e => do
    match e with
    | Expr.forallE nm t _ _ => if !existentialOnly? then recordTypeIfHigherOrder .forall nm t else pure ()
    | _ => match_expr e with
      | Exists t tlam =>
        let name :=
          if let .lam nm _ _ _ := tlam then nm
          else Name.anonymous
        recordTypeIfHigherOrder .exists name t
      | _ => pure ()
  )
  let res := (← get).quantifiedTypes.toArray
  return res
  where recordTypeIfHigherOrder (qt : QuantType ) (nm : Name) (e : Expr) : QuantElimM (n := n) Unit := do
    if ← isHigherOrder e then
      modify (fun s => { s with quantifiedTypes := (qt, nm, e) :: s.quantifiedTypes })

def higherOrderQuantifiers (e : Expr) (existentialOnly? : Bool := false) : n (Array (QuantType × Name × Expr)) := do
  let (types, _st) ← (higherOrderQuantifiedTypes' e existentialOnly?).run default
  return types

def hasHigherOrderQuantification (e : Expr) (existentialOnly? : Bool := false) : n Bool := do
  return (← higherOrderQuantifiers e existentialOnly?).size > 0

def getHOQuat (e : Expr) (mode : checkMode := .hypothesis) : n (Array (QuantType × Name × Expr)) :=
  quantMetaTelescopeReducing e mode fun _ => higherOrderQuantifiers

def logHOQuantsErorrs (hoqs : Array (QuantType × Name × Expr)) (pos : Option Name := none) : TacticM Unit := do
  let loc := match pos with
    | some n => s!"hypotesis {n}"
    | none => "the goal"
  for q in hoqs do
    logError s!"Higher-order quantification in {loc} detected: {q.1} {q.2.1} : {q.2.2}"

def goalSmTTranslatable? : TacticM Unit := do
    let quants <- getHOQuat (<- getMainTarget) .goal
    logHOQuantsErorrs quants
    for h in (<- getLCtx) do
      unless h.isImplementationDetail do
        let quants <- getHOQuat h.type .hypothesis
        logHOQuantsErorrs quants h.userName

elab "is_translatable_to_smt?" : tactic => goalSmTTranslatable?

end Veil
