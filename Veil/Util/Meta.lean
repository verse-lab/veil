import Lean
open Lean Elab Command

/-! # Meta-programming utility functions

  This file contains utility functions for doing meta-programming in
  Lean, especially around manipulating syntax.
-/

def Lean.Expr.isBool (e : Expr) : Bool := e.isConstOf `Bool
def Lean.TSyntax.isApp? (stx : Term) : Option (Ident × Array Term) := do
  let #[f, args] := stx.raw.getArgs | failure
  let `(term| $f:ident) := f | failure
  return (⟨f⟩, args.getArgs.map (⟨·⟩))

/-- Like `getForallArity`, but only counts the number of `default`
(i.e. explicit) binders. -/
partial def Lean.Expr.getForallArityExplicitBinders : Expr → Nat
  | .mdata _ b       => getForallArityExplicitBinders b
  | .forallE _ _ b bi => getForallArityExplicitBinders b + (if bi.isExplicit then 1 else 0)
  | e                =>
    if e.isHeadBetaTarget then
      getForallArityExplicitBinders e.headBeta
    else
      let e' := e.cleanupAnnotations
      if e != e' then getForallArityExplicitBinders e' else 0

/-- Like `Meta.mkLambdaFVars`, but makes all `default` binders implicit. -/
def Lean.Meta.mkLambdaFVarsImplicit (vs : Array Expr) (e : Expr) (usedOnly : Bool := false) (usedLetOnly : Bool := true) (etaReduce : Bool := false) (binderInfoForMVars := BinderInfo.implicit) : TermElabM Expr := do
  let e <- Meta.mkLambdaFVars vs e usedOnly usedLetOnly etaReduce binderInfoForMVars
  return go vs.size e
  where go (cnt : Nat) (e : Expr) : Expr :=
    match cnt, e with
    | 0, _ => e
    | _, Expr.lam n d b .default =>
      let b := go (cnt-1) b
      Expr.lam n d b .implicit
    | _, Expr.lam n d b bi =>
      let b := go (cnt-1) b
      Expr.lam n d b bi
    | _, _ => e

namespace Veil

/-- Syntax for `∀ a₀ a₁ .. aₙ, Decidable (P a₀ a₁ .. aₙ)`. -/
def decidableNStx [Monad m] [MonadError m] [MonadQuotation m] (n : Nat) (relName : Name) : m Term := do
  let idents := (Array.range n).map fun i => mkIdent $ Name.mkSimple s!"a{i}"
  if n == 0 then
    `(term| $(mkIdent ``Decidable) ($(mkIdent relName)))
  else
    `(term| ∀ $idents*, $(mkIdent ``Decidable) ($(mkIdent relName) $idents*))

def mkVeilImplementationDetailName (n : Name) : Name :=
  Name.mkSimple s!"__veil_{n}"

def isVeilImplementationDetailName (n : Name) : Bool :=
  n.isStr && n.toString.startsWith "__veil_"

def addVeilDefinitionAsync (n : Name) (e : Expr)
  (red := Lean.ReducibilityHints.regular 0)
  (attr : Array Attribute := #[])
  (type : Option Expr := none) : TermElabM Unit := do
  addDecl <|
    Declaration.defnDecl <|
      mkDefinitionValEx n [] (type.getD <| ← Meta.inferType e) e red
      (DefinitionSafety.safe) []
  Elab.Term.applyAttributes n attr

def addVeilDefinition (n : Name) (e : Expr)
  (red := Lean.ReducibilityHints.regular 0)
  (attr : Array Attribute := #[])
  (type : Option Expr := none) : TermElabM Unit := do
  addVeilDefinitionAsync n e red attr type
  enableRealizationsForConst n

/-- A wrapper around Lean's standard `elabCommand`, which performs
Veil-specific logging and sanity-checking. -/
def elabVeilCommand (stx : Syntax) : CommandElabM Unit := do
  trace[veil.debug] "{stx}"
  elabCommand stx

/--
  Veil actions, in order to be executable, need to have `Decidable`
  instances available for all the predicates that feed into `require`,
  `assert`, or `assume` statements, as well as `if` conditions.

  This function is a version of `elabTerm` that returns _both_ an
  `Array` of metavariables, whose types consist of all the predicates
  that need to be `Decidable` for this action to be executable, and the
  elaborated term itself.
-/
def elabTermDecidable (stx : Term) : TermElabM (Array Expr × Expr) := do
  /- We want to throw an error if anything fails or is missing during
  elaboration. -/
  Term.withoutErrToSorry $ do
  withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) do
  let e ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVars
  let mvars ← (Array.map Expr.mvar) <$> Meta.getMVars e
  let mvars' ← mvars.filterMapM (simplifyMVarType · isDecidableInstance)
  let e ← instantiateMVars e
  return (mvars', e)
where
  isDecidableInstance (body : Expr) : TermElabM Bool := do
    let body ← Meta.whnf body
    let res := match body.getAppFn.constName? with
    | .some n => n == ``Decidable
    | .none => false
    return res
  /-- `mv`'s type will include arguments which are not actually needed
  for the predicate. This method gets rid of those unnecessary
  arguments. Moreover, it only returns those `mv`ars whose final result
  type passes the given filter. -/
  simplifyMVarType (mv : Expr) (keepBodyIf : Expr → TermElabM Bool := fun _ => return true): TermElabM (Option Expr) := do
    let ty ← Meta.inferType mv
    Meta.forallTelescope ty fun ys body => do
      if !(← keepBodyIf body) then return none
      let simplified_type ← Meta.mkForallFVars ys (← Meta.whnf body) (usedOnly := true)
      -- Create a new mvar to replace the old one
      let decl ← mv.mvarId!.getDecl
      let mv' ← Meta.mkFreshExprMVar (.some simplified_type) (kind := decl.kind) (userName := ← mkFreshUserName `dec_pred)
      -- Assign the old mvar, to get rid of it
      let mv_pf ← do
        -- NOTE: `mkLambdaFVars` can behave unexpectedly when handling mvars
        -- (e.g., automatically applying them to the body); we workaround this
        -- by using a dummy fvar and then doing replacement
        Meta.withLocalDeclD decl.userName simplified_type fun z => do
          let tmp ← Meta.mkLambdaFVars ys $ mkAppN z (ys.filter fun y => y.occurs body)
          pure $ tmp.replaceFVar z mv'
      mv.mvarId!.assign mv_pf
      return .some mv'

/-- Given `nm : type`, return `type` -/
def getSimpleBinderType [Monad m] [MonadError m] (sig : TSyntax `Lean.Parser.Command.structSimpleBinder) : m (TSyntax `term) := do
  match sig with
  | `(Lean.Parser.Command.structSimpleBinder| $_:ident : $tp:term) => pure tp
  | _ => throwError s!"getSimpleBinderType: don't know how to handle {sig}"

/-- Create the syntax for something like `type1 → type2 → .. → typeN`, ending with `terminator`. -/
def mkArrowStx [Monad m] [MonadQuotation m] [MonadError m] (tps : List Term) (terminator : Option $ TSyntax `term := none) : m (TSyntax `term) := do
  match tps with
  | [] => if let some t := terminator then return t else throwError "empty list of types and no terminator"
  | [a] => match terminator with
    | none => `(term| $a)
    | some t => `(term| $a -> $t)
  | a :: as =>
    let cont ← mkArrowStx as terminator
    `(term| $a -> $cont)

/-- Given `nm`, `(r : Int) (v : vertex)` and `Prop`, return `nm : Int -> vertex -> Prop` -/
def complexBinderToSimpleBinder [Monad m] [MonadQuotation m] [MonadError m] (nm : TSyntax `ident) (br : TSyntaxArray `Lean.Parser.Term.bracketedBinder) (domT : TSyntax `term) : m (TSyntax `Lean.Parser.Command.structSimpleBinder) := do
  let types ← br.mapM fun m => match m with
    | `(bracketedBinder| ($_arg:ident : $tp:term)) => return tp
    | _ => throwError "Invalid binder syntax {br}"
  let typeStx ← mkArrowStx types.toList domT
  let simple ← `(Lean.Parser.Command.structSimpleBinder| $nm:ident : $typeStx)
  return simple

def binderIdentToIdent (bi : TSyntax ``binderIdent) : Ident :=
  match bi with
  | `(binderIdent|$i:ident) => i
  | _ => unreachable!

/-- Convert existential binders into function binders. -/
def toFunBinderArray [Monad m] [MonadError m] [MonadQuotation m] (stx : TSyntax `Lean.explicitBinders) : m (TSyntaxArray `Lean.Parser.Term.funBinder) :=
  match stx with
  | `(explicitBinders|$bs*) =>
    bs.flatMapM fun
      | `(bracketedExplicitBinders|($bis* : $tp)) =>
        bis.mapM fun bi =>
          let id := binderIdentToIdent bi
          `(Lean.Parser.Term.funBinder| ($id : $tp:term))
      | _ => throwError "unexpected syntax in explicit binder: {stx}"
  | _ => throwError "unexpected syntax in explicit binder: {stx}"

def Option.stxArrMapM [Monad m] [MonadError m] [MonadQuotation m] (o : Option (TSyntax α)) (f : TSyntax α → m (TSyntaxArray β)) : m (TSyntaxArray β) := do
  match o with
  | .some stx => f stx
  | .none => pure #[]

/-- Like `CommandElabM.liftTermElabM`, but also binds the given
binders. We use this instead of `runTermElabM`, since we don't want to
define section variables and thus pollute the environment (but rather
pass only the binders we care about on a as-needed basis.) -/
def liftTermElabMWithBinders (binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (x : Array Expr → TermElabM α) : CommandElabM α :=
  Elab.Command.liftTermElabM <| Term.elabBinders binders fun vs => x vs

/-- Like `throwErrorAt`, but if `stx` is `none`, use `getRef` instead. -/
def _root_.Lean.throwErrorAtOpt [Monad m] [MonadRef m] [MonadError m] (stx : Option Syntax) (msg : MessageData) : m α := do
  match stx with
  | .some stx => throwErrorAt stx msg
  | .none => throwErrorAt (← getRef) msg

scoped syntax (name := throwErrorAt') "throwErrorAt'" term:max ppSpace (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwErrorAt' $ref $msg:interpolatedStr) => `(Lean.throwErrorAtOpt $ref (m! $msg))
  | `(throwErrorAt' $ref $msg:term)            => `(Lean.throwErrorAtOpt $ref $msg)

/-- Is this identifier all capital letters and digits? We use this to
represent implicit universal quantification, i.e. `rel N` means `∀ n,
rel n`. -/
def isCapital (i : Lean.Syntax) : Bool :=
  i.getId.isStr && i.getId.toString.all (fun c => c.isUpper || c.isDigit)

end Veil
