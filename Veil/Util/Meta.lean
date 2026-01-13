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
  let e <- Meta.mkLambdaFVars vs e usedOnly usedLetOnly etaReduce (binderInfoForMVars := binderInfoForMVars)
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

def Lean.Elab.Attribute.mkStx [Monad m] [MonadQuotation m] (attr : Attribute) : m (TSyntax `Lean.Parser.Term.attrInstance) := do
  let kindStx ← match attr.kind with
    | AttributeKind.global => `(Lean.Parser.Term.attrKind| )
    | AttributeKind.local  => `(Lean.Parser.Term.attrKind| local)
    | AttributeKind.scoped => `(Lean.Parser.Term.attrKind| scoped)
  `(Lean.Parser.Term.attrInstance| $kindStx $(Lean.mkIdent attr.name):ident)

namespace Veil

declare_syntax_cat commands
syntax (command ppLine ppLine)* : commands
elab_rules : command
  | `(commands| $cmds:command*) => do
    for cmd in cmds do
      elabCommand cmd

def constructCommands (thms : Array (TSyntax `command)) : CoreM (TSyntax `commands) := `(commands| $[$thms]*)


def withTiming {m α} [Monad m] [MonadTrace m] [MonadOptions m] [MonadRef m] [MonadLiftT BaseIO m] [AddMessageContext m] (name : String) (tac : m α) : m α := do
  let startTime ← IO.monoMsNow; let res ← tac; let endTime ← IO.monoMsNow
  trace[veil.timing] s!"{name} took {endTime - startTime}ms"
  return res

/-- Syntax for `∀ a₀ a₁ .. aₙ, Decidable (P a₀ a₁ .. aₙ)`. -/
def decidableNStx [Monad m] [MonadError m] [MonadQuotation m] (n : Nat) (relName : Name) : m Term := do
  let idents := (Array.range n).map fun i => mkIdent $ Name.mkSimple s!"a{i}"
  if n == 0 then
    `(term| $(mkIdent ``Decidable) ($(mkIdent relName)))
  else
    `(term| ∀ $idents*, $(mkIdent ``Decidable) ($(mkIdent relName) $idents*))

def mkVeilImplementationDetailName (n : Name) : Name :=
  Name.mkSimple s!"__veil_{n}"

def mkVeilImplementationDetailIdent (n : Name) : Ident :=
  mkIdent $ mkVeilImplementationDetailName n

def isVeilImplementationDetailName (n : Name) : Bool :=
  n.isStr && n.toString.startsWith "__veil_"

/-- **If** `derivedStx` doesn't have an informative source span, inherit the
source span from `originalStx`. -/
def _root_.Lean.Syntax.inheritSourceSpanFrom (derivedStx : TSyntax α) (originalStx : Syntax) : TSyntax α :=
  let alreadyHaveInfo := match derivedStx.raw.getPos? with
  | .some pos => pos.byteIdx != 1 -- i.e. not the dummy position
  | .none => false
  if alreadyHaveInfo then
    derivedStx
  else
    ⟨derivedStx.raw.setInfo originalStx.getHeadInfo⟩

/-- Use this instead of `PrettyPrinter.delab` to get a correct
representation of Veil expressions. Without these options, the
delaboration might not correctly round-trip. -/
def delabVeilExpr (e : Expr) (withExplicitInstances? : Bool := false) := do
  let stx ← withOptions (applyOptions · veilPrettyPrinterOptions) $ PrettyPrinter.delab e
  return Syntax.inheritSourceSpanFrom stx (← getRef)
where
  veilPrettyPrinterOptions : Array (Name × DataValue) :=
    (if withExplicitInstances? then #[(`pp.explicit, .ofBool true), (`pp.instances, .ofBool true)] else #[]) ++
    #[(`pp.deepTerms, .ofBool true), (`pp.motives.all, .ofBool true), (`pp.universes, .ofBool true),
    (`pp.letVarTypes, .ofBool true), (`pp.funBinderTypes, .ofBool true), (`pp.structureInstanceTypes, .ofBool true)]
  applyOptions (s : Options) (opts : Array (Name × DataValue)) : Options :=
    opts.foldl (fun s (n, v) => s.insert n v) s

private def stxForVeilDefinition (red : ReducibilityHints) (attrs : Array Attribute) (baseName : Name) (type : Expr) (e : Expr) : TermElabM (TSyntax `command) := do
  let attrs ← attrs.mapM (·.mkStx)
  let attrs? ← if attrs.isEmpty then pure Option.none else pure $ .some $ ← `(Parser.Term.attributes| @[$attrs,*])
  let typeStx ← delabVeilExpr type
  let eStx ← delabVeilExpr e
  match red with
  | .regular _ =>
    `(command|$[$attrs?:attributes]? def $(mkIdent baseName) : $typeStx := $eStx)
  | .abbrev =>
    `(command|$[$attrs?:attributes]? abbrev $(mkIdent baseName) : $typeStx := $eStx)
  | .opaque =>
    `(command|$[$attrs?:attributes]? opaque $(mkIdent baseName) : $typeStx := $eStx)

/-- You MUST call `enableRealizationsForConst` and
`Elab.Term.applyAttributes` after calling this function and before the
elaborator ends. -/
def addVeilDefinitionAsync (n : Name) (e : Expr) (compile := true)
  (red := Lean.ReducibilityHints.regular 0)
  (attr : Array Attribute := #[])
  (type : Option Expr := none)
  (addNamespace : Bool := true)
  : TermElabM Name := do
  let type ← match type with
  | .some t => pure t
  | .none => Meta.inferType e
  let fullName ← if addNamespace then pure $ (← getCurrNamespace).append n else pure n
  let addFn := if compile then addAndCompile else addDecl
  addFn <|
    Declaration.defnDecl <|
      mkDefinitionValEx fullName [] type e red
      (DefinitionSafety.safe) []
  trace[veil.desugar] "{← stxForVeilDefinition red attr n type e}"
  return fullName

def addVeilDefinition (n : Name) (e : Expr) (compile := true)
  (red := Lean.ReducibilityHints.regular 0)
  (attr : Array Attribute := #[])
  (type : Option Expr := none)
  (addNamespace : Bool := true)
  : TermElabM Name := do
  let n ← addVeilDefinitionAsync n e compile red attr type addNamespace
  enableRealizationsForConst n
  Term.applyAttributes n attr
  return n

def addVeilTheorem (n : Name) (statement : Expr) (proof : Expr) (attr : Array Attribute := #[]) (addNamespace : Bool := true) : TermElabM Name := do
  let fullName ← if addNamespace then pure $ (← getCurrNamespace).append n else pure n
  let decl := Declaration.thmDecl (mkTheoremValEx fullName [] statement proof [])
  addDecl decl
  enableRealizationsForConst fullName
  Term.applyAttributes fullName attr
  return fullName

/-- A wrapper around Lean's standard `elabCommand`, which performs
Veil-specific logging and sanity-checking. -/
def elabVeilCommand (stx : Syntax) : CommandElabM Unit := do
  trace[veil.desugar] "{stx}"
  elabCommand stx

/-- Is this type a `Decidable` instance? -/
def isDecidableInstance (type : Expr) : TermElabM Bool := do
  let ty ← Meta.reduce (skipTypes := false) type
  Meta.forallTelescope ty fun _ body => do
    return (← Meta.whnf body).getAppFn.constName? == some ``Decidable

/-- Elaborates the term (ignoring typeclass inference failures) and
returns the set of `Decidable` instances needed to make it elaborate
correctly. -/
def getRequiredDecidableInstances (stx : Term) : TermElabM (Array (Term × Expr) × Expr) := do
  /- We want to throw an error if anything fails or is missing during
  elaboration. -/
  Term.withoutErrToSorry $ do
  -- We elaborate the `stx` ignoring typeclass inference failures, but ensuring we
  -- do synthesize all the metavariables that we can (not postponing them). This
  -- is to ensure the resulting expression is 'complete' (i.e. doesn't have holes,
  -- except for the `Decidable` instances, which will be passed explicitly).
  withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) do
  let e ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
  let mvars ← (Array.map Expr.mvar) <$> Meta.getMVars e
  let mvars' ← mvars.filterMapM (simplifyMVarType · isBodyDecidable)
  return (mvars', e)
where
  isBodyDecidable (body : Expr) : TermElabM Bool := do
    return (← Meta.whnf body).getAppFn.constName? == some ``Decidable
  /-- `mv`'s type will include arguments which are not actually needed
  for the predicate. This method gets rid of those unnecessary
  arguments. Moreover, it only returns those `mv`ars whose final result
  type passes the given filter. -/
  simplifyMVarType (mv : Expr) (keepBodyIf : Expr → TermElabM Bool := fun _ => return true): TermElabM (Option (Term × Expr)) := do
    let ty ← Meta.reduce (skipTypes := false) $ ← Meta.inferType mv
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
      -- IMPORTANT: the type might have _delayed assignment metavariables_ if an
      -- assertion (which has default argument values provided by
      -- `veil_exact_theory` and `by veil_exact_state`) appears under a binder
      -- (e.g. `∀` quantification). We don't handle this, so we throw an error.
      let tyMVars ← Meta.getMVars simplified_type
      if !tyMVars.isEmpty then
        throwError "(type still has mvars after simplification):\n{simplified_type}"
      let tyStx ← delabVeilExpr simplified_type
      -- trace[veil.debug] "simplifyMVarType {mv}:\n{ty}\n~~> {simplified_type}"
      return (tyStx, mv')

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
  let (decInsts, e) ← getRequiredDecidableInstances stx
  let mvars := decInsts.map (fun (_tyStx, mv) => mv)
  let e ← instantiateMVars e
  return (mvars, e)

/-- Given `nm : type`, return `type` -/
def getSimpleBinderType [Monad m] [MonadError m] (sig : TSyntax `Lean.Parser.Command.structSimpleBinder) : m (TSyntax `term) := do
  match sig with
  | `(Lean.Parser.Command.structSimpleBinder| $_:ident : $tp:term) => pure tp
  | _ => throwError s!"getSimpleBinderType: don't know how to handle {sig}"

/-- Given `t : type1 → type2 → .. → typeN → codomain`,
    return `([type1, type2, .., typeN], codomain)`.
    Best efforts. A better way would be to use elaboration. -/
partial def splitForallArgsCodomain [Monad m] [MonadError m] [MonadQuotation m] (t : Term) : m (Array Term × Term) := do
  let rec go (t : Term) (acc : Array Term) : m (Array Term × Term) := do
    match t with
    | `(term| $a → $b) | `(term| [$_:ident : $a] → $b) | `(term| [$a:term] → $b)
    | `(term| ∀ [$_:ident : $a], $b) | `(term| ∀ [$a:term], $b)
      => go b (acc.push a)
    | `(term| ($[$idts:ident]* : $a) → $b) | `(term| {$[$idts:ident]* : $a} → $b)
    | `(term| ∀ ($[$idts:ident]* : $a), $b) | `(term| ∀ {$[$idts:ident]* : $a}, $b)
      => go b (acc ++ Array.replicate idts.size a)
    | _ => return (acc, t)
  go t #[]

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

/- From: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/binderIdent.20vs.20Ident -/
def identToBinderIdent (i : Ident) : TSyntax ``binderIdent := Unhygienic.run <|
  withRef i `(binderIdent| $i:ident)

def binderIdentToIdent [Monad m] [MonadError m] (bi : TSyntax ``binderIdent) : m Ident :=
  match bi with
  | `(binderIdent|$i:ident) => pure i
  | _ => throwError "[binderIdentToIdent] unexpected syntax: {bi}"

section Binders
open Lean.Parser

def Term.explicitBinderF := Term.explicitBinder (requireType := false)
def Term.implicitBinderF := Term.implicitBinder (requireType := false)

/-- Transforms an explicit binder into an implicit one. -/
def mkImplicitBinder [Monad m] [MonadQuotation m] : TSyntax `Lean.Parser.Term.bracketedBinder -> m (TSyntax `Lean.Parser.Term.bracketedBinder)
  | `(Term.explicitBinderF| ($id:ident : $tp:term)) => do `(Term.bracketedBinderF| {$id:ident : $tp:term})
  | stx => return stx
end Binders

def bracketedBinderIdent [Monad m] [MonadError m] [MonadQuotation m] (stx : TSyntax `Lean.Parser.Term.bracketedBinder) : m (Option Ident) := do
  match stx with
  | `(bracketedBinder| ($id:ident : $_tp)) => return id
  | `(bracketedBinder| [$id:ident : $_tp]) => return id
  | `(bracketedBinder| {$id:ident : $_tp}) => return id
  | _ => return none

/-- Given a set of binders, return the terms that correspond to them.
Typeclasses that are not named are replaced with `_`, to be inferred. -/
def bracketedBindersToTerms [Monad m] [MonadError m] [MonadQuotation m] (stx : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) : m (Array Term) := do
  let idents : Array (Option Ident) ← stx.mapM bracketedBinderIdent
  idents.mapM (fun mid => do
    match mid with
    | some id => `(term|$id)
    | none => `(term|_))

def explicitBindersFlatMapM [Monad m] [MonadError m] [MonadQuotation m] (stx : TSyntax `Lean.explicitBinders) (f : TSyntax `Lean.binderIdent → TSyntax `term → m α) : m (Array α) :=
  match stx with
  | `(explicitBinders|$bs*) =>
    bs.flatMapM fun
      | `(bracketedExplicitBinders|($bis* : $tp)) =>
        bis.mapM fun bi => f bi tp
      | _ => throwError "unexpected syntax in explicit binder: {stx}"
  | _ => throwError "unexpected syntax in explicit binder: {stx}"

/-- Convert existential binders into function binders. -/
def toFunBinderArray [Monad m] [MonadError m] [MonadQuotation m] (stx : TSyntax `Lean.explicitBinders) : m (TSyntaxArray `Lean.Parser.Term.funBinder) :=
  explicitBindersFlatMapM stx fun bi tp => do
    let id ← binderIdentToIdent bi
    `(Lean.Parser.Term.funBinder| ($id : $tp:term))

/-- Convert existential binders into definition binders. -/
def toBracketedBinderArray [Monad m] [MonadError m] [MonadQuotation m] (stx : TSyntax `Lean.explicitBinders) : m (TSyntaxArray `Lean.Parser.Term.bracketedBinder) := do
  explicitBindersFlatMapM stx fun bi tp => do
    let id ← binderIdentToIdent bi
    `(bracketedBinder| ($id : $tp:term))

def explicitBindersToTerms [Monad m] [MonadError m] [MonadQuotation m] (stx : TSyntax `Lean.explicitBinders) : m (Array Term) := do
  toBracketedBinderArray stx >>= bracketedBindersToTerms

open Lean.Parser.Term in
def bracketedBinderToFunBinder [Monad m] [MonadError m] [MonadQuotation m] (stx : TSyntax ``bracketedBinder) : m (TSyntax ``funBinder) := do
  match stx with
  | `(bracketedBinder| ($id:ident : $tp:term)) => `(funBinder| ($id:ident : $tp:term))
  | `(bracketedBinder| [$id:ident : $tp:term]) => `(funBinder| [$id:ident : $tp:term])
  | `(bracketedBinder| [$tp:term]) => `(funBinder| [$tp:term])
  | `(bracketedBinder| {$id:ident*}) => `(funBinder| {$id:ident*})
  | `(bracketedBinder| {$ids:ident* : $tp:term}) => `(funBinder| {$ids:ident* : $tp:term})
  | _ => throwError "bracketedBinderToFunBinder: unexpected syntax {stx}"

/-- Convert existential binders (`explicitBinders`) into identifiers. -/
def toIdentArray [Monad m] [MonadError m] [MonadQuotation m] (stx : TSyntax `Lean.explicitBinders) : m (TSyntaxArray `ident) := do
  explicitBindersFlatMapM stx fun bi _tp => do `(ident| $(← binderIdentToIdent bi))

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
def isCapital (i : Name) : Bool :=
  i.isStr && i.toString.all (fun c => c.isUpper || c.isDigit)

/-- You _can_ use these as `funBinder`s, but they won't have a type, so might fail strangely. -/
def getFieldIdentsForStruct [Monad m] [MonadEnv m] [MonadError m] (n : Name) : m (Array Ident) := do
  let .some sinfo := getStructureInfo? (← getEnv) n
    | throwError "getFieldNamesForStruct: {n} is not a structure"
  return sinfo.fieldNames.map (fun n => mkIdent n)

/-- Modelled after `Lean.Elab.Term.withAutoBoundImplicit`, but
customisable via `conditionToBind` and `unboundCont`.

FIXME: use `withAutoBoundImplicit` instead. The only difference is that
we return `.default` binders, rather than `.implicit`. -/
private partial def withAutoBoundCont
  (k : TermElabM α)
  (conditionToBind : Name → TermElabM Bool)
  (unboundCont : Exception → Name → TermElabM α)
  : TermElabM α := do
  withReader (fun ctx => { ctx with autoBoundImplicit := true, autoBoundImplicits := {} }) do
    let rec loop (s : Term.SavedState) : TermElabM α := withIncRecDepth do
      try
        k
      catch
        | ex => match isAutoBoundImplicitLocalException? ex with
          | some n =>
            if ← conditionToBind n then
            -- Restore state, declare `n`, and try again
              s.restore
              Meta.withLocalDecl n .default (← Meta.mkFreshTypeMVar) fun x =>
                withReader (fun ctx => { ctx with autoBoundImplicits := ctx.autoBoundImplicits.push x } ) do
                  loop (← saveState)
            else unboundCont ex n
          | none   => throw ex
    loop (← saveState)

/-- Automatically bind all variables whose names contain only capitals
(and/or digits). -/
private partial def withAutoBoundCapitals (k : TermElabM α) : TermElabM α := do
  withAutoBoundCont k (fun n => return isCapital n) (fun ex n => do throwErrorAt ex.getRef "Unbound uncapitalized variable: {n}")

@[inline] macro "exists?" br:explicitBinders ? "," t:term : term =>
  match br with
  | some br => `(exists $br, $t)
  | none => `($t)

@[inline] macro "forall?" br:bracketedBinder* "," t:term : term =>
  if br.size > 0 then
    `(∀ $br*, $t)
  else
    `($t)

def expandTermMacro [Monad m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m] (stx : Term) : m Term := do
  TSyntax.mk <$> (Elab.liftMacroM <| expandMacros stx)

/-- All capitalized variables inside `uqc%` will be automatically
universally quantified. Example: `uqc% (Nat.le N M)` becomes `∀ N M, Nat.le N M`. -/
syntax (name := univerallyQuantifyCapitalsStx) "uqc% " term : term

@[term_elab univerallyQuantifyCapitalsStx]
def elabUniverallyQuantifyCapitals : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(term| uqc% $t:term) =>
    let originalFVarIds := (← getLCtx).getFVarIds
    -- This ensures the capitals will be bound as `fvar`s
    withAutoBoundCapitals $ do
    -- CHECK can we get rid of the next line?
    withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) do
    -- NOTE: even though we don't use the result, this will throw an exception
    -- for unbound variables, which is what `withAutoBoundCapitals` requires
    let e ← Term.elabTerm t expectedType?
    let lctx ← getLCtx
    -- Inspect the local context and collect the capitals that weren't already
    -- bound when we started.
    let mut capitalVars : Array Expr := #[]
    for ldecl in lctx do
      let x := ldecl.fvarId
      if originalFVarIds.contains x then continue
      match lctx.getRoundtrippingUserName? x with
      | .some n => if isCapital n then capitalVars := capitalVars.push (.fvar x)
      | .none => pure ()
    -- Quantify over capitals
    Meta.mkForallFVars capitalVars e
  | _ => throwUnsupportedSyntax

def repeatedOp [Monad m] [MonadQuotation m] (op : Name) (operands : Array (TSyntax `term)) (default : Option (TSyntax `term) := none) : m (TSyntax `term) := do
  if operands.isEmpty then
    match default with
    | .some d => return d
    | .none => panic! "[repeatedOp {op}]: no operands and no default"
  else
    let last := operands.size - 1
    let initT := operands[last]!
    let acc := operands[0:last]
    acc.foldrM (init := initT) fun operand acc => `(term|$(mkIdent op) $operand $acc)

def repeatedAnd [Monad m] [MonadQuotation m] (operands : Array (TSyntax `term)) : m (TSyntax `term) := do
  repeatedOp `And operands (default := ← `(term|$(mkIdent `True)))

def repeatedOr  [Monad m] [MonadQuotation m] (operands : Array (TSyntax `term)) : m (TSyntax `term) := do
  repeatedOp `Or operands (default := ← `(term|$(mkIdent `False)))

/--
Similar to the `distinct` keyword in SMT-LIB, this generates inequality
conditions for multiple terms. Example: `distinct a b c d`=
-/
syntax "distinct" (term:max)* : term
macro_rules
  | `(term|distinct $[$ids:term]*) => do
    let mut inequalities := #[]
    for index_left in [0:ids.size] do
      for index_right in [index_left+1:ids.size] do
        let elem_i := ids[index_left]!
        let elem_j := ids[index_right]!
        inequalities := inequalities.push (← `($elem_i ≠ $elem_j))
    let fmla ← repeatedAnd inequalities
    return fmla

-- adapted from `elabSimpTheorem` in `Lean/Elab/Tactic/Simp.lean`
def elabSimpTheoremFromTerm (config : Meta.ConfigWithKey) (id : Meta.Origin) (stx : Syntax)
    (post : Bool) (inv : Bool) : TermElabM (Option (Array Meta.SimpEntry)) := do
  let thm? ← Term.withoutModifyingElabMetaStateWithInfo <| withRef stx do
    let e ← Term.elabTerm stx .none
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    if e.hasSyntheticSorry then
      return .none
    let e := e.eta
    if e.hasMVar then
      let r ← Meta.abstractMVars e
      return some (r.paramNames, r.expr)
    else
      return some (#[], e)
  if let some (levelParams, proof) := thm? then
    let thms ← Meta.mkSimpTheoremFromExpr id levelParams proof (post := post) (inv := inv) (config := config)
    let res := thms.map (Meta.SimpEntry.thm ·)
    return .some res
  else
    return .none

-- adapted from `elabOpenDecl` in `Lean/Elab/Tactic/BuiltinTactic.lean`
def evalOpen (decl : TSyntax `Lean.Parser.Command.openDecl) (k : MetaM α) : MetaM α := do
  try
    pushScope
    let openDecls ← elabOpenDecl decl
    withTheReader Core.Context (fun ctx => { ctx with openDecls := openDecls }) k
  finally
    popScope

/-- Returns `(fun $binders* => $body)`, but takes care of the case
where `binders` is empty. -/
def mkFunSyntax [Monad m] [MonadQuotation m] (binders : TSyntaxArray `Lean.Parser.Term.funBinder) (body : TSyntax `term) : m (TSyntax `term) := do
  if binders.isEmpty then pure body else `(fun $binders* => ($body))

open Meta Elab Term in
/-- `meta_match_option val => t1 => t2` is a meta-level construct that
matches on `val` of type `Option α` for some `α`. If `val = some v`, it evaluates
`t1 v` (an application); if `val = none`, it evaluates `t2`. This is useful
in tactics where `t1` and/or `t2` might be ill-typed. -/
elab "meta_match_option" val:term "=>" t1:term "=>" t2:term : term <= expectedType => do
  let valExpr ← elabTerm val none
  let valExpr ← whnf valExpr
  let ty ← inferType valExpr
  let coreTy ← match_expr ty.consumeMData with
    | Option coreTy => pure coreTy
    | _ => throwError "meta_match_option expected an Option type"
  match_expr valExpr with
  | Option.some _ v =>
    let arrowTy ← mkArrow coreTy expectedType
    let t1Expr ← elabTerm t1 arrowTy
    let app := t1Expr.betaRev #[v]
    pure app
  | Option.none _ =>
    let t2Expr ← elabTerm t2 expectedType
    pure t2Expr
  | _ => throwError "meta_match_option expected an Option expression"

open Meta Elab Term in
/-- Given a term `val` of function type, `remove_unused_args% val`
produces a new term where any arguments that are not used in the body
are removed. -/
elab "remove_unused_args% " val:term : term => do
  let valExpr ← elabTerm val none
  let valExpr ← instantiateMVars valExpr
  lambdaTelescope valExpr fun xs body => do
    mkLambdaFVars xs body (usedOnly := true)

open Meta Elab Term in
/-- Given a set of binders a term `val`, `remove_unused_binders% binders => val`
produces a new term where any binder in `binders` that are not used in
the body are removed (i.e., they will not become arguments). -/
elab "remove_unused_binders% " binders:bracketedBinder* "=>" val:term : term => do
  elabBinders binders fun vs => do
    let valExpr ← elabTerm val none
    let valExpr ← instantiateMVars valExpr
    mkLambdaFVars vs valExpr (usedOnly := true)

end Veil
