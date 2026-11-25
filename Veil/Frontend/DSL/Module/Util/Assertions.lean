module

public meta import Veil.Frontend.DSL.Module.Util.StateTheory

public meta section

open Lean Elab Command Term Meta Tactic

namespace Veil

/-! ## Data Types -/

inductive TheoryAndStateTermTemplateArgKind where
  | theory
  | state
  | nextState

/-- How state fields exposed by `withTheoryAndStateTermTemplate` are represented. -/
inductive StateFieldView where
  /-- The state contains concrete representation fields, which must be converted
  with `FieldRepresentation.get`. -/
  | concrete
  /-- The state fields are already abstract and can be exposed directly. -/
  | abstract

/-! ## Assertion Creation & Registration -/

def _root_.Lean.TSyntax.getPropertyName (stx : TSyntax `propertyName) : Name :=
  match stx with
  | `(propertyName| [$id]) => id.getId.eraseMacroScopes
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
      | .termination => s!"termination_{sz}"
      | .stateConstraint => s!"state_constraint_{sz}"

def Module.registerAssertion [Monad m] [MonadError m] (mod : Module) (sc : StateAssertion) : m Module := do
  mod.throwIfAlreadyDeclared sc.name
  let mut mod := { mod with assertions := mod.assertions.push sc, _declarations := mod._declarations.insert sc.name sc.declarationKind }
  for set in sc.inSets do
    let currentAssertions := mod._assertionSets.getD set Std.HashSet.emptyWithCapacity
    mod := { mod with _assertionSets := mod._assertionSets.insert set (currentAssertions.insert sc.name) }
  return mod

/-! ## Shadowing Diagnostics -/

/-- The user-visible field with this name. In a transition, primed names
refer to the post-state. -/
def Module.fieldShadowedBy? (mod : Module) (name : Name) (includeTheory := true)
    (includeState := true) (primed := false) : Option StateComponent :=
  if name.hasMacroScopes then none
  else
    let post := if includeState && primed then
      mod.mutableComponents.find? (fun field => field.name.appendAfter "'" == name)
    else none
    post <|> (if includeState then mod.mutableComponents.find? (·.name == name) else none) <|>
      (if includeTheory then mod.immutableComponents.find? (·.name == name) else none)

def warnLocalParameterShadow [Monad m] [MonadLog m] [MonadOptions m] [AddMessageContext m]
    (ref : Syntax) (name : Name) : m Unit :=
  logWarningAt ref
    m!"local `{name}` shadows parameter `{name}`; references to this name resolve to the local"

def warnFieldShadow [Monad m] [MonadLog m] [MonadOptions m] [AddMessageContext m]
    (ref : Syntax) (binder : String) (name : Name) (field : StateComponent) : m Unit := do
  let kind := if field.isMutable then "mutable state" else "immutable theory"
  logWarningAt ref m!"{binder} `{name}` shadows {kind} component `{field.name}`; references to this name resolve to the {binder}"

def Module.warnExplicitParameterShadows (mod : Module)
    (params : Option (TSyntax `Lean.explicitBinders)) (includeState := true)
    (primed := false) : CommandElabM Unit := do
  if let some binders := params then
    discard <| explicitBindersFlatMapM binders fun binder _ => do
      let id ← binderIdentToIdent binder
      if let some field := mod.fieldShadowedBy? id.getId (includeState := includeState) (primed := primed) then
        warnFieldShadow id "parameter" id.getId field

/-- Read Lean's elaborated binders so warnings respect the scopes of patterns,
quantifiers, and other term syntax. The source span excludes generated
binders, and also lets us deduplicate binders elaborated more than once. -/
def Module.warnTermShadows [Monad m] [MonadInfoTree m] [MonadLog m] [MonadOptions m]
    [AddMessageContext m] (mod : Module) (stx : Syntax) (firstTree : Nat)
    (includeState : Syntax.Range → Bool := fun _ => true) (primed := false)
    (parameters : NameSet := {})
    (ignore : Syntax.Range → Bool := fun _ => false) : m Unit := do
  let some range := stx.getRange? | return
  let info ← getInfoState
  let mut binders : Array (TermInfo × LocalDecl × Syntax.Range) := #[]
  for i in [firstTree:info.trees.size] do
    let tree := info.trees[i]!.substitute info.assignment
    binders ← tree.foldInfoM (init := binders) fun _ node binders => do
      let .ofTermInfo term := node | return binders
      unless term.isBinder && term.stx.isIdent do return binders
      let .original .. := term.stx.getHeadInfo | return binders
      let some span := term.stx.getRange? | return binders
      unless range.start ≤ span.start && span.stop ≤ range.stop do return binders
      let some decl := term.lctx.findFVar? term.expr | return binders
      return binders.push (term, decl, span)
  let locals := binders.foldl (fun ids (_, decl, _) => ids.insert decl.fvarId) ({} : FVarIdSet)
  let mut seen : Std.HashSet Syntax.Range := {}
  for (term, decl, span) in binders do
    let name := term.stx.getId
    if name.hasMacroScopes || seen.contains span || ignore span then continue
    seen := seen.insert span
    let prior := term.lctx.findDeclRev? fun prior =>
      if prior.index < decl.index && prior.userName == name &&
          (locals.contains prior.fvarId || (parameters.contains name &&
            prior.kind != .implDetail && !prior.binderInfo.isInstImplicit))
      then some prior else none
    if let some prior := prior then
      unless locals.contains prior.fvarId do warnLocalParameterShadow term.stx name
    else if let some field := mod.fieldShadowedBy? name (includeState := includeState span) (primed := primed) then
      warnFieldShadow term.stx "local" name field

/-! ## Tactic Infrastructure -/

section AssertionElab

syntax (name := veil_exact_theory) "veil_exact_theory" : tactic
syntax (name := veil_exact_state) "veil_exact_state" : tactic

/-- Find the newest implementation-detail binding with `userName`. Generated
bindings, such as theory field views and the state binding of each action
statement, reuse their names at successive openings, so reverse lookup selects
the one from the most recent opening. -/
private def findImplementationDetail? (lctx : LocalContext)
    (userName : Name) : Option LocalDecl :=
  lctx.findDeclRev? fun decl =>
    if decl.kind == .implDetail && decl.userName == userName then
      some decl
    else
      none

/-- Private names distinguish logical fields, concrete representations and the
current action state. Only the base name is visible in pretty-printed terms. -/
inductive FieldBinderRole where
  | theory | state | stateConcrete | nextState | nextStateConcrete | actionState

private def FieldBinderRole.names (role : FieldBinderRole) (field : Name) : Name × Name :=
  match role with
  | .theory            => (`Veil.fieldBinder.theory, field)
  | .state             => (`Veil.fieldBinder.state, field)
  | .stateConcrete     => (`Veil.fieldBinder.stateConcrete, field.appendAfter "_conc")
  | .nextState         => (`Veil.fieldBinder.nextState, field.appendAfter "'")
  | .nextStateConcrete => (`Veil.fieldBinder.nextStateConcrete, field.appendAfter "_conc'")
  | .actionState       => (`Veil.fieldBinder.actionState, field)

def mkPrivateFieldIdent (role : FieldBinderRole) (field : Name) : MetaM Ident := do
  let (tag, base) := role.names field
  let scope := extractMacroScopes (← mkFreshUserName base)
  return mkIdent ({ scope with ctx := scope.ctx ++ tag }.review)

def isPrivateFieldBinder (name : Name) (role : FieldBinderRole) (field : Name) : Bool :=
  let (tag, base) := role.names field
  let scope := extractMacroScopes name
  tag.isSuffixOf scope.ctx && scope.name == base

def findFieldBinder? (lctx : LocalContext) (role : FieldBinderRole) (field : Name) : Option LocalDecl :=
  lctx.findDeclRev? fun decl =>
    if isPrivateFieldBinder decl.userName role field then some decl else none

/-- Reconstruct a `Theory` term from the hypotheses in the context. -/
def elabExactTheory : TacticM Unit := withMainContext do
  let mod ← getCurrentModule
  let lctx ← getLCtx
  let comp := mod.immutableComponents.map fun field =>
    let decl? := findFieldBinder? lctx .theory field.name <|>
      findImplementationDetail? lctx (mkVeilImplementationDetailName field.name)
    Lean.mkIdent (decl?.map (·.userName) |>.getD field.name)
  let constr ← `(term| (⟨$[$comp],*⟩ : $(← mod.theoryStx)))
  trace[veil.debug] "theory constr: {constr}"
  Tactic.evalTactic $ ← `(tactic| exact $constr)

def elabExactState : TacticM Unit := withMainContext do
  let mod ← getCurrentModule
  let lctx ← getLCtx
  let currentState? := findFieldBinder? lctx .actionState currentStateBindingName
  let actualFields : Array Term ← mod.mutableComponents.mapM fun field => do
    let nm := field.name
    if let some decl := findFieldBinder? lctx .stateConcrete nm then
      pure (mkIdent decl.userName)
    else if let some st := currentState? then
      `(term| $(← exprToSyntax st.toExpr).$(mkIdent nm))
    else try
      -- Hand-written Lean callers can provide a logical field as a projection.
      let some value := (lctx.findFromUserName? nm).bind (·.value? true) | failure
      let value := match_expr value with
        | id _ v => v
        | _ => value
      match_expr value with
      | Veil.FieldRepresentation.get _ _ _ _ concrete => exprToSyntax concrete
      | _ => failure
    catch _ =>
      let conc := nm.appendAfter "_conc"
      let some decl := lctx.findFromUserName? conc
        | throwError "state component {nm} is not available in the local context"
      pure (mkIdent decl.userName)
  let constr ← `(term| (⟨$[$actualFields],*⟩ : $(← mod.stateStx)))
  trace[veil.debug] "state constr: {constr}"
  Tactic.evalTactic $ ← `(tactic| exact $constr)

elab_rules : tactic
  | `(tactic| veil_exact_theory) => elabExactTheory
  | `(tactic| veil_exact_state) => elabExactState

/-! ## Theory/State Template Infrastructure -/

/-- Expose the fields under their DSL names, unless an enclosing user binder
already owns the name. The private field bindings remain available to generated code. -/
scoped syntax (name := veilFieldViews)
  "veil_field_views% " ("(" ident " := " ident ")")* (" hiding " ident+)? " in " term : term

def Parameter.isGeneratedFieldContext (p : Parameter) : Bool :=
  p.kind matches .backgroundTheory | .environmentState

/-- Mark the ambient parameters by identity before entering the user term. -/
def withGeneratedFieldContext (params : Array Parameter) (vars : Array Expr) (body : TermElabM α) :
    TermElabM α := do
  let lctx := (params.zip vars).foldl (init := ← getLCtx) fun ctx (p, var) =>
    if p.isGeneratedFieldContext then ctx.setKind var.fvarId! .implDetail else ctx
  withLCtx' lctx body

/-- Bind the field views for `body`. Abstract the lets together so Lean traverses
the body and updates its pending metavariable contexts only once per opening. -/
def bindFieldViews [Monad m] [MonadControlT MetaM m] [MonadLiftT MetaM m]
    (views : List (Name × Expr × Expr)) (body : m Expr) : m Expr :=
  go views #[]
where
  go (views : List (Name × Expr × Expr)) (vars : Array Expr) : m Expr := do
    match views with
    | [] => mkLetFVars vars (← body) (generalizeNondepLet := false)
    | (name, ty, value) :: rest =>
      withLetDecl name ty value (kind := .implDetail) fun var =>
        go rest (vars.push var)

@[term_elab veilFieldViews]
def elabVeilFieldViews : TermElab := fun stx expectedType? => do
  let `(veil_field_views% $[($names:ident := $fields:ident)]* $[hiding $generated:ident*]? in $body) := stx
    | throwUnsupportedSyntax
  let lctx := (generated.getD #[]).foldl (init := ← getLCtx) fun ctx id =>
    if let some decl := ctx.findFromUserName? id.getId then
      ctx.setKind decl.fvarId .implDetail
    else ctx
  withLCtx' lctx do
    let mut namesSeen : NameSet := {}
    let mut views := []
    for (name, field) in (names.zip fields).reverse do
      if namesSeen.contains name.getId then continue
      namesSeen := namesSeen.insert name.getId
      -- Instance parameters remain available to typeclass search.
      if lctx.any (fun decl => decl.userName == name.getId && decl.kind != .implDetail &&
          !decl.binderInfo.isInstImplicit) then continue
      let value ← getFVarFromUserName field.getId
      views := (name.getId, ← inferType value, value) :: views
    -- The body can infer the result type of an unannotated ghost function.
    bindFieldViews views (elabTerm body expectedType?)

/-- Wrap a term in field destructors. The callback receives the binders in
the order of `targets` (one array per opened structure). Generated terms can
refer directly to these binders, even when a user binder shadows a field. -/
def Module.withFieldBinders (mod : Module)
    (targets : List (TheoryAndStateTermTemplateArgKind × Term × Bool))
    (motiveType : Option Term) (body : Array (Array Ident) → MetaM Term)
    (fieldRepInstance : Term := fieldRepresentation) (stateSortTerm : Option Term := none)
    (stateView : StateFieldView := .concrete) : MetaM Term := do
  let motive := mkIdent `motive
  let motiveBody ← match motiveType with
    | some ty => `(fun _ => $ty)
    | none => `(fun _ => _)
  let (theoryName, stateName) := (mod.name ++ theoryName, mod.name ++ stateName)
  let casesOnTheory := theoryName ++ `casesOn
  let casesOnState := stateName ++ `casesOn
  let openings ← targets.toArray.mapM fun (kind, receiver, wrap?) => do
    let privateNames (name : Name) (view : FieldBinderRole) := do
      let fields ← getFieldIdentsForStruct name
      fields.mapM fun f => mkPrivateFieldIdent view f.getId
    let (fields, concrete) ← match kind with
      | .theory => pure (← privateNames theoryName .theory, #[])
      | .state => pure (← privateNames stateName .state, ← privateNames stateName .stateConcrete)
      | .nextState => pure (← privateNames stateName .nextState, ← privateNames stateName .nextStateConcrete)
    pure (kind, receiver, wrap?, fields, concrete)
  let body ← body (openings.map fun (_, _, _, fields, _) => fields)
  openings.foldrM (init := body) fun (kind, i, wrap?, fields, concrete) body => do
    match kind with
    | .theory =>
      let tmp ← mkFunSyntax fields body
      let i ← if wrap? then `(term| $(mkIdent ``readFrom) $i) else pure i
      `(term|
        @$(mkIdent casesOnTheory) $(← mod.uninterpretedParamIdents)*
        ($motive := $motiveBody) ($i) ($tmp))
    | .state | .nextState =>
      let (binders, body') ← match stateView with
        | .abstract => pure (fields, body)
        | .concrete => do
          -- Annotate types here, otherwise there can be issues like `f a`,
          -- where `f` has a complicated type definitionally equal to
          -- `node → Bool`: coercions will not be inserted to make `f a` a Prop.
          let fieldTypes ← mod.mutableComponents.mapM (·.typeStx)
          let bundled := fields.zip fieldTypes |>.zip concrete
          let body' ← bundled.foldrM (init := body) fun ((f, ty), fConc) b => do
            `(let $f:ident : $ty := ($fieldRepInstance _).$(mkIdent `get) $fConc:ident ; $b)
          pure (concrete, body')
      let tmp ← mkFunSyntax binders body'
      let sortTerms : Array Term ← match stateSortTerm with
        | some sortTerm => pure #[sortTerm]
        | none => match stateView with
          | .concrete =>
            pure ((← mod.uninterpretedParamIdentsForTheoryOrState true).map (fun i => (i : Term)))
          | .abstract =>
            -- `State` takes only the dispatcher; the abstract instantiation
            -- is `FieldAbstractType` at the module's sorts.
            pure #[← `($fieldAbstractDispatcher $(← mod.uninterpretedParamIdents)*)]
      let i ← if wrap? then `(term| $(mkIdent ``getFrom) $i) else pure i
      `(term|
        @$(mkIdent casesOnState) $sortTerms*
        ($motive := $motiveBody) ($i) ($tmp))

/-- Open fields for a generated term that takes them in target order. -/
def Module.withTheoryAndStateTermTemplate (mod : Module)
    (targets : List (TheoryAndStateTermTemplateArgKind × Term × Bool))
    (motiveType : Option Term) (body : Array Ident → MetaM Term)
    (fieldRepInstance : Term := fieldRepresentation) (stateSortTerm : Option Term := none)
    (stateView : StateFieldView := .concrete) : MetaM Term :=
  mod.withFieldBinders targets motiveType (fun groups => body groups.flatten)
    fieldRepInstance stateSortTerm stateView

/-- Make the field binders visible to the user term. -/
def openUserFieldNames (fields : Array Ident) (body : Term) (generated : Array Ident := #[]) : MetaM Term := do
  let names := fields.map fun field => mkIdent field.getId.eraseMacroScopes
  if generated.isEmpty then
    `(veil_field_views% $[($names:ident := $fields:ident)]* in $body)
  else
    `(veil_field_views% $[($names:ident := $fields:ident)]* hiding $generated:ident* in $body)

/-- Open theory and state fields under their declared names in a user term. -/
def Module.withUserFieldNames (mod : Module)
    (targets : List (TheoryAndStateTermTemplateArgKind × Term × Bool))
    (motiveType : Option Term) (body : Term)
    (fieldRepInstance : Term := fieldRepresentation) (stateSortTerm : Option Term := none)
    (generated : Array Ident := #[]) :
    MetaM Term :=
  mod.withFieldBinders targets motiveType (fun groups => openUserFieldNames groups.flatten body generated)
    fieldRepInstance stateSortTerm

/-! ## Convenience Wrappers -/

/-- This is used wherever we want to define a predicate over the
background theory (e.g. in `assumption` definitions). Instead of
writing `fun th => Pred`, this will pattern-match over the theory and
make all its fields accessible for `Pred`. -/
def withTheory (t : Term) (motiveType : Option Term) : MetaM (Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Term) := do
  let mut mod ← getCurrentModule
  let th ← mkIdent <$> mkFreshUserName `th
  let fn ← do
    let tmp ← mod.withUserFieldNames [(.theory, th, true)] motiveType t
    `(term| (fun ($th : $environmentTheory) => $tmp))
  -- See NOTE(SUBTLE) to see why this is not actually ill-typed.
  let binders := #[← `(bracketedBinder| ($th : $environmentTheory := by veil_exact_theory))]
  return (binders, ← `(term|$fn $th))

/-- This is used wherever we want to define a predicate over the
background theory and the mutable state (e.g. in `invariant`
definitions). Instead of writing `fun th st => Pred`, this will
pattern-match over the theory and state and make all their fields
accessible for `Pred`. This was previously called `funcasesM`. -/
def withTheoryAndState (t : Term) (motiveType : Option Term) (fieldRepInstance : Term := fieldRepresentation) : MetaM (Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Term) := do
  let mut mod ← getCurrentModule
  let th ← mkIdent <$> mkFreshUserName `th
  let st ← mkIdent <$> mkFreshUserName `st
  let fn ← do
    let tmp ← mod.withUserFieldNames [(.theory, th, true), (.state, st, true)]
      motiveType t (fieldRepInstance := fieldRepInstance)
    `(term| (fun ($th : $environmentTheory) ($st : $environmentState) => $tmp))
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

/-- Variant of `withTheoryAndState` that uses specific types for theory and
state rather than the environment theory `ρ` and environment state `σ`. We use
this to elaborate assertions in `sat trace` commands. -/
def withTheoryAndStateFn (mod : Module) (t : Term) (motiveType : Option Term) (theoryT stateT : Term)
    (fieldRepInstance : Term) (stateSortTerm : Term) : MetaM Term := do
  let th ← mkIdent <$> mkFreshUserName `th
  let st ← mkIdent <$> mkFreshUserName `st
  -- Ghost relations' default `st` parameter uses `by veil_exact_state`, which
  -- constructs `@State χ`.
  -- We need `χ` in scope so the tactic can resolve it.
  let t' ← `(let $(mkIdent fieldConcreteTypeName) := $stateSortTerm; $t)
  let tmp ← mod.withUserFieldNames [(.theory, th, true), (.state, st, true)]
    motiveType t' fieldRepInstance (stateSortTerm := some stateSortTerm)
  `(term| (fun ($th : $theoryT) ($st : $stateT) => $tmp))

/-! ## Term Creation -/

/-- The result of elaborating a Veil term together with its generated syntax
fragments and definition body. -/
structure ElaboratedVeilTerm where
  -- TODO: The Parameter metadata needs a systematic way to describe the exact
  -- binder order of generated Lean declarations. Assertion/ghost/assembled
  -- definitions currently store user params, generated theory/state binders,
  -- and extracted Decidable params in different places, so later code has to
  -- reconstruct the binder order in fragile declaration-kind-specific ways.
  /-- Extracted `Decidable` instance parameters; pass through
  `Module.canonicalizeExtraParams` before storing in the `Module`. -/
  extraParams : Array Parameter
  thstBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)
  term : Term
  expr : Expr

/-- Elaborates the term with all state and theory variables bound (or just
theory if `justTheory` is true). When `quantifyCapitals` is true,
capitalized variables are universally quantified via `uqc%` (only valid for
`Prop`-returning terms). The `motiveType` parameter controls the motive used
in the `casesOn` eliminators. -/
def Module.mkVeilTerm (mod : Module) (name : Name) (dk : DeclarationKind) (params : Option (TSyntax `Lean.explicitBinders)) (term : Term)
  (motiveType : Option Term) (justTheory : Bool := false) (quantifyCapitals : Bool := false) : TermElabM ElaboratedVeilTerm := withExporting (isExporting := true) do
  -- Default theory/state arguments store tactic syntax in auxiliary declarations.
  -- These are part of the public signature of an assertion or ghost definition.
  withDeclName ((← getCurrNamespace) ++ name) do
  let baseParams ← mod.declarationBaseParams dk
  let binders ← baseParams.mapM (·.binder)
  let paramBinders ← Option.stxArrMapM params toBracketedBinderArray
  -- We don't `universallyQuantifyCapitals` after `withTheory` /
  -- `withTheoryAndState` because we want to have the universal
  -- quantification as deeply inside the term as possible, rather than above
  -- the binders for `rd` and `st` introduced below.
  let body ← if quantifyCapitals then `(uqc% ($term:term)) else pure term
  let (thstBinders, term') ← if justTheory then withTheory body motiveType else withTheoryAndState body motiveType
  let term' := Syntax.inheritSourceSpanFrom term' term
  -- Record the `Decidable` instances that are needed for the assertion.
  let allBinders := binders ++ paramBinders ++ thstBinders
  let (insts, expr) ← elabBinders allBinders $ fun vs => do
    let firstTree := (← getInfoTrees).size
    let (insts, expr) ← withSaveInfoContext <| withGeneratedFieldContext baseParams vs <|
      getRequiredDecidableInstances name term' (dsimpSubReaderSubStateRefl >=> foldFieldRepresentationGet)
    let expr ← instantiateMVars expr
    -- Segment `vs`
    let baseFVars := vs.extract 0 binders.size
    let paramFVars := vs.extract binders.size (binders.size + paramBinders.size)
    let thstFVars := vs.extract (binders.size + paramBinders.size) vs.size
    let userBaseFVars := (baseParams.zip baseFVars).filterMap fun (p, v) =>
      if p.isGeneratedFieldContext then none else some v
    let parameters ← (userBaseFVars ++ paramFVars).foldlM (init := ({} : NameSet)) fun names var => do
      return names.insert (← var.fvarId!.getUserName)
    mod.warnTermShadows term firstTree (includeState := fun _ => !justTheory) (parameters := parameters)
    let decMVars := insts.map (·.2)
    -- Binder infos are intentionally mixed here:
    -- * module-level base parameters should be implicit,
    -- * user parameters and the theory/state arguments keep their binder info,
    -- * extracted `Decidable` metavariables become typeclass arguments.
    let lctx := thstFVars.foldl (fun ctx var =>
      ctx.setUserName var.fvarId! (ctx.getFVar! var).userName.eraseMacroScopes) (← getLCtx)
    let expr ← withLCtx' lctx <| Meta.mkLambdaFVars (paramFVars ++ decMVars ++ thstFVars) expr
      (binderInfoForMVars := BinderInfo.instImplicit)
    let expr ← Meta.mkLambdaFVarsImplicit baseFVars expr
    let expr ← instantiateMVars expr
    if expr.hasMVar then
      throwError "mvar(s) exist in the elaborated assertion expression. Consider adding more type annotations."
    pure (insts, expr)
  trace[veil.debug] "insts: {insts.map (·.1)}"
  let extraParams : Array Parameter := insts.mapIdx (fun i (decT, _) => { kind := .definitionParameter name .typeclass, name := Name.mkSimple s!"{name}_dec_{i}", «type» := decT, userSyntax := .missing })
  return {
    extraParams := extraParams
    thstBinders := thstBinders
    term := term'
    expr := expr
  }

end AssertionElab

end Veil
