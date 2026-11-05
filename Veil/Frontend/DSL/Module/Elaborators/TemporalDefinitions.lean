module

public meta import Veil.Frontend.DSL.Module.Util
public meta import Lentil.Basic
public meta import Lasso.LTL.Notation
public import Veil.Core.Tools.LivenessMC.Interface

public meta section

open Lean Parser Elab Command Term
namespace Veil

/-! ## Shared action references -/

/-- `t` of `Enabled t`, `⟨ t ⟩`, `𝒲ℱ t` or `𝒮ℱ t` as an action, applied to arguments (`a x y`) or not (`a`),
possibly in parentheses: the name `a` and the arguments, if `t` has this shape. Both definitions of a temporal
property recognize an action this way (`actionAtomOf`, `elabTlfmlAction`). -/
partial def actionApp? : Term → Option (Ident × Array Term)
  | `(($t)) => actionApp? t
  | `($a:ident) => some (a, #[])
  | `($a:ident $args:term*) => some (a, args)
  | _ => none

/-- The module's action named `a`, if any, and its arguments `args`, one for each of its parameters. A
parameter left open, as `·` or by stopping before it, is `none` and stands for any value: for an action
`a (x y : T)`, `a`, `a ·` and `a · ·` all mean "any instantiation", and `a x₀` and `a x₀ ·` both mean `a x₀ y`
for some `y`. -/
def Module.resolveActionAtom? (mod : Module) (a : Ident) (args : Array Term) :
    TermElabM (Option (ProcedureSpecification × Array (Option Term))) := do
  let some spec := mod.actions.find? (·.name == a.getId) | return none
  if args.size > spec.params.size then
    throwErrorAt a "action `{spec.name}` takes {spec.params.size} parameter(s), but {args.size} \
      were given; write `·` for a parameter that can take any value"
  let args := args.map fun arg => if arg.raw.isOfKind ``Lean.Parser.Term.cdot then none else some arg
  return some (spec, args ++ .replicate (spec.params.size - args.size) none)

/-! ## Shallow formula elaboration

`[tlfml| …]` elaborates temporal formulas to Lentil predicates for proofs. The macros and elaborators
below adapt its state and action atoms to the current Veil module.

Lentil reads `⌜ t ⌝` as `state_pred t` with `t : σ → Prop`. While Veil elaborates a temporal property of a
module (`veil.temporal.moduleAtoms`), `t` is instead a proposition over the module's fields, as in an
assertion: the theory fields are bound around the whole formula, and the state fields around each atom. -/

/-- Internal: the atom `⌜ t ⌝` of a `[tlfml| …]` formula, see `elabTlfmlStateAtom`. -/
syntax (name := tlfmlStateAtom) "veil_tlfml_state_atom% " term:max : term

/-- Internal: `t` of `Enabled t`, `⟨ t ⟩`, `𝒲ℱ t` or `𝒮ℱ t` in a `[tlfml| …]` formula, see
`elabTlfmlAction`. -/
syntax (name := tlfmlAction) "veil_tlfml_action% " term:max : term

macro_rules
  | `([tlfml| ⌜ $t:term ⌝]) => `(veil_tlfml_state_atom% ($t))
  | `([tlfml| Enabled $t:term]) => `(Lentil.tl_enabled (veil_tlfml_action% ($t)))
  | `([tlfml| ⟨ $t:term ⟩]) => `(Lentil.action_pred (veil_tlfml_action% ($t)))
  | `([tlfml| 𝒲ℱ $t:term]) => `(Lentil.weak_fairness (veil_tlfml_action% ($t)))
  | `([tlfml| 𝒮ℱ $t:term]) => `(Lentil.strong_fairness (veil_tlfml_action% ($t)))

/-- `⌜ t ⌝` as Lentil reads it, `state_pred t`, or, while a temporal property of the current module is
elaborated, `state_pred (fun st => t)` with the state fields bound in `t` as in an assertion. -/
@[term_elab tlfmlStateAtom] def elabTlfmlStateAtom : TermElab := fun stx expectedType? => do
  let `(veil_tlfml_state_atom% $t) := stx | throwUnsupportedSyntax
  unless veil.temporal.moduleAtoms.get (← getOptions) do
    return ← elabTerm (← `($(mkIdent ``Lentil.state_pred) $t)) expectedType?
  let mod ← getCurrentModule
  let st := mkVeilImplementationDetailIdent `st
  let body ← mod.withTheoryAndStateTermTemplate [(.state .none "_conc", st, true)] (some (← `(Prop)))
    (fun _ _ => `(uqc% ($t:term)))
  elabTerm (← `($(mkIdent ``Lentil.state_pred) fun ($st : $environmentState) => $body)) expectedType?

/-- Elaborate a temporal action relation on the proof side. In a module's temporal property, the
parameters of an action left open (`Module.resolveActionAtom?`) are existentially quantified: e.g. for
`send (src dst : node)`, `send` becomes `fun s s' => ∃ src dst, send src dst s s'` and `send · d₀` becomes
`fun s s' => ∃ src, send src d₀ s s'`. Otherwise, elaborate `t` directly. -/
@[term_elab tlfmlAction] def elabTlfmlAction : TermElab := fun stx expectedType? => do
  let `(veil_tlfml_action% $t) := stx | throwUnsupportedSyntax
  let some (a, args) := actionApp? t | elabTerm t expectedType?
  let some (spec, args) ← (do
      unless veil.temporal.moduleAtoms.get (← getOptions) do return none
      (← getCurrentModule).resolveActionAtom? a args)
    | elabTerm t expectedType?
  if args.all Option.isSome then return ← elabTerm t expectedType?
  -- Generate the existential quantifiers for the open parameters and construct the body of the relation
  let mut xs : Array Ident := #[]
  let mut actualArgs : Array Term := #[]
  for (p, arg?) in spec.params.zip args do
    let some arg := arg? | do
      let x := Lean.mkIdent (← mkFreshUserName p.name)
      xs := xs.push x
      actualArgs := actualArgs.push x
    actualArgs := actualArgs.push arg
  elabTerm (← `(fun (s s' : $environmentState) => ∃ $[$xs:ident]*, $a $actualArgs* s s')) expectedType?

/-! ## Deep formula elaboration -/

/-- The action and its arguments in `Enabled t`, `⟨ t ⟩`, `𝒲ℱ t` or `𝒮ℱ t`, where `t` must be an action of
the module (`actionApp?`), with `none` for a parameter left open (`Module.resolveActionAtom?`). -/
private def actionAtomOf (mod : Module) (t : Term) : TermElabM (Name × Array (Option Term)) := do
  let actions := mod.actions.map (·.name) |>.toList
  let some (a, args) := actionApp? t
    | throwErrorAt t "expected an action of this module, applied to arguments or not; the module's \
        actions are {actions}"
  let some (spec, args) ← mod.resolveActionAtom? a args
    | throwErrorAt a "unknown action `{a.getId}`; the module's actions are {actions}"
  return (spec.name, args)

/-- The label predicate deciding `Enabled a …`/`⟨ a … ⟩`, a match over every constructor: the one of `a`
compares the label's arguments with the given ones, leaving the open parameters unconstrained, and the
others are false.

For a module whose actions are `send (src dst : node)` and `recv`, `Enabled send` and `⟨ send ⟩` give
```lean
fun lbl => match lbl with
  | Label.send .. => true
  | Label.recv .. => false
```
and `Enabled (send · d₀)` and `⟨ send · d₀ ⟩` give
```lean
fun lbl => match lbl with
  | Label.send _ dst => decide (dst = d₀)
  | Label.recv .. => false
``` -/
private def mkActionLabelMatch (mod : Module) (actionName : Name) (args : Array (Option Term)) :
    TermElabM Term := do
  let lbl := mkIdent `lbl
  let alts ← mod.actions.mapM fun (act : ProcedureSpecification) => do
    let ctor : Ident := Lean.mkIdent (labelTypeName ++ act.name)
    if act.name != actionName then
      `(Lean.Parser.Term.matchAltExpr| | $ctor:ident .. => $(Lean.mkIdent ``Bool.false))
    else if args.all Option.isNone then
      `(Lean.Parser.Term.matchAltExpr| | $ctor:ident .. => $(Lean.mkIdent ``Bool.true))
    else
      -- A fresh variable for each given argument, so that the argument cannot capture it
      let mut pats : Array Term := #[]
      let mut eqs : Array Term := #[]
      for (p, arg?) in act.params.zip args do
        let some arg := arg? | pats := pats.push (← `(_))
        let x := Lean.mkIdent (← mkFreshUserName p.name)
        pats := pats.push x
        eqs := eqs.push (← `($x = $arg))
      `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkApp ctor pats):term => decide ($(← repeatedAnd eqs)))
  `(term| fun $lbl => match $lbl:ident with $alts:matchAlt*)

-- `∀ x, φ` and `∃ x, φ` become the conjunction and the disjunction of `φ` over the values that `Enumeration`
-- lists for the type of `x`. For a sort, these are only known once `#temporal_check` instantiates the module.
macro_rules
  | `([ltl| ∀ $x:ident, $f]) => `($(mkIdent ``LivenessMC.forallEnum) fun $x => [ltl| $f])
  | `([ltl| ∀ $x:ident : $t, $f]) => `($(mkIdent ``LivenessMC.forallEnum) fun ($x : $t) => [ltl| $f])
  | `([ltl| ∃ $x:ident, $f]) => `($(mkIdent ``LivenessMC.existsEnum) fun $x => [ltl| $f])
  | `([ltl| ∃ $x:ident : $t, $f]) => `($(mkIdent ``LivenessMC.existsEnum) fun ($x : $t) => [ltl| $f])

/-- The atoms of `[ltl| …]`, read against the current module while Veil elaborates one of its temporal
formulas (`veil.temporal.moduleAtoms`). `⌜ t ⌝` is a state predicate and `⌞ t ⌟` a theory predicate,
which see the module's fields as an assertion does; `Enabled a …`/`⟨ a … ⟩` name one of its actions, and
`𝒲ℱ a …`/`𝒮ℱ a …` are the formulas they abbreviate, the same as when written out.

`⟨ a ⟩` is decided by the label of the step taken, which is stronger than Lentil's action predicate that
the shallow definition uses; see `Veil.temporalDeclaration`.
Tried before the plain reading of `[ltl| …]` (`Lasso.elabLtlAtom`), to which it defers otherwise. -/
@[term_elab Lasso.ltlFormula] def elabModuleLtlAtom : TermElab := fun stx expectedType? => do
  unless veil.temporal.moduleAtoms.get (← getOptions) do throwUnsupportedSyntax
  let mod ← getCurrentModule
  let (th, st) := (mkIdent `th, mkIdent `st)
  let statePredicate (targets : List (TheoryAndStateTermTemplateArgKind × Term × Bool)) (t : Term) := do
    let body ← mod.withTheoryAndStateTermTemplate targets (some (← `(Prop))) (fun _ _ => `(uqc% ($t:term)))
    -- The constructor does not take the field's default, so `name` is given explicitly
    `($(mkIdent ``LivenessMC.LivenessAtom.state) ($(mkIdent ``ModelChecker.SafetyProperty.mk)
        ($(mkIdent `name) := $(quote Name.anonymous))
        ($(mkIdent `property) := fun ($th : $environmentTheory) ($st : $environmentState) => $body)))
  let atom ← match stx with
    | `([ltl| ⌜ $t:term ⌝]) => statePredicate [(.theory, th, true), (.state .none "_conc", st, true)] t
    | `([ltl| ⌞ $t:term ⌟]) => statePredicate [(.theory, th, true)] t
    -- `Enabled a`/`⟨ a ⟩` are decided by a predicate on the action label, not on a state
    | `([ltl| Enabled $t:term]) =>
      let (actionName, args) ← actionAtomOf mod t
      `($(mkIdent ``LivenessMC.LivenessAtom.enabled) $(quote (Name.mkSimple s!"Enabled {actionName}"))
          $(← mkActionLabelMatch mod actionName args))
    | `([ltl| ⟨ $t:term ⟩]) =>
      let (actionName, args) ← actionAtomOf mod t
      `($(mkIdent ``LivenessMC.LivenessAtom.taken) $(quote (Name.mkSimple s!"⟨{actionName}⟩"))
          $(← mkActionLabelMatch mod actionName args))
    -- Checking `t` before unfolding reports a wrong one once, not for both `Enabled t` and `⟨ t ⟩`. The
    -- unfoldings are Lentil's fairness (`Lentil.wf_as_implies`, `Lentil.sf_as_implies`).
    | `([ltl| 𝒲ℱ $t:term]) =>
      discard <| actionAtomOf mod t
      return ← elabTerm (← `([ltl| (◇ □ Enabled $t) → □ ◇ ⟨ $t ⟩])) expectedType?
    | `([ltl| 𝒮ℱ $t:term]) =>
      discard <| actionAtomOf mod t
      return ← elabTerm (← `([ltl| (□ ◇ Enabled $t) → □ ◇ ⟨ $t ⟩])) expectedType?
    -- `tlfml` also admits a plain term (a `Lentil.pred`), which has no meaning for the model checker
    | `([ltl| $t:term]) =>
      throwErrorAt t "a plain term is not an atomic proposition of a model-checked property; write \
        `⌜ {t} ⌝` for a state predicate"
    | `([ltl| $f]) =>
      throwErrorAt f "a model-checked property can only use the atoms `⌜ … ⌝`, `⌞ … ⌟`, `Enabled …` and \
        `⟨ … ⟩`, the fairness conditions `𝒲ℱ …` and `𝒮ℱ …`, the connectives `⊤`, `⊥`, `¬`, `∧`, `∨`, `→`, \
        `↔`, `□`, `◇`, `◯`, `𝑈`, `𝑅`, `↝` and `⇒`, and the quantifiers `∀ x, …`, `∀ x : T, …`, `∃ x, …` and \
        `∃ x : T, …`; this formula is none of them"
    | _ => throwUnsupportedSyntax
  elabTerm (← `($(mkIdent ``Lasso.Formula.atom) $atom)) expectedType?

/-! ## Temporal property definitions

A temporal property `p` has up to two definitions: the shallow `p`, a `Lentil.pred` for `prove_temporal_by`,
and the deep `p.ast`, an `Lasso.Formula` syntax tree for `#temporal_check`. -/

private def Module.modifyTemporalProperty (mod : Module) (name : Name) (f : TemporalProperty → TemporalProperty) :
    Module :=
  { mod with temporalProperties := mod.temporalProperties.map fun tp => if tp.name == name then f tp else tp }

/-- Define and register `p.ast`, the deep definition of `tp`: a `LivenessProperty ρ σ Label` built by
`LivenessProperty.ofFormula` from `[ltl| φ]`, elaborating the formula once. As for an assertion
(`Module.mkVeilTerm`), every `Decidable` instance that cannot be synthesized here, such as one for a quantifier
over a sort or one that exists only at a concrete type, becomes a trailing instance-implicit parameter, which
`#temporal_check` synthesizes at the types it instantiates the module with. The same goes for the
`Enumeration` instances that the temporal quantifiers `∀ x, …`/`∃ x, …` need, such as one for a sort. -/
private def Module.defineTemporalCheck (mod : Module) (tp : TemporalProperty) : CommandElabM Module := do
  let defName := toTemporalAstName tp.name
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .invariantLike {})
  let decParams ← liftTermElabM <| withExporting (isExporting := true) do
    withDeclName ((← getCurrNamespace) ++ defName) do
    let binders ← (baseParams ++ extraParams).mapM (·.binder)
    let body ← `(($(mkIdent ``Veil.LivenessMC.LivenessProperty.ofFormula) $(quote tp.name) [ltl| $(tp.formula)] :
      $(mkIdent ``Veil.LivenessMC.LivenessProperty) $environmentTheory $environmentState $(← mod.labelTypeStx)))
    let (insts, e) ← elabBinders binders fun vs => do
      -- The atoms are read against this module (`elabModuleLtlAtom`)
      let (insts, e) ← withOptions (veil.temporal.moduleAtoms.set · true) <|
        getRequiredDecidableInstances defName body (dsimpSubReaderSubStateRefl >=> foldFieldRepresentationGet)
          (alsoExtract := #[``Veil.Enumeration])
      let e ← Meta.mkLambdaFVars (vs ++ insts.map (·.2)) (← instantiateMVars e)
        (binderInfoForMVars := .instImplicit)
      let e ← instantiateMVars e
      if e.hasMVar then
        let holes ← (← Meta.getMVars e).mapM fun mv => do instantiateMVars (← mv.getType)
        let holes := MessageData.joinSep (holes.toList.map toMessageData) Format.line
        throwError "the definition of `{defName}` still has holes after elaboration, of type(s){indentD holes}"
      pure (insts, e)
    let _ ← addVeilDefinition defName (← Meta.letToHave e)
    return insts.mapIdx fun i (decT, _) =>
      { kind := .definitionParameter defName .typeclass, name := Name.mkSimple s!"{tp.name}_dec_{i}",
        «type» := decT, userSyntax := .missing : Parameter }
  let (mod, decParams) ← liftTermElabM <| mod.canonicalizeExtraParams decParams
  mod.registerDerivedDefinition
    { name := defName, kind := .invariantLike, params := #[], extraParams := extraParams ++ decParams,
      derivedFrom := {}, stx := none }

/-- Define `p`, the shallow definition of `tp`, and record its extra parameters in `tp`. -/
private def Module.defineTemporalVerify (mod : Module) (tp : TemporalProperty) : CommandElabM Module := do
  -- The dependencies decide which extracted `Decidable` parameters `p` binds. The formula needs those of
  -- the actions (bound to their transitions below) and of the ghosts (used in atoms). Only `p._proof` needs
  -- those of `Init`, `NextStep`, `Invariants` and `Assumptions`: its statement mentions them and reuses the
  -- binders of `p` (`Module.getStatementForTemporalTheorems`).
  let ghostDefs := mod._derivedDefinitions.valuesArray.filter fun dd =>
      match dd.kind with | .ghost _ | .theoryGhost _ => true | _ => false
  let dependencies := (Std.HashSet.ofArray (mod.actions.map (·.name)))
    |>.union (Std.HashSet.ofArray (ghostDefs.map (·.name)))
    |>.union (Std.HashSet.ofArray #[assembledInitName, assembledNextStepName,
        assembledInvariantsName, assembledAssumptionsName])
  let dk : DeclarationKind := .derivedDefinition .actionLike dependencies
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) dk
  let baseBinders ← baseParams.mapM (·.binder)
  let extraBinders ← extraParams.mapM (·.binder)
  let allBinders := (← baseBinders.mapM mkImplicitBinder) ++ (← extraBinders.mapM mkImplicitBinder)
  -- Build let bindings for each action's transition relation
  -- For action `send (x : ts)`, generate:
  --   let send := fun x => @send.ext.tr <modArgs> x th
  -- For action `poll` (no params), generate:
  --   let poll := @poll.ext.tr <modArgs> th
  let thIdent := mkVeilImplementationDetailIdent `th
  let mut letBindings : Array (Ident × Term) := #[]
  for act in mod.actions do
    let actTrName := mkIdent <| toTransitionName <| toExtName act.name
    let ((_, modArgs), (specificBinders, specificArgs)) ← mod.declarationSplitBindersArgs act.name act.info.declarationKind
    let specificFunBinders ← specificBinders.mapM bracketedBinderToFunBinder
    let appTerm ← `(@$actTrName $modArgs* $specificArgs* $thIdent)
    let rhs ← mkFunSyntax specificFunBinders appTerm
    letBindings := letBindings.push (mkIdent act.name, rhs)
  -- State fields and ghosts need no bindings: each `⌜ t ⌝` sees them as an assertion does
  -- (`Veil.elabTlfmlStateAtom`).
  -- Assemble the body: let bindings + [tlfml| user_formula ]
  let fullBody ← do
    let body ← letBindings.foldrM (init := ← `([tlfml| $(tp.formula)])) fun (bindName, bindVal) body =>
      `(let $bindName := $bindVal; $body)
    -- Expose immutable theory fields in temporal formulas, matching assertions and ghosts.
    let temporalPredType ← `($(mkIdent ``Lentil.pred) $environmentState)
    let bodyWithTheory ← liftTermElabM <|
      mod.withTheoryAndStateTermTemplate
        [(.theory, thIdent, true)]
        (some temporalPredType)
        (fun _ _ => pure body)
    `(fun ($thIdent : $environmentTheory) => $bodyWithTheory)
  -- Generate the definition
  -- NOTE: We might use `remove_unused_args%` to trim some unused arguments, but
  -- that makes the later use of the temporal property in proofs more complicated,
  -- as we need to figure out which arguments got removed in building its syntax of application
  let cmd ← `(noncomputable def $(mkIdent tp.name) $[$allBinders]* := $fullBody)
  -- The atoms are read against this module (`Veil.elabTlfmlStateAtom`)
  withScope (fun scope => { scope with opts := veil.temporal.moduleAtoms.set scope.opts true }) do
    elabVeilCommand cmd
  return mod.modifyTemporalProperty tp.name ({ · with extraParams })

/-! ## Definition generation and error handling

A property may be declared before the definitions it depends on exist.
- Its deep definition (`.check`, `p.ast`) needs the final action type `Label`.
`Module.ensureSpecIsFinalized` generates `Label` and immediately elaborates all pending deep definitions.
- Its shallow definition (`.verify`, `p`) needs the proof-side `Init`, `NextStep`, `Invariants` and
`Assumptions`. `Module.ensureVerificationSpec` completes verification preparation and immediately
elaborates all pending shallow definitions.

  With `veil.deferVCGeneration`, `#gen_spec` leaves proof-side preparation to the first command
  that needs it, so a shallow definition can remain pending after the spec is finalized.

`checkPending` and `verifyPending` track the two definitions independently. -/

/-- `tp` loses its definition for `side` (`.check` for `p.ast`, `.verify` for `p`), which failed with `errs`.
If `tp` has its other definition too (it did not ask for `(only := …)`), it keeps that one, and the errors
become warnings suggesting `(only := …)`. Otherwise it has no definition left: the errors are reported and
`tp` is forgotten. -/
def Module.dropTemporalDefinition (mod : Module) (tp : TemporalProperty) (side : TemporalTarget)
    (errs : Array Message) : CommandElabM Module := do
  if tp.target matches .both then
    let (rest, kept, failed, keptTarget) := if side.needsCheck
      then (TemporalTarget.verify, "proved", "model-checking", "verify")
      else (TemporalTarget.check, "model checked", "proof", "check")
    -- `logMessage` keeps the positions of the failing subformula, which `logAt` would recompute from a
    -- `Syntax`, but it skips `warningAsError`, which `logAt` applies
    let severity := if warningAsError.get (← getOptions) then MessageSeverity.error else .warning
    for e in errs do
      logMessage { e with severity, data := m!"`{tp.name}` is only {kept}, since its {failed} \
        definition fails to elaborate (write `temporal (only := {keptTarget})` to say so):{indentD e.data}" }
    return mod.modifyTemporalProperty tp.name ({ · with target := rest })
  -- Already logged once through `logAt`, these keep their positions and context
  for e in errs do logMessage e
  -- Forget `tp`
  return { mod with
    temporalProperties := mod.temporalProperties.filter (·.name != tp.name)
    _declarations := mod._declarations.erase tp.name }

/-- Whether a definition of `tp` that `side` needs (`.check` for `p.ast`, `.verify` for `p`) is yet to be
generated. -/
private def TemporalProperty.isPending (tp : TemporalProperty) (side : TemporalTarget) : Bool :=
  (side.needsCheck && tp.checkPending) || (side.needsVerify && tp.verifyPending)

private def TemporalProperty.clearPending (tp : TemporalProperty) (side : TemporalTarget) : TemporalProperty :=
  { tp with
    checkPending := tp.checkPending && !side.needsCheck
    verifyPending := tp.verifyPending && !side.needsVerify }

/-- Generate the definition of `tp` for `side`, handling failures through `Module.dropTemporalDefinition`
and clearing its pending flag. -/
def Module.generateTemporalDefinition (mod : Module) (tp : TemporalProperty) (side : TemporalTarget) :
    CommandElabM Module := do
  let sideName := if side.needsCheck then "check" else "verify"
  withTraceNode (`veil.perf.elaborator.temporal ++ tp.name) (fun _ => return s!"temporal {tp.name} ({sideName})") do
    let define := if side.needsCheck then mod.defineTemporalCheck tp else mod.defineTemporalVerify tp
    let mod ← match ← commitIfNoErrors define with
      | .ok mod => pure mod
      | .error errs => mod.dropTemporalDefinition tp side errs
    return mod.modifyTemporalProperty tp.name (·.clearPending side)

/-- Generate all pending temporal definitions for `side`. -/
def Module.generatePendingTemporalDefinitions (mod : Module) (side : TemporalTarget) : CommandElabM Module :=
  mod.temporalProperties.foldlM (init := mod) fun mod tp =>
    if tp.isPending side then mod.generateTemporalDefinition tp side else pure mod

end Veil
