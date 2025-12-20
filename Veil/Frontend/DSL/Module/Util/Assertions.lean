import Veil.Frontend.DSL.Module.Util.StateTheory

open Lean Parser Elab Command Term Meta Tactic

namespace Veil

/-! ## Data Types -/

inductive TheoryAndStateTermTemplateArgKind where
  | theory
  /-- When the concrete field representation is not used,
  `suffix` is the suffix to append to each field after
  destructing a state.

  When the concrete field representation is used,
  `suffixConc` is the suffix to append to each field after
  destructing a state, and `suffix` is the suffix appended to
  each field's _original name_ (i.e., not the one after appending
  `suffixConc`) after applying `FieldRepresentation.get` to
  the concrete field.

  When either is `none`, no suffix is appended in the corresponding case. -/
  | state (suffix suffixConc : Option String)

/-! ## Assertion Creation & Registration -/

def _root_.Lean.TSyntax.getPropertyName (stx : TSyntax `propertyName) : Name :=
  match stx with
  | `(propertyName| [$id]) => id.getId
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

def Module.registerAssertion [Monad m] [MonadError m] (mod : Module) (sc : StateAssertion) : m Module := do
  mod.throwIfAlreadyDeclared sc.name
  let mut mod := { mod with assertions := mod.assertions.push sc, _declarations := mod._declarations.insert sc.name sc.declarationKind }
  for set in sc.inSets do
    let currentAssertions := mod._assertionSets.getD set Std.HashSet.emptyWithCapacity
    mod := { mod with _assertionSets := mod._assertionSets.insert set (currentAssertions.insert sc.name) }
  return mod

/-! ## Tactic Infrastructure -/

section AssertionElab

syntax (name := veil_exact_theory) "veil_exact_theory" : tactic
syntax (name := veil_exact_state) "veil_exact_state" : tactic

/-- Reconstruct a `Theory` term from the hypotheses in the context. -/
def elabExactTheory : TacticM Unit := do
  let mod ← getCurrentModule
  let comp := mod.immutableComponents.map (Lean.mkIdent ·.name)
  let constr <- `(term| (⟨$[$comp],*⟩ : $(← mod.theoryStx)))
  trace[veil.debug] "theory constr: {constr}"
  Tactic.evalTactic $ ← `(tactic| exact $constr)

def elabExactState : TacticM Unit := withMainContext do
  let mod ← getCurrentModule
  let comp := mod.mutableComponents.map (·.name)
  -- find all available state components in the local context
  let lctx ← getLCtx
  let some ldecls := comp.mapM (m := Option) lctx.findFromUserName?
    | throwError "not all state components are available in the local context"
  let actualFields : Array Term ← if mod._useFieldRepTC
    then
      -- find the concrete field from the _values_ of `ldecls`
      -- here, only use some simple heuristics to do the matching
      ldecls.mapM fun ldecl => do
        let some v := ldecl.value? true
          | throwError "state component {ldecl.userName} has no value in the local context"
        let v := match_expr v with
          | id _ vv => vv | _ => v
        match_expr v with
        | Veil.FieldRepresentation.get _ _ _ _ cf =>
          if let .fvar fv := cf
          then let nm ← fv.getUserName ; `(term| $(mkIdent nm) )
          else delabVeilExpr cf
        | _ => throwError "unable to extract concrete field from state component {ldecl.userName}"
    else
      ldecls.mapM fun a => `(term| $(mkIdent a.userName) )
  -- NOTE: It is very weird that if not doing it using `exact`
  -- (e.g., instead constructing the state `Expr` and using
  -- `closeMainGoalUsing`), then some meta-variable (e.g.,
  -- `IsSubStateOf` arguments) synthesis will fail.
  let constr ← `(term| (⟨$[$actualFields],*⟩ : $(← mod.stateStx mod._useFieldRepTC)))
  trace[veil.debug] "state constr: {constr}"
  Tactic.evalTactic $ ← `(tactic| exact $constr)

elab_rules : tactic
  | `(tactic| veil_exact_theory) => elabExactTheory
  | `(tactic| veil_exact_state) => elabExactState

/-! ## Theory/State Template Infrastructure -/

/-- Given `t : Prop` which accesses fields of theory and/or state,
returns the proper "wrapper" term which pattern-matches over theory
and/or and state, thus making all their fields accessible in `t`.
`t` can depend on the field names of theory and state. The pattern-matches
are generated according to `targets`.
- `stateSortTerm`: Optional term to use as the sort argument for state casesOn.
  If not provided, uses `mod.sortIdentsForTheoryOrState mod._useFieldRepTC`. -/
def Module.withTheoryAndStateTermTemplate (mod : Module)
  (targets : List (TheoryAndStateTermTemplateArgKind × Ident))
  (t : Array Ident /- field names of theory -/ →
       Array Ident /- field names of state -/ →
       MetaM (TSyntax `term))
  (fieldRepInstance : Term := fieldRepresentation)
  (stateSortTerm : Option Term := none)
  : MetaM (TSyntax `term) := do
  let motive := mkIdent `motive
  let (theoryName, stateName) := (mod.name ++ theoryName, mod.name ++ stateName)
  let casesOnTheory := theoryName ++ `casesOn
  let casesOnState := stateName ++ `casesOn
  let theoryFields ← getFieldIdentsForStruct theoryName
  let stateFields ← getFieldIdentsForStruct stateName
  let stateFieldsWithSuffix suf : Array Ident :=
    stateFields.map fun (f : Ident) => f.getId.appendAfter suf |> Lean.mkIdent
  let t ← t theoryFields stateFields
  targets.foldrM (init := t) fun (kind, i) body => do
    match kind with
    | .theory =>
      let tmp ← mkFunSyntax theoryFields body
      `(term|
        @$(mkIdent casesOnTheory) $(← mod.sortIdents)*
        ($motive := fun _ => Prop)
        ($(mkIdent ``readFrom) $i)
        ($tmp))
    | .state suffix suffixConc =>
      let sfs := suffix.elim stateFields stateFieldsWithSuffix
      let sfsConc := suffixConc.elim stateFields stateFieldsWithSuffix
      let body' ← if !mod._useFieldRepTC then pure body else
        -- annotate types here, otherwise there can be issues like: for `f a`
        -- where `f` has a complicated type but definitionally equal to `node → Bool`,
        -- coercions will not be inserted to make `f a` into `Prop`
        -- (notice that `decide` expects a `Prop` argument here)
        let fieldTypes ← mod.mutableComponents.mapM (·.typeStx)
        let bundled := sfs.zip fieldTypes |>.zip sfsConc
        bundled.foldrM (init := body) fun ((f, ty), fConc) b => do
          `(let $f:ident : $ty := ($fieldRepInstance _).$(mkIdent `get) $fConc:ident ; $b)
      let tmp ← mkFunSyntax (if !mod._useFieldRepTC then sfs else sfsConc) body'
      let sortTerms ← match stateSortTerm with
        | some sortTerm => pure #[sortTerm]
        | none => pure (← mod.sortIdentsForTheoryOrState mod._useFieldRepTC)
      `(term|
        @$(mkIdent casesOnState) $sortTerms*
        ($motive := fun _ => Prop)
        ($(mkIdent ``getFrom) $i)
        ($tmp))

/-! ## Convenience Wrappers -/

/-- This is used wherever we want to define a predicate over the
background theory (e.g. in `assumption` definitions). Instead of
writing `fun th => Pred`, this will pattern-match over the theory and
make all its fields accessible for `Pred`. -/
def withTheory (t : Term) (fieldRepInstance : Term := fieldRepresentation) : MetaM (Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Term) := do
  let mut mod ← getCurrentModule
  let th := mkIdent `th
  let fn ← do
    let tmp ← mod.withTheoryAndStateTermTemplate [(.theory, th)] (fun _ _ => pure t) fieldRepInstance
    `(term| (fun ($th : $environmentTheory) => $tmp))
  -- See NOTE(SUBTLE) to see why this is not actually ill-typed.
  let binders := #[← `(bracketedBinder| ($th : $environmentTheory := by veil_exact_theory))]
  return (binders, ← `(term|$fn $th))

/-- This is used wherever we want to define a predicate over the
background theory and the mutable state (e.g. in `invariant`
definitions). Instead of writing `fun th st => Pred`, this will
pattern-match over the theory and state and make all their fields
accessible for `Pred`. This was previously called `funcasesM`. -/
def withTheoryAndState (t : Term) : MetaM (Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Term) := do
  let mut mod ← getCurrentModule
  let (th, st) := (mkIdent `th, mkIdent `st)
  let fn ← do
    let tmp ← mod.withTheoryAndStateTermTemplate [(.theory, th), (.state .none "_conc", st)] (fun _ _ => pure t)
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
def withTheoryAndStateFn (mod : Module) (t : Term) (theoryT stateT : Term)
    (fieldRepInstance : Term) (stateSortTerm : Term) : MetaM Term := do
  let (th, st) := (mkIdent `th, mkIdent `st)
  let tmp ← mod.withTheoryAndStateTermTemplate
    [(.theory, th), (.state .none "_conc", st)]
    (fun _ _ => pure t)
    fieldRepInstance
    (stateSortTerm := some stateSortTerm)
  `(term| (fun ($th : $theoryT) ($st : $stateT) => $tmp))

/-! ## Term Creation -/

/-- Implicitly quantifies capital variables and elaborates the term with all
state and theory variables bound (or just theory if `justTheory` is true). -/
def Module.mkVeilTerm (mod : Module) (name : Name) (dk : DeclarationKind) (params : Option (TSyntax `Lean.explicitBinders)) (term : Term) (justTheory : Bool := false) : TermElabM (Array Parameter × Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Term × Term) := do
  let baseParams ← mod.declarationBaseParams dk
  let binders ← baseParams.mapM (·.binder)
  let paramBinders ← Option.stxArrMapM params toBracketedBinderArray
  -- We don't `universallyQuantifyCapitals` after `withTheory` /
  -- `withTheoryAndState` because we want to have the universal
  -- quantification as deeply inside the term as possible, rather than above
  -- the binders for `rd` and `st` introduced below.
  let body ← `(uqc% ($term:term))
  let (thstBinders, term') ← if justTheory then withTheory body else withTheoryAndState body
  let term' := Syntax.inheritSourceSpanFrom term' term
  -- Record the `Decidable` instances that are needed for the assertion.
  let (insts, _) ← elabBinders (binders ++ paramBinders ++ thstBinders) $ fun _ => getRequiredDecidableInstances term'
  trace[veil.debug] "insts: {insts.map (·.1)}"
  let extraParams : Array Parameter := insts.mapIdx (fun i (decT, _) => { kind := .definitionParameter name .typeclass, name := Name.mkSimple s!"{name}_dec_{i}", «type» := decT, userSyntax := .missing })
  return (extraParams, thstBinders, term', body)

end AssertionElab

end Veil
