module

public meta import Veil
public meta import Veil.Frontend.DSL.Module.VCGen.Common
public meta import Veil.Core.Tools.Synthesizer.Render

/-!
# Solver queries

Every question UPDR asks is the satisfiability of a conjunction over the module's assembled
transition system:

`assumptions th ∧ [init th s₀] ∧ F th s₀ ∧ tr th s₀ s₁ ∧ … ∧ tr th sₖ₋₁ sₖ ∧ G th sₖ`,

where `F` is a frame and `G` the negation of a predicate or the literals of a diagram. This file
writes the universally quantified negation of such a conjunction as a `Term`, the statement that
Veil's tactic pipeline then proves or refutes.

## Main definitions

* `Veil.Synthesizer.QueryCtx`: the syntax shared by the queries about one module.
* `Veil.Synthesizer.Query`: the shape of a query.
* `Veil.Synthesizer.QueryCtx.statement`: the statement of a query.
* `Veil.Synthesizer.QueryPhases`: the time the queries of this process spent in each phase.

## Implementation notes

* A transition is the disjunction over the actions `tag = a ∧ tr th s (Label.a args) s'`, with a
  variable `tag` of the module's `ActionTag` type and one variable per action parameter, named the
  way Veil's trace decoder expects, so that a model decodes through `buildTraceFromModel`.
* Predicates are asserted under one theory and state binder, since Veil's preprocessing pays for
  every binder it destructures. Capitals are quantified per predicate with `uqc%`.
* A diagram is asserted *skolemized*: its existential variables become universally bound variables
  of the statement and each literal a hypothesis, so that an unsat core names literals.
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Term Meta Veil Lean.Parser.Term

/-- The syntax shared by the queries about one module. -/
structure QueryCtx where
  /-- The module. -/
  mod : Veil.Module
  /-- The module's uninterpreted sort parameters. -/
  sorts : Array Ident
  /-- The binders of the sort parameters. -/
  sortBinders : Array (TSyntax ``bracketedBinder)
  /-- The binders of the typeclass instances. -/
  typeclassBinders : Array (TSyntax ``bracketedBinder)
  /-- The theory variable. -/
  th : Ident
  /-- The theory type. -/
  theoryT : Term
  /-- The state type. -/
  stateT : Term
  /-- The module's assembled relational transition system. -/
  rtsExpr : Term
  /-- The field representation of the state type, for `withTheoryAndStateFn`. -/
  fieldRepInstance : Term
  /-- The field type of the state type, for `withTheoryAndStateFn`. -/
  stateSortTerm : Term

/-- The query context of a module. -/
def QueryCtx.ofModule (mod : Veil.Module) : TermElabM QueryCtx := do
  let sorts ← mod.uninterpretedParamIdents
  let typeclassParams := mod.parameters.filter fun p ↦
    p.kind matches .moduleTypeclass .sortAssumption | .moduleTypeclass .userDefined
  return {
    mod, sorts
    sortBinders := ← mod.uninterpretedParamBinders
    typeclassBinders := ← typeclassParams.mapM (·.binder)
    th := mkIdent `th
    theoryT := ← mod.theoryStx
    stateT := ← `($(mkIdent stateName) ($fieldAbstractDispatcher $sorts*))
    rtsExpr := ← `(@$assembledRTS $sorts*)
    fieldRepInstance := ← `($instAbstractFieldRepresentation $sorts*)
    stateSortTerm := ← `($fieldAbstractDispatcher $sorts*) }

/-- The identifier of the `i`-th state of a query. -/
def stateIdent (i : Nat) : Ident := mkIdent (.mkSimple s!"st{i}")

/-- What a query asserts of its last state. -/
inductive Goal where
  /-- The negation of a predicate. -/
  | violates (p : Term)
  /-- The literals of a diagram, over element variables of the given sorts. -/
  | diagram (vars : Array SortName) (lits : Array Term)

/-- The shape of a query: `assumptions th ∧ [init th s₀] ∧ frame s₀ ∧ tr s₀ s₁ ∧ … ∧ goal sₖ` for
`k` transitions. -/
structure Query where
  /-- Whether the first state is initial. -/
  init : Bool := false
  /-- The predicates that hold in the first state. -/
  frame : Array Term := #[]
  /-- Assert each predicate of the frame as its own hypothesis. -/
  separate : Bool := false
  /-- The number of transitions. -/
  steps : Nat := 0
  /-- What the query asserts of the last state. -/
  goal : Goal

namespace QueryCtx

variable (ctx : QueryCtx)

/-- A predicate over the module's theory and state, `fun th st ↦ t` with the capitals of `t`
universally quantified. -/
def wrapPred (t : Term) : TermElabM Term := do
  withTheoryAndStateFn ctx.mod (← `(uqc% (($t:term) : Prop))) (some (← `(Prop)))
    ctx.theoryT ctx.stateT ctx.fieldRepInstance ctx.stateSortTerm

/-- A predicate applied to the state `st`. -/
def applyPred (t : Term) (st : Ident) : TermElabM Term := do
  `(($(← ctx.wrapPred t) $(ctx.th) $st))

/-- The conjunction of predicates applied to the state `st`, under one binder, or each under its
own when `separate`. -/
def applyPreds (ts : Array Term) (st : Ident) (separate : Bool := false) :
    TermElabM (Array Term) := do
  if ts.isEmpty then return #[]
  if separate then return ← ts.mapM (ctx.applyPred · st)
  let conj ← repeatedAnd (← ts.mapM fun t ↦ `((uqc% (($t:term) : Prop))))
  let w ← withTheoryAndStateFn ctx.mod conj (some (← `(Prop)))
    ctx.theoryT ctx.stateT ctx.fieldRepInstance ctx.stateSortTerm
  return #[← `(($w $(ctx.th) $st))]

/-- `⋁ₐ (tag = a ∧ tr th curr (Label.a args) next)` for transition `i`, with the binders of its
tag and arguments. The step is written with the normalized transition relation `trNorm?` when
given. A module without actions has no transitions. -/
def stepDisjunction (trNorm? : Option Name) (i : Nat) (curr next : Ident) :
    TermElabM (Term × Array (TSyntax ``bracketedBinder)) := do
  if ctx.mod.actions.isEmpty then return (← `(False), #[])
  let tag := mkIdent (.mkSimple s!"_tr{i}_tag")
  let mut binders := #[← `(bracketedBinder| ($tag : $actionTagType))]
  let mut disjuncts := #[]
  for act in ctx.mod.actions do
    let (_, params) ← ctx.mod.declarationAllParams act.name act.declarationKind
    let args := params.mapIdx fun j p ↦
      mkIdent (.mkSimple s!"_tr{i}_act_{act.name}_arg{j}_{p.name}")
    for (a, p) in args.zip params do
      binders := binders.push (← `(bracketedBinder| ($a : $(p.type))))
    let lbl ← `(($(mkIdent (labelTypeName ++ act.name)) $args*))
    let step ← match trNorm? with
      | some n => `($(mkIdent n) $(ctx.sorts)* $(ctx.th) $curr $lbl $next)
      | none => `(($(ctx.rtsExpr)).$(mkIdent `tr) $(ctx.th) $curr $lbl $next)
    let tagValue := mkIdent (actionTagEnumInstName ++ act.name)
    disjuncts := disjuncts.push (← `(($tag = $tagValue ∧ $step)))
  return (← repeatedOr disjuncts, binders)

/-- The statement of query `q`: the negation of its conjunction, universally quantified over the
module's sorts and instances, the `ActionTag` type when there are transitions, the tag, argument
and diagram variables, the theory and the states. -/
def statement (trNorm? : Option Name) (q : Query) : TermElabM Term := do
  let rts := ctx.rtsExpr
  let mut conj := #[← `(($rts).$(mkIdent `assumptions) $(ctx.th))]
  if q.init then conj := conj.push (← `(($rts).$(mkIdent `init) $(ctx.th) $(stateIdent 0)))
  conj := conj ++ (← ctx.applyPreds q.frame (stateIdent 0) q.separate)
  let mut binders := #[]
  for i in [:q.steps] do
    let (tr, bs) ← ctx.stepDisjunction trNorm? (i + 1) (stateIdent i) (stateIdent (i + 1))
    conj := conj.push tr
    binders := binders ++ bs
  let last := stateIdent q.steps
  match q.goal with
  | .violates p => conj := conj.push (← `(¬ $(← ctx.applyPred p last)))
  | .diagram vars lits =>
    conj := conj ++ (← ctx.applyPreds lits last)
    binders := binders ++
      (← vars.mapIdxM fun i s ↦ `(bracketedBinder| ($(varIdent i) : $(mkIdent s))))
  let tagBinders ← if q.steps > 0 && !ctx.mod.actions.isEmpty then
      pure #[← `(bracketedBinder| ($actionTagType : Type)),
        ← `(bracketedBinder|
          ($actionTagEnumInst : $(Ident.toEnumClass actionTagType) $actionTagType))]
    else pure #[]
  let allBinders := ctx.sortBinders ++ ctx.typeclassBinders ++ tagBinders ++ binders
  let states := (Array.range (q.steps + 1)).map stateIdent
  `(∀ $allBinders* ($(ctx.th) : $(ctx.theoryT)) ($states* : $(ctx.stateT)), ¬ $(← repeatedAnd conj))

end QueryCtx

/-- Wall-clock milliseconds the queries of this process spent in each phase. -/
structure QueryPhases where
  /-- Elaborating statements. -/
  elabMs : Nat := 0
  /-- Veil's preprocessing of statements. -/
  preprocessMs : Nat := 0
  /-- The `smt` tactic: translation, solving and proof reconstruction. -/
  smtMs : Nat := 0
  /-- Decoding models. -/
  decodeMs : Nat := 0
  /-- Normalizing transition relations, outside any query. -/
  normalizeMs : Nat := 0
deriving Repr, Inhabited

/-- The phase times of `a` minus those of `b`. -/
def QueryPhases.sub (a b : QueryPhases) : QueryPhases where
  elabMs := a.elabMs - b.elabMs
  preprocessMs := a.preprocessMs - b.preprocessMs
  smtMs := a.smtMs - b.smtMs
  decodeMs := a.decodeMs - b.decodeMs
  normalizeMs := a.normalizeMs - b.normalizeMs

initialize queryPhases : IO.Ref QueryPhases ← IO.mkRef {}

/-- Add the milliseconds since `t0` to the phase `f` updates. -/
def notePhase (f : QueryPhases → Nat → QueryPhases) (t0 : Nat) : IO Unit := do
  let dt := (← IO.monoMsNow) - t0
  queryPhases.modify (f · dt)

end Veil.Synthesizer
