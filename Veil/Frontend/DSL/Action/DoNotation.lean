import Lean
import Lean.Parser
import Veil.Frontend.DSL.Action.Syntax
-- TODO FIXME: factor out Velvet syntax from Loom core
import Veil.Frontend.DSL.Action.Semantics.WP
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Action.TupleUpdate


open Lean Elab Command Term Meta Lean.Parser

/-! # Custom do-notation for Veil actions

  This file implements a custom do-notation for Veil actions. It's
  probably the hackiest part of Veil right now, and difficult to
  maintain. Once the Lean FRO ships its extensible do-notation, we
  should port over as soon as possible.

-/

namespace Veil

abbrev doSeq := TSyntax ``Term.doSeq
abbrev doSeqItem := TSyntax ``Term.doSeqItem

syntax "let" term ":" term ":|" term : doElem

/--
Lean's built-in `if h : p then ...` do-element parser only accepts an identifier
for `h`. Veil's if-some syntax also allows tuple witnesses such as
`if (x, y) : p x y then ...`, so we add a parser that accepts a term-shaped
witness and desugar it below.
-/
@[doElem_parser high] def ifSomeDo := leading_parser
  "if " >> termParser maxPrec >> " : " >> termParser >> " then " >>
  Lean.Parser.Term.doSeq >> optional ("else " >> Lean.Parser.Term.doSeq)

/--
In an action block, `veil_let x := v` gives a name to `v` without eagerly
inlining it during verification.

**WARNING**: The right-hand side `v` should be a pure expression.
-/
-- NOTE: Do not replace this with `syntax ... : doElem`. Since term-level `veil_let`
-- is also a term parser, Lean's ordinary `doReassign` parser can otherwise
-- consume an action block fragment like `veil_let x := v; y := x` as
-- `(veil_let x := v; y) := x`.
@[doElem_parser high] def veilLetDo := leading_parser
  "veil_let " >> Lean.Parser.Term.letDecl

/--
In a term, `veil_let x := v; body` gives a name to `v` inside `body` without
eagerly inlining it during verification. The semicolon before `body` is part of
the syntax.
-/
-- NOTE: We intentionally require an explicit semicolon here instead of Lean's
-- `optSemicolon`; otherwise this term parser may capture the next do/action
-- statement as the body of the term-level `veil_let`.
@[term_parser]
def veilLetTerm := leading_parser:leadPrec
  withPosition ("veil_let " >> Lean.Parser.Term.letDecl) >>
  "; " >> termParser

macro_rules
  | `(veil_let $decl:letDecl; $body:term) => do
    let letEq := mkIdent ``Veil.letEq
    let thisId := mkIdent `this
    match decl with
    | `(letDecl| $x:ident := $t:term) => `($letEq $t (fun $x:ident => $body))
    | `(letDecl| $x:ident : $ty:term := $t:term) => `($letEq ($t : $ty) (fun ($x:ident : $ty) => $body))
    | `(letDecl| $x:term := $t:term) => `($letEq $t (fun $x:term => $body))
    | `(letDecl| $x:term : $ty:term := $t:term) => `($letEq ($t : $ty) (fun $x:term => $body))
    | `(letDecl| := $t:term) => `($letEq $t (fun $thisId:ident => $body))
    | `(letDecl| : $ty:term := $t:term) => `($letEq ($t : $ty) (fun $thisId:ident => $body))
    | _ => Macro.throwUnsupported

/- See:
 - https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Pattern.20match.20and.20name.20binder.20.60none.60/near/514568614
 - https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.60reducible.60.20bug.20with.20.60namedPattern.60s.3F/near/534955024

for information around how this works and different options for
implementing this functionality. In a previous version of Veil, we used
the `@_` trick (which allowed us to destruct everything once, which
apparently had better performance), but since we now need to maintain
definitional equality (to enable typeclass inference to work
correctly), we use projections.
-/

/-- Make available the (immutable) theory with `let` binders. Only called once. -/
def makeTheoryAvailable [Monad m] [MonadEnv m] [MonadQuotation m] (mod : Module) : m (Array doSeqItem) := do
  let thVar := mkVeilImplementationDetailName `theory
  let readTheory ← `(Term.doSeqItem| let $(mkIdent thVar) := (← $(mkIdent ``read)))
  let bindFields ← mod.immutableComponents.mapM (fun f => return ← `(Term.doSeqItem| let $(mkIdent f.name) := $(mkIdent thVar).$(mkIdent f.name)))
  return #[readTheory] ++ bindFields

private abbrev concreteFieldFromName (nm : Name) : Ident := mkIdent <| Name.mkSimple s!"{nm}_conc"

/-- Called in the preamble, to make available `let mut` binders for the state. Only called once. -/
def makeStateAvailable [Monad m] [MonadEnv m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array doSeqItem) := do
  let stVar := mkVeilImplementationDetailName `state
  let getState ← `(Term.doSeqItem| let mut $(mkIdent stVar) := (← $(mkIdent ``get)))
  let bindFields ← mod.mutableComponents.flatMapM fun f => do
    if mod._useFieldRepTC then
      let concreteField := concreteFieldFromName f.name
      -- If we are using the field representation typeclass, we need to make
      -- both concrete fields and their abstracted versions (through `.get`) available.
      -- Annotating the type here is necessary to avoid unification issues.
      let ty ← f.typeStx
      let b1 ← `(Term.doSeqItem| let mut $concreteField := $(mkIdent stVar).$(mkIdent f.name))
      let b2 ← `(Term.doSeqItem| let mut $(mkIdent f.name) : $ty := ($fieldRepresentation _).$(mkIdent `get) $concreteField)
      return #[b1, b2]
    else
      return #[← `(Term.doSeqItem| let mut $(mkIdent f.name) := $(mkIdent stVar).$(mkIdent f.name))]
  return #[getState] ++ bindFields

/-- Refresh the state variables. -/
def getState [Monad m] [MonadEnv m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array doSeqItem) := do
  let stVar := mkVeilImplementationDetailName `state
  let getState ← `(Term.doSeqItem| $(mkIdent stVar):ident := (← $(mkIdent ``get)))
  let bindFields ← mod.mutableComponents.flatMapM fun f => do
    if mod._useFieldRepTC then
      -- slightly repeating code, but anyway
      let concreteField := concreteFieldFromName f.name
      let ty ← f.typeStx
      let b1 ← `(Term.doSeqItem| $concreteField:ident := $(mkIdent stVar).$(mkIdent f.name))
      -- NOTE: It seems that the type annotation syntax is not allowed on the
      -- LHS of an assignment, so use the `id` hack.
      let b2 ← `(Term.doSeqItem| $(mkIdent f.name):ident := @$(mkIdent ``id) ($ty) (($fieldRepresentation _).$(mkIdent `get) $concreteField))
      return #[b1, b2]
    else
      return #[← `(Term.doSeqItem| $(mkIdent f.name):ident := $(mkIdent stVar).$(mkIdent f.name))]
  return #[getState] ++ bindFields

/-- Does this statement run a (potentially state-modifying) VeilM
sub-computation embedded via `(← e)`?

By the time the assignment cases of `expandDoElemVeil` run, the bind-arrow
forms (`v ← t`, `r a ← t`) have already been normalized into `:= ←`, i.e. the
embedded computation appears as a `Term.liftMethod` (`(← e)`) node. We detect
*any* such node anywhere in the statement.

This is deliberately an over-approximation: refreshing the cached state binders
after a statement that did *not* actually modify the state is harmless (it
re-reads the same values), whereas *failing* to refresh after one that did is a
silent soundness bug (a stale read). So when in doubt, we refresh. A `←`
belonging to a nested `do` still denotes a computation in the *same* VeilM monad
when it runs, so refreshing after it is still correct. -/
def stmtRunsComputation (stx : Syntax) : Bool :=
  (stx.find? (·.isOfKind ``Lean.Parser.Term.liftMethod)).isSome

/-- Append a state refresh when `stx` contains an embedded computation. -/
private def appendStateRefreshIfNeeded (mod : Module) (stx : Syntax)
    (items : Array doSeqItem) : TermElabM (Array doSeqItem) := do
  if stmtRunsComputation stx then
    return items ++ (← getState mod)
  return items

macro_rules
  | `(assume  $t) => `($(mkIdent ``VeilM.assume) $t)
  | `(pick   $t)  => `($(mkIdent ``MonadNonDet.pick) $t)
  | `(pick)       => `($(mkIdent ``MonadNonDet.pick) _)
  | `(doElem| let $x:term :| $p) => `(doElem| let $x:term ← $(mkIdent ``VeilM.pickSuchThat):ident _ (fun $x => $p))
  | `(doElem| let $x:term : $ty:term :| $p) => `(doElem| let $x:term ← $(mkIdent ``VeilM.pickSuchThat):ident $ty (fun $x => $p))

/-- Parse a tuple of identifiers. Note that the syntax of tuple seems non-trivial. -/
private def collectIfSomeBinderIdents (pat : Term) : TermElabM (Array Ident) := do
  match pat with
  | `(term| $x:ident) => return #[x]
  | `(($_:hygieneInfo $x:ident, $xs:ident,*)) => return #[x] ++ xs.getElems
  | _ => throwErrorAt pat "unsupported witness pattern for Veil `if-some`; expected an identifier or tuple of identifiers"

mutual
partial def expandDoSeqVeil (proc : Name) (stx : doSeq) : TermElabM (Array doSeqItem) :=
  match stx with
  | `(doSeq| $doS:doSeqItem*) => return Array.flatten $ ← doS.mapM (expandDoElemVeil proc)
  | _ => throwErrorAt stx s!"unexpected syntax of Veil do-notation sequence {stx}"

partial def expandDoElemVeil (proc : Name) (stx : doSeqItem) : TermElabM (Array doSeqItem) := do
  let mod ← getCurrentModule (errMsg := "You cannot use Veil do-notation outside of a Veil module!")
  match stx with
  -- Ignore semicolons
  | `(Term.doSeqItem| $stx ;) => expandDoElemVeil proc $ ← `(Term.doSeqItem| $stx:doElem)
  | `(Term.doSeqItem| veil_var $x:ident : $ty:term) => do
    let pickItem ← `(Term.doSeqItem| let $x:ident ← pick ($ty:term))
    let mutItem ← `(Term.doSeqItem| let mut $x:ident := $x:ident)
    return (← expandDoElemVeil proc pickItem) ++ (← expandDoElemVeil proc mutItem)
  | `(Term.doSeqItem| veil_let $decl:letDecl) => do
    let eqWS := mkIdent ``Veil.eqWithoutSubst
    let thisId := mkIdent `this
    let el ← match decl with
      | `(letDecl| $x:ident := $t:term) =>
        `(Term.doSeqItem| let $x:ident :| $eqWS:ident $x:ident $t)
      | `(letDecl| $x:ident : $ty:term := $t:term) =>
        `(Term.doSeqItem| let $x:ident : $ty:term :| $eqWS:ident $x:ident ($t : $ty))
      | `(letDecl| $x:term := $t:term) =>
        `(Term.doSeqItem| let $x:term :| $eqWS:ident $x:term $t)
      | `(letDecl| $x:term : $ty:term := $t:term) =>
        `(Term.doSeqItem| let $x:term : $ty:term :| $eqWS:ident $x:term ($t : $ty))
      | `(letDecl| := $t:term) =>
        `(Term.doSeqItem| let $thisId:ident :| $eqWS:ident $thisId:ident $t)
      | `(letDecl| : $ty:term := $t:term) =>
        `(Term.doSeqItem| let $thisId:ident : $ty:term :| $eqWS:ident $thisId:ident ($t : $ty))
      | _ => throwErrorAt stx "unsupported `veil_let` declaration"
    return #[el]
  -- Ordinary local `let`s do not mutate state. Refresh only if their initializer
  -- runs an embedded VeilM computation via `(← ...)`.
  | `(Term.doSeqItem| let $decl:letDecl) =>
    appendStateRefreshIfNeeded mod decl.raw #[stx]
  | `(Term.doSeqItem| let mut $decl:letDecl) =>
    appendStateRefreshIfNeeded mod decl.raw #[stx]
  -- `pure $t` where `$t` embeds a state-modifying computation (e.g.
  -- `pure (← act)`): Lean lifts the `←` out and runs it, mutating the state,
  -- so the cached binders must be refreshed before any later read. We handle it
  -- exactly like a bare-term statement below (bind the value, refresh, then
  -- re-emit `pure b`): this preserves the statement's return value *and*
  -- refreshes the state. (Effect-free `pure`, incl. the auto-inserted
  -- `pure ()`, has no `←` and falls through to the cheap passthrough.)
  --
  -- NOTE: this only covers a single, statement-level `pure (← …)`. A `term`
  -- may still embed binds in positions we don't special-case; that residual is
  -- the FIXME below, unfixable in general until Lean ships an extensible
  -- do-notation. `return $t` needs no refresh: it short-circuits the rest of
  -- the block, so no later statement reads the (stale) binders.
  | `(Term.doSeqItem| pure $t:term) =>
    if stmtRunsComputation t then
      let b := mkIdent <| ← mkFreshUserName `_bind
      let bind ← `(Term.doSeqItem| let $b:ident ← $(mkIdent ``pure):ident $t:term)
      return #[bind] ++ (← getState mod) ++ #[← `(Term.doSeqItem| $(mkIdent ``pure):ident $b:ident)]
    return #[stx]
  -- We don't want to introduce state updates after statements that cannot
  -- affect any later read, so we pass these through unchanged.
  -- FIXME: we could have `pure (← state_modifying_action)`, so this isn't
  -- sound. In general, you could even have multiple binds in a single
  -- `term`, so this entire approach is broken and really unfixable until
  -- Lean ships an extensible do-notation. It's best-effort for now.
  | `(Term.doSeqItem| return $t:term)
  -- NOTE: all the expressions in `require`, `assert`, and `assume`,
  -- `pick-such-that` and `if` need to be `Decidable` for execution.
  | `(Term.doSeqItem| let $_ :| $t)
  => return #[stx]
  -- `pick` itself does not modify state, but a computation embedded in its
  -- binder or type (e.g. `pick (Fin (← proc))`) can. Refresh afterward so
  -- later field reads see the state written by that computation.
  | `(Term.doSeqItem| let $_ : $_ ← pick $_) | `(Term.doSeqItem| let $_ : $_ ← pick)
  | `(Term.doSeqItem| let $_ ← pick $_) | `(Term.doSeqItem| let $_ ← pick) =>
    appendStateRefreshIfNeeded mod stx.raw #[stx]
  | `(Term.doSeqItem| assume $t) =>
    appendStateRefreshIfNeeded mod t.raw #[stx]
  -- We elaborate `require` and `assert` here, since we need to record
  -- which procedure they belong to
  | `(Term.doSeqItem| require $t) =>
    let assertId ← mkNewAssertion proc stx
    let requireItem ← `(Term.doSeqItem| $(mkIdent ``VeilM.require):ident $t $(Syntax.mkNatLit assertId.toNat))
    appendStateRefreshIfNeeded mod t.raw #[requireItem]
  | `(Term.doSeqItem| assert $t) =>
    let assertId ← mkNewAssertion proc stx
    let assertItem ← `(Term.doSeqItem| $(mkIdent ``VeilM.assert):ident $t $(Syntax.mkNatLit assertId.toNat))
    appendStateRefreshIfNeeded mod t.raw #[assertItem]
  -- Conditional boolean statements (`if`)
  | `(Term.doSeqItem| if $t:term then $thn:doSeq $[else if $ts:term then $elifs:doSeq]* $[else $e?:doSeq]?) =>
    let mkIfWithRefresh (c : Term) (thn els : Array doSeqItem) : TermElabM doSeqItem := do
      -- If the condition runs a sub-computation (e.g. `if (← act)`), Lean lifts
      -- the call *before* the `if`, so it mutates the state before either branch
      -- runs, leaving the cached state binders stale at branch entry. Refresh
      -- them at the start of each branch body. (When the condition is pure this
      -- is unnecessary, and skipped.)
      let (thn, els) ←
        if stmtRunsComputation c then
          let refresh ← getState mod
          pure (refresh ++ thn, refresh ++ els)
        else
          pure (thn, els)
      `(Term.doSeqItem| if $c:term then $thn* else $els*)
    let thn ← expandDoSeqVeil proc thn
    let els ← match e? with
      | some els => expandDoSeqVeil proc els
      | none => pure #[← `(Term.doSeqItem| pure ())]
    let rest ← ts.zip elifs |>.foldrM (init := els) fun (elifCond, elif) acc => do
      let elifExpanded ← expandDoSeqVeil proc elif
      let res ← mkIfWithRefresh elifCond elifExpanded acc
      pure #[res]
    let ret ← mkIfWithRefresh t thn rest
    pure #[ret]
  -- Conditional existence statements (`if-some`)
  | `(Term.doSeqItem| if $h:term : $t:term then $thn:doSeqItem* else $els:doSeq) =>
    let ids ← collectIfSomeBinderIdents h
    let fs ← `(Term.doSeqItem| let $h:term :| $t:term)
    let thn := fs :: thn.toList |>.toArray
    let existsGuard ← `(term| ∃ $[$ids:ident]*, $t:term)
    -- TODO: should we use a `dite` here?
    expandDoElemVeil proc $ ← `(Term.doSeqItem| if $existsGuard:term then $thn* else $els)
  | `(Term.doSeqItem| if $h:term : $t:term then $thn:doSeq) =>
    expandDoElemVeil proc $ ← `(Term.doSeqItem| if $h:term : $t:term then $thn else pure ())
  -- Non-deterministic assignments
  | `(Term.doSeqItem| $id:ident := *) =>
    let (frApp, ex) ← freshPick mod id
    return ex ++ (← expandDoElemVeil proc $ ← `(Term.doSeqItem|$id:ident := $frApp))
  | `(Term.doSeqItem| $idts:term := *) =>
    let some (id, ts) := idts.isApp? | throwErrorAt stx "wrong syntax for non-deterministic assignment {stx}"
    let (frApp, ex) ← freshPick mod id ts
    return ex ++ (← expandDoElemVeil proc $ ← `(Term.doSeqItem|$idts:term := $frApp))
  -- Deterministic assignments
  | `(Term.doSeqItem| $id:ident := $t:term) => assignState mod id t
  | `(Term.doSeqItem| $id:ident ← $t:term) => expandDoElemVeil proc $ ← `(Term.doSeqItem| $id:ident := ← $t:term)
  | `(Term.doSeqItem| $idts:term := $t:term) =>
    let some (id, ts) := idts.isApp? | return #[stx]
    let stx' <- withRef t `(term| $id _[ $[$ts],* ↦ $t:term ]_)
    let stx <- withRef stx `(Term.doSeqItem| $id:ident := $stx')
    expandDoElemVeil proc stx
  | `(Term.doSeqItem| $idts:term ← $t:term) => expandDoElemVeil proc $ ← `(Term.doSeqItem| $idts:term := ← $t:term)
  -- We handle `bind`s of terms specially, since we want to maintain
  -- the same return value, even though we update the state.
  | `(Term.doSeqItem|$t:term) =>
    let b := mkIdent <| ← mkFreshUserName `_bind
    let bind ← `(Term.doSeqItem| let $b:ident ← $t:term)
    return #[bind] ++ (← getState mod) ++ #[← `(Term.doSeqItem| $(mkIdent ``pure):ident $b:ident)]
  -- For any other do-notation element, we pesimistically refresh the
  -- binders for the state variables, as the state might have changed
  | doE => return #[doE] ++ (← getState mod)
where
freshPick (mod : Module) (id : Ident) (ts : Array Term := #[]) : TermElabM (Term × Array doSeqItem) := do
  let nm := id.getId
  let fr := mkIdent <| ← mkFreshUserName $ (Name.mkSimple s!"pick_{nm}")
  let some sc := mod.signature.find? (·.name = nm)
    | throwErrorAt (← getRef) s!"State component {nm} not found in module {mod.name}"
  -- When we have arguments (`ts`) and can look up the component, build a
  -- narrower pick type that only includes domain dimensions for capitalized
  -- (universally quantified) arguments. Non-capitalized arguments represent
  -- specific values and don't need to be enumerated.
  if ts.isEmpty then
    let ty ← mod.getStateComponentTypeStx nm
    return (fr, #[← `(Term.doSeqItem| let $fr ← pick ($ty:term))])
  let domainTerms := sc.domainTerms
  let componentsSize := domainTerms.size
  let tsUsed := ts.take componentsSize
  let tsResidue := ts.drop componentsSize
  let mut pickDomainTerms : Array Term := #[]
  let mut capitalArgs : Array Term := #[]
  for i in [:tsUsed.size] do
    if isCapital tsUsed[i]!.raw.getId then
      pickDomainTerms := pickDomainTerms.push domainTerms[i]!
      capitalArgs := capitalArgs.push tsUsed[i]!
  -- Domain terms beyond ts.size are not specified, so include them in pick type
  for i in [tsUsed.size:componentsSize] do
    pickDomainTerms := pickDomainTerms.push domainTerms[i]!
  let pickType ← mkArrowStx pickDomainTerms.toList (some sc.codomainTerm)
  let frApp := Syntax.mkApp fr <| capitalArgs ++ tsResidue
  return (frApp, #[← `(Term.doSeqItem| let $fr ← pick ($pickType:term))])

assignState (mod : Module) (id : Ident) (t : Term) : TermElabM (Array doSeqItem) := do
  let name := id.getId
  -- we are assigning to a structure field (probably a child module's state)
  let isStructureAssignment := !name.isAtomic
  let component := mod.signature.find? (·.name = name)
  if isStructureAssignment || component.isNone then
    -- Only check immutability for structure assignments (nested module state).
    -- When component.isNone and !isStructureAssignment, it's a local variable.
    if isStructureAssignment then
      mod.throwIfImmutable name
    let res ← `(Term.doSeqItem| $id:ident := $t:term)
    -- If the RHS ran a sub-computation (e.g. `v := ← proc` / `v ← proc` for a
    -- local var, or `child.f := ← childAction` for nested module state), it may
    -- have mutated *any* field of the state, so the cached state binders for
    -- every field are stale. Reload them. (A pure RHS cannot change the state,
    -- so no refresh is emitted in that case.)
    appendStateRefreshIfNeeded mod t.raw #[res]
  else
    let .some component := component | unreachable!
    mod.throwIfImmutable name
    let bindId := mkIdent <| ← mkFreshUserName $ (mkVeilImplementationDetailName $ Name.mkSimple s!"bind_{id.getId}")
    if mod._useFieldRepTC then
      /-
      The processing below:
      - Analyze the pattern to get the list of pattern arguments `pat`
        and the base value `v`
      - `componentsSize`: the number of arguments that the field expects
      - Let `pat = patUsed ++ patResidue`, where `patUsed` has size at
        most `componentsSize`

      When `patUsed.size < componentsSize`, we need to "pad" the pattern
      with `none`s to make it "full".

      `patResidue` can be non-empty, since the codomain of the field can
      be a function. When `patResidue` is non-empty, we need to "spill"
      them to the base value `v`. See the `v'` below.
      -/
      let (pat, v) := match t with
        | `(term| $f:ident _[ $[$idxs],* ↦ $v ]_) =>
          if f.getId = name then (idxs, v) else (#[], t)
        | _ => (#[], t)
      let _ ← do
        let x ← TupleUpdate.findFirstAppearance pat
        if x.any (·.2.isSome) then
          throwErrorAt stx s!"When using field representation typeclass, you cannot use the same capitalized identifier more than once in the assignment:\n\n{name} {pat}\n\nsince it can lead to unexpected semantics."
      let componentsSize := mod.signature.find? (·.name == name) |>.elim 0 (·.domainTerms.size)
      let (patUsed, patResidue) := (pat.take componentsSize, pat.drop componentsSize)
      let vPadded ← do
        let funBinders : Array (TSyntax `Lean.Parser.Term.funBinder) ←
          patUsed.mapM fun i => if isCapital i.raw.getId then `(Term.funBinder| $(⟨i.raw⟩):ident ) else `(Term.funBinder| _ )
        let v' ←
          if patResidue.isEmpty
          then pure v
          else
            let old := Syntax.mkApp (← `($(mkIdent name):ident)) patUsed
            `($old _[ $[$patResidue],* ↦ $v ]_)
        mkFunSyntax funBinders v'
      let patTerm ← do
        let patOpt ← patUsed.mapM fun i => if isCapital i.raw.getId then `($(mkIdent ``Option.none)) else `(($(mkIdent ``Option.some) $i))
        let components ← `($(fieldLabelToDomain stateName)
          $(← mod.uninterpretedParamIdents):ident*
          $(mkIdent <| structureFieldLabelTypeName stateName ++ name):ident)
        `(veil_dsimp% [$(mkIdent `fieldRepresentationPatSimp)] ($(mkIdent ``FieldUpdatePat.pad) ($components) $(Syntax.mkNatLit patOpt.size) $patOpt*))
      let concreteField := concreteFieldFromName name
      let bind ← `(Term.doSeqItem| let $bindId:ident := ($fieldRepresentation _).$(mkIdent `setSingle) ($patTerm) ($vPadded) $concreteField)
      let modifyGetConcrete ← withRef stx `(Term.doSeqItem| $concreteField:ident ← $(mkIdent ``modifyGet):ident
        (fun $(mkIdent `st):ident => (($bindId, {$(mkIdent `st) with $id:ident := $bindId}))))
      -- this line also appeared above in `getState`
      let getAgain ← `(Term.doSeqItem| $(mkIdent name):ident := @$(mkIdent ``id) ($(← component.typeStx)) (($fieldRepresentation _).$(mkIdent `get) $concreteField))
      -- The block above re-binds only the assigned field `name`. If the RHS ran
      -- a sub-computation (e.g. `w := ← proc`), that call may have written
      -- *other* fields too; their cached binders (including their `f_conc`) are
      -- now stale, and a later indexed update of such a field would write back
      -- from the stale value, discarding the callee's writes. Reload all fields.
      return ← appendStateRefreshIfNeeded mod t.raw #[bind, modifyGetConcrete, getAgain]
    let bind ← `(Term.doSeqItem| let $bindId:ident := $t:term)
    let res ← withRef stx `(Term.doSeqItem| $id:ident ← $(mkIdent ``modifyGet):ident
    (fun $(mkIdent `st):ident => (($bindId, {$(mkIdent `st) with $id:ident := $bindId}))))
    -- Same rationale as the field-representation branch above: refresh all
    -- field binders when the RHS may have mutated state beyond `name`.
    appendStateRefreshIfNeeded mod t.raw #[bind, res]
end

def elabVeilDo (proc : Name) (readerTp : Term) (stateTp : Term) (instx : doSeq) : TermElabM Expr := do
  let mod ← getCurrentModule (errMsg := "You cannot use Veil do-notation outside of a Veil module!")
  let doS ← getDoElems instx
  let (doS, _) ← (expandDoSeqVeil proc (← `(doSeq| $(doS)*))).run
  let mut preludeAssn : Array doSeqItem := #[]
  -- IMPORTANT: we add `let ⟨⟩ := ()` at the beginning of every
  -- do-notation sequence; for reasons we don't understand, if this isn't
  -- present, then type inference fails for actions returning natural
  -- numbers of ints, e.g. `return 5`.
  preludeAssn := preludeAssn.push (← `(Term.doSeqItem| let ⟨⟩ := ()))
  -- TODO: make available child modules' actions using `alias.actionName`
  -- Make available state fields as mutable variables
  preludeAssn := preludeAssn.append (← makeStateAvailable mod)
  -- Make available immutable fields as immutable variables; we
  preludeAssn := preludeAssn.append (← makeTheoryAvailable mod)
  -- Prepend the prelude assignments
  let doS := preludeAssn.append doS
  let outstx ← `(term| ((do $doS*) : $(mkIdent ``VeilM):ident $veilModeVar $readerTp $stateTp _))
  trace[veil.debug] "{outstx}"
  elabTerm outstx none
where
getDoElems (stx : doSeq) : TermElabM (Array doSeqItem) := do
  let doS <- match stx with
  | `(doSeq| $doE*) => pure doE
  | `(doSeq| { $doE* }) => pure doE
  | _ => throwErrorAt stx "unexpected syntax of Veil `do`-notation sequence {stx}"

elab (name := VeilDo) "veil_do" name:ident "in" readerTp:term "," stateTp:term "in" instx:doSeq : term => do
  elabVeilDo name.getId readerTp stateTp instx

attribute [fieldRepresentationPatSimp] FieldUpdatePat.pad IteratedArrow.curry IteratedProd.default HAppend.hAppend IteratedProd.append Eq.mp
attribute [fieldRepresentationSetSimpPre] FieldRepresentation.setSingle LawfulFieldRepresentationSet.set_append List.singleton_append
attribute [fieldRepresentationSetSimpPost] CanonicalField.set FieldUpdateDescr.fieldUpdate FieldUpdatePat.match IteratedProd.patCmp IteratedArrow.curry IteratedArrow.uncurry
attribute [fieldRepresentationSetSimpPost] List.foldr Option.elim Bool.and_true Bool.and_eq_true decide_eq_true_eq ite_eq_left_iff Bool.false_eq_true false_and and_self
attribute [fieldRepresentationSetSimpPost ↓] reduceIte ite_true ite_false and_true true_and

end Veil
