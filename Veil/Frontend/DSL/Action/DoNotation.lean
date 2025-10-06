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
    if mod._useStateRepTC then
      let concreteField := concreteFieldFromName f.name
      -- annotating the type here is necessary to avoid unification issues
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
    if mod._useStateRepTC then
      -- slightly repeating code, but anyway
      let concreteField := concreteFieldFromName f.name
      let b1 ← `(Term.doSeqItem| $concreteField:ident := $(mkIdent stVar).$(mkIdent f.name))
      let b2 ← `(Term.doSeqItem| $(mkIdent f.name):ident := ($fieldRepresentation _).$(mkIdent `get) $concreteField)
      return #[b1, b2]
    else
      return #[← `(Term.doSeqItem| $(mkIdent f.name):ident := $(mkIdent stVar).$(mkIdent f.name))]
  return #[getState] ++ bindFields

macro_rules
  | `(assume  $t) => `($(mkIdent ``VeilM.assume) $t)
  | `(pick   $t)  => `($(mkIdent ``MonadNonDet.pick) $t)
  | `(pick)       => `($(mkIdent ``MonadNonDet.pick) _)
  | `(doElem| let $x:term :| $p) => `(doElem| let $x:term ← $(mkIdent ``VeilM.pickSuchThat):ident _ (fun $x => $p))

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
  -- We don't want to introduce state updates after pure statements, so
  -- we pass these through unchanged
  -- FIXME: we could have `pure (← state_modifying_action)`, so this isn't
  -- sound. In general, you could even have multiple binds in a single
  -- `term`, so this entire approach is broken and really unfixable until
  -- Lean ships an extensible do-notation. It's best-effort for now.
  | `(Term.doSeqItem| pure $t:term)
  | `(Term.doSeqItem| return $t:term)
  -- NOTE: all the expressions in `require`, `assert`, and `assume`,
  -- `pick-such-that` and `if` need to be `Decidable` for execution.
  | `(Term.doSeqItem| assume $t)
  | `(Term.doSeqItem| let $_ :| $t)
  | `(Term.doSeqItem| let $_ : $_ ← pick $_) | `(Term.doSeqItem| let $_ : $_ ← pick)
  | `(Term.doSeqItem| let $_ ← pick $_) | `(Term.doSeqItem| let $_ ← pick)
  => return #[stx]
  -- We elaborate `require` and `assert` here, since we need to record
  -- which procedure they belong to
  | `(Term.doSeqItem| require $t) =>
    let assertId ← mkNewAssertion proc stx
    return #[← `(Term.doSeqItem| $(mkIdent ``VeilM.require):ident $t $(Syntax.mkNatLit assertId.toNat))]
  | `(Term.doSeqItem| assert $t) =>
    let assertId ← mkNewAssertion proc stx
    return #[← `(Term.doSeqItem| $(mkIdent ``VeilM.assert):ident $t $(Syntax.mkNatLit assertId.toNat))]
  -- Conditional boolean statements (`if`)
  | `(Term.doSeqItem| if $t:term then $thn:doSeq else $els:doSeq) =>
    let thn ← expandDoSeqVeil proc thn
    let els ← expandDoSeqVeil proc els
    let ret ← `(Term.doSeqItem| if $t then $thn* else $els*)
    return #[ret]
  | `(Term.doSeqItem| if $t:term then $thn:doSeq) =>
    expandDoElemVeil proc $ ← `(Term.doSeqItem| if $t then $thn:doSeq else pure ())
  -- Conditional existence statements (`if-some`)
  | `(Term.doSeqItem| if $h:ident : $t:term then $thn:doSeqItem* else $els:doSeq) =>
    let fs ← `(Term.doSeqItem| let $h:ident :| $t:term)
    let thn := fs :: thn.toList |>.toArray
    -- TODO: should we use a `dite` here?
    expandDoElemVeil proc $ ← `(Term.doSeqItem| if (∃ $h:ident, $t) then $thn* else $els)
  | `(Term.doSeqItem| if $h:ident : $t:term then $thn) =>
    expandDoElemVeil proc $ ← `(Term.doSeqItem| if $h:ident : $t:term then $thn else pure ())
  -- Non-deterministic assignments
  | `(Term.doSeqItem| $id:ident := *) =>
    let (fr, ex) ← freshPick mod id
    return ex ++ (← expandDoElemVeil proc $ ← `(Term.doSeqItem|$id:ident := $fr))
  | `(Term.doSeqItem| $idts:term := *) =>
    let some (id, ts) := idts.isApp? | throwErrorAt stx "wrong syntax for non-deterministic assignment {stx}"
    let (fr, ex) ← freshPick mod id
    return ex ++ (← expandDoElemVeil proc $ ← `(Term.doSeqItem|$idts:term := $fr:ident $ts*))
  -- Deterministic assignments
  | `(Term.doSeqItem| $id:ident := $t:term) => assignState mod id t
  | `(Term.doSeqItem| $id:ident ← $t:term) => expandDoElemVeil proc $ ← `(Term.doSeqItem| $id:ident := ← $t:term)
  | `(Term.doSeqItem| $idts:term := $t:term) =>
    let some (id, ts) := idts.isApp? | return #[stx]
    let stx' <- withRef t `(term| $id[ $[$ts],* ↦ $t:term ])
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
freshPick (mod : Module) (id : Ident) : TermElabM (Ident × Array doSeqItem) := do
  let ty ← mod.getStateComponentTypeStx id.getId
  let fr := mkIdent <| ← mkFreshUserName $ (Name.mkSimple s!"pick_{id.getId}")
  return (fr, #[← `(Term.doSeqItem| let $fr ← pick ($ty:term))])

assignState (mod : Module) (id : Ident) (t : Term) : TermElabM (Array doSeqItem) := do
  let name := id.getId
  -- we are assigning to a structure field (probably a child module's state)
  let isStructureAssignment := !name.isAtomic
  let component := mod.signature.find? (·.name = name)
  if isStructureAssignment || component.isNone then
    -- TODO: throwIfImmutable
    let res ← `(Term.doSeqItem| $id:ident := $t:term)
    return #[res]
  else
    let .some component := component | unreachable!
    -- TODO: throwIfImmutable
    let bindId := mkIdent <| ← mkFreshUserName $ (mkVeilImplementationDetailName $ Name.mkSimple s!"bind_{id.getId}")
    if mod._useStateRepTC then
      let (pat, v) := match t with
        | `(term| $f:ident [ $[$idxs],* ↦ $v ]) =>
          if f.getId = name then (idxs, v) else (#[], t)
        | _ => (#[], t)
      -- NOTE: here slightly deviates from how `pat` is handled in `TupleUpdate`;
      -- namely, turn every Capital identifier into `none`
      -- NOTE: the actual pattern size might be smaller than `pat.size`, since
      -- the base can be a function; we shrink the size according to how
      -- `toComponents` is generated
      let componentsSize := match component.type with
        | .simple _ => 0
        | .complex b _ => b.size
      let actualPatSize := min pat.size componentsSize
      let patOpt ← pat.take actualPatSize |>.mapM fun i => if isCapital i.raw.getId then `($(mkIdent ``Option.none)) else `(($(mkIdent ``Option.some) $i))
      let funBinders : Array (TSyntax `Lean.Parser.Term.funBinder) ←
        pat.mapM fun i => if isCapital i.raw.getId then `(Term.funBinder| $(⟨i.raw⟩):ident ) else `(Term.funBinder| _ )
      let vPadded ← if funBinders.isEmpty then pure v else `(fun $[$funBinders]* => ($v))
      let components ← `($(fieldToComponents stateName)
        $(← mod.sortIdents):ident*
        $(mkIdent <| structureFieldLabelTypeName stateName ++ name):ident)
      let patTerm ← `(dsimp% [$(mkIdent `fieldRepresentationSimp)] ($(mkIdent ``FieldUpdatePat.pad) ($components) $(Syntax.mkNatLit patOpt.size) $patOpt*))
      let concreteField := concreteFieldFromName name
      let bind ← `(Term.doSeqItem| let $bindId:ident := ($fieldRepresentation _).$(mkIdent `setSingle) ($patTerm) ($vPadded) $concreteField)
      let modifyGetConcrete ← withRef stx `(Term.doSeqItem| $concreteField:ident ← $(mkIdent ``modifyGet):ident
        (fun $(mkIdent `st):ident => (($bindId, {$(mkIdent `st) with $id:ident := $bindId}))))
      -- this line also appeared above
      let getAgain ← `(Term.doSeqItem| $(mkIdent name):ident := ($fieldRepresentation _).$(mkIdent `get) $concreteField)
      return #[bind, modifyGetConcrete, getAgain]
    let bind ← `(Term.doSeqItem| let $bindId:ident := $t:term)
    let res ← withRef stx `(Term.doSeqItem| $id:ident ← $(mkIdent ``modifyGet):ident
    (fun $(mkIdent `st):ident => (($bindId, {$(mkIdent `st) with $id:ident := $bindId}))))
    return #[bind, res]
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

attribute [fieldRepresentationSimp] FieldUpdatePat.pad IteratedArrow.curry IteratedProd.default HAppend.hAppend IteratedProd.append Eq.mp

end Veil
