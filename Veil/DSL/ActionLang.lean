import Lean
import Lean.Parser
import Veil.State
import Veil.DSL.Util
import Veil.DSL.Base
import Veil.DSL.StateExtensions


open Lean Elab Command Term Meta Lean.Parser

/-!
  # Action Language

  This file defines the syntax and semantics for the imperative language
  we use to define initializers and actions.
-/
section Veil

section Types
/-! Our language is parametric over the state type. -/
variable (σ : Type)

/-- One-state formula -/
@[inline] abbrev sprop := σ -> Prop
/-- One-state formula that also talks about the return value. -/
@[inline] abbrev rprop (ρ : Type u) := ρ → sprop σ
/-- Two-state formula -/
@[inline] abbrev actprop := σ -> σ -> Prop

/-  Wlp (σ : Type) (ρ : Type) := rprop σ ρ -> sprop σ -/
abbrev Wlp (σ : Type) (ρ : Type) := σ -> rprop σ ρ -> Prop

/-- Function which transforms any two-state formula into `Wlp` -/
@[actSimp]
def Function.toWlp (r : σ -> σ -> Prop) : Wlp σ Unit :=
  fun s post => ∀ s', r s s' -> post () s'

end Types
section

variable {σ ρ : Type}

@[actSimp]
def Wlp.pure (r : ρ) : Wlp σ ρ := fun s post => post r s
@[actSimp]
def Wlp.bind (wp : Wlp σ ρ) (wp_cont : ρ -> Wlp σ ρ') : Wlp σ ρ' :=
  fun s post => wp s (fun r s' => wp_cont r s' post)

instance : Monad (Wlp σ) where
  pure := Wlp.pure
  bind := Wlp.bind

@[actSimp]
def Wlp.require (rq : Prop) : Wlp σ PUnit := fun s post => rq ∧ post () s
@[actSimp]
def Wlp.det (act : σ -> ρ × σ) : Wlp σ ρ := fun s post => let (ret, s') := act s ; post ret s'
@[actSimp]
def Wlp.fresh (τ : Type) : Wlp σ τ := fun s post => ∀ t, post t s
@[actSimp]
def Wlp.withState {σ} (r : σ -> ρ) : Wlp σ ρ :=
  fun s post => post (r s) s
@[actSimp]
def Wlp.spec (pre : sprop σ) (post : σ -> rprop σ ρ) : Wlp σ ρ :=
  fun s post' => ∀ s' r, pre s ∧ (post' r s' -> post s r s')

instance : MonadStateOf σ (Wlp σ) where
  get := fun s post => post s s
  set s' := fun _ post => post () s'
  modifyGet := Wlp.det

class IsStateExtension (σ : semiOutParam Type) (σ' : Type) where
  extendWith : σ -> σ' -> σ'
  restrictTo : σ' -> σ

export IsStateExtension (extendWith restrictTo)

instance [IsStateExtension σ σ'] : MonadLift (Wlp σ) (Wlp σ') where
  monadLift := fun m s post => m (restrictTo s) (fun r s' => post r (extendWith s' s))

macro "unfold_wlp" : conv =>
  `(conv| unfold
    -- unfold actions defined via Veil do-notation
    Wlp.det
    Wlp.pure
    Wlp.bind
    Wlp.require
    Wlp.fresh
    Wlp.withState
    -- unfold specifications
    Wlp.spec
    -- unfold actions defined via two-state relations
    Function.toWlp
    -- unfold actions definded via lifting
    monadLift
    restrictTo
    extendWith)

end

partial def getCapitals (s : Syntax) :=
  let rec loop  (acc : Array $ TSyntax `ident ) (s : Syntax) : Array $ TSyntax `ident :=
    if s.isIdent then
      if isCapital s then
        acc.push ⟨s⟩
      else
        acc
    else
      s.getArgs.foldl (init := acc) loop
  (loop #[] s).toList.eraseDups.toArray

/-- Close the given expression under all capital letters.
    this is called for `require`, `safety` and `invariant` -/
def closeCapitals (s : Term) : MacroM Term :=
  let caps := getCapitals s
  `(forall $[$caps]*, $s)

/-- Throw an error if the field (which we're trying to assign to) was
declared immutable. FIXME: make sure elaboration aborts? -/
def throwIfImmutable (lhs : TSyntax `Lean.Parser.Term.structInstLVal) : TermElabM Unit := do
  let spec := (← localSpecCtx.get).spec
  let nm ← getIdFrom lhs
  let .some comp := spec.getStateComponent nm
    | throwErrorAt lhs "trying to assign to undeclared state component {nm}"
  if comp.isImmutable then
    throwErrorAt lhs "{comp.kind} {comp.name} was declared immutable, but trying to assign to it!"
  where getIdFrom (lhs : TSyntax `Lean.Parser.Term.structInstLVal) : TermElabM Name :=
    match lhs with
    | `(Lean.Parser.Term.structInstLVal|$id:ident) => pure id.getId
    | _ => throwErrorAt lhs "expected an identifier in the LHS of an assignment, got {repr lhs}"

def getFields : TermElabM (Array Name) := do
  let spec := (← localSpecCtx.get).spec
  pure $ spec.signature.map (·.name)

/-- In some cases, during the macro expansion, we need to annotate certain
    arguments with the state type. To get the state type, we need an access to an
    eviorment with we don't have at the macro-expansion stage. To overcome this, we
    introduce the following notation, witch gets resolved to a current state type
    during the elaboration stage  -/
elab "[State]" : term => do
    let stateTp := (← localSpecCtx.get).spec.stateStx
    elabTerm (<- `(term| $stateTp)) none

/-- This is used in `require` were we define a predicate over a state.
    Instead of writing `fun st => Pred` this command will pattern match over
    `st` making all its fields accessible for `Pred` -/
macro "funcases" t:term : term => `(term| by intros st; unhygienic cases st; exact $t)
macro "funcases" id:ident t:term : term => `(term| by unhygienic cases $id:ident; exact $t)

/-- `require s` checks if `s` is true on the current state -/
syntax "require" term      : term
/-- `fresh [ty]?` allocate a fresh variable of a given type `ty` -/
syntax "fresh" (lineEq term) ? : term

declare_syntax_cat doSeqVeil
declare_syntax_cat doElemVeil

syntax (priority := low) doElem : doElemVeil

syntax (priority := high) term ":=" "*" : doElemVeil

syntax "if" term "then" doSeqVeil colGe "else" doSeqVeil : doElemVeil
syntax "if" term "then" doSeqVeil : doElemVeil
syntax "if" ident ":" term "then" doSeqVeil colGe "else" doSeqVeil : doElemVeil
syntax "if" ident ":" term "then" doSeqVeil : doElemVeil


declare_syntax_cat unchanged
declare_syntax_cat spec
syntax "requires" term colGe "ensures" rcasesPat  "," term : spec
syntax (priority := high) "requires" term colGe "ensures" term : spec
syntax "with unchanged" "[" ident,* "]" : unchanged
syntax spec (colGe unchanged)? : term
syntax "[unchanged|" ident* "]" : term

syntax sepByIndentSemicolon(doElemVeil) : doSeqVeil

def hasRHS? (stx : TSyntax `doElem) : Option (Term × (Term -> TermElabM (TSyntax `doElem))) := do
  match stx with
  | `(doElem| $t:term) => (t, fun t => (`(doElem| $t:term) : TermElabM _))
  | `(doElem| $id:ident := $t:term) =>
    (t, fun t => (`(doElem| $id:ident := $t) : TermElabM _))
  | `(doElem| let $id:ident := $t:term) =>
    (t, fun t => (`(doElem| let $id:ident := $t) : TermElabM _))
  | `(doElem| let mut $id:ident := $t:term) =>
    (t, fun t => (`(doElem| let mut $id:ident := $t) : TermElabM _))
  | `(doElem| $id:ident <- $t:term) =>
    (t, fun t => (`(doElem| $id:ident <- $t:term) : TermElabM _))
  | `(doElem| let $id:ident <- $t:term) =>
    (t, fun t => (`(doElem| let $id:ident <- $t:term) : TermElabM _))
  | `(doElem| let mut $id:ident <- $t:term) =>
    (t, fun t => (`(doElem| let mut $id:ident <- $t:term) : TermElabM _))
  | _ => none

def withState? (doE : TSyntax `doElem) : TermElabM $ TSyntax `doElem := do
  let some (t, cont) := hasRHS? doE | return doE
  let fields : Array Name <- getFields
  if t.raw.find? (·.getId ∈ fields) |>.isSome then
    let t <- withRef t `(<- Wlp.withState (funcases $t))
    cont t
  else return doE

mutual
partial def expandDoSeqVeil (stx : TSyntax `doSeqVeil) : TermElabM (TSyntax ``Term.doSeq) :=
  match stx with
  | `(doSeqVeil| $doS:doElemVeil*) => do
    let doS <- doS.getElems.mapM expandDoElemVeil
    `(doSeq| $[$doS:doElem]*)
  | _ => throwErrorAt stx s!"unexpected syntax of Veil `do`-notation sequence {stx}"

partial def expandDoElemVeil (stx : TSyntax `doElemVeil) : TermElabM (TSyntax `doElem) := do
  trace[dsl.debug] "[expandDoElemVeil] {stx}"
  match stx with
  | `(doElemVeil| if $h:ident : $t:term then $thn) =>
    expandDoElemVeil $ <- `(doElemVeil| if $h:ident : $t:term then $thn else pure ())
  | `(doElemVeil| if $h:ident : $t:term then $thn:doElemVeil* else $els:doSeqVeil) =>
    let t' <- `(doElemVeil| require $t)
    let thn := t' :: thn.getElems.toList |>.toArray
    expandDoElemVeil $ <-
      `(doElemVeil|
        if (∃ $h:ident, $t) then
          let $h:ident <- fresh; $[$thn]*
        else $els)
  | `(doElemVeil| if $t:term then $thn:doSeqVeil) =>
    expandDoElemVeil $ <- `(doElemVeil| if $t then $thn:doSeqVeil else pure ())
  | `(doElemVeil| if $t:term then $thn:doSeqVeil else $els:doSeqVeil) =>
    let thn <- expandDoSeqVeil thn
    let els <- expandDoSeqVeil els
    `(doElem| if <- Wlp.withState (funcases $t) then $thn else $els)
  | `(doElemVeil| $id:ident := *) =>
      trace[dsl.debug] "[doElemVeil] id assignment {stx}"
      let .some typeStx ← (<- localSpecCtx.get) |>.spec.getStateComponentTypeStx (id.getId)
        | throwErrorAt stx "trying to assign to undeclared state component {id}"
      expandDoElemVeil $ <- `(doElemVeil|if True then let y <- fresh ($typeStx); $id:ident := y)
  | `(doElemVeil| $idts:term := *) =>
      trace[dsl.debug] "[doElemVeil] term assignment {stx}"
      let some (id, ts) := idts.isApp? | throwErrorAt stx "wrong syntax for non-deterministic assignment {stx}"
      let .some typeStx ← (<- localSpecCtx.get) |>.spec.getStateComponentTypeStx (id.getId)
        | throwErrorAt stx "trying to assign to undeclared state component {id}"
      expandDoElemVeil $ <- `(doElemVeil|if True then let y <- fresh ($typeStx); $idts:term := y $ts*)
  | `(doElemVeil| $doE:doElem) =>
    match doE with
    | `(doElem| $id:ident := $t:term) =>
        trace[dsl.debug] "[doElem] id assignment {doE}"
        let id' <- `(Term.structInstLVal| $id:ident)
        let fields <- getFields
        if id.getId ∈ fields then
          throwIfImmutable id'
          `(doElem| @Wlp.det _ _ (fun (st : [State]) => ((), { st with $id' := (funcases st $t)})))
        else
          withState? $ <- `(doElem| $id:ident := $t:term)
    | `(doElem| $idts:term := $t:term) =>
      trace[dsl.debug] "[doElem] term assignment {doE}"
      let some (id, ts) := idts.isApp? | `(doElem| $doE:doElem)
      let stx <- withRef idts `(term| $id[ $[$ts],* ↦ $t:term ])
      let stx <- `(doElemVeil| $id:ident := $stx)
      expandDoElemVeil stx
    | _ => withState? doE
  | _ => throwErrorAt stx s!"unexpected syntax of Veil `do`-notation {stx}"
end

elab "do'" stx:doSeqVeil : term => do
  let stx' <- expandDoSeqVeil stx
  trace[dsl.debug] "{stx}\n→\n{stx'}"
  elabTerm (<- `(term| ((do $stx') : Wlp [State] _))) none

macro_rules
  | `(require $t) => `(Wlp.require $t)
  | `(fresh   $t) => `(Wlp.fresh $t)
  | `(fresh)      => `(Wlp.fresh _)

/- Ensures statement -/

open Tactic in
/-- ```with_rename_old t``` runs tactic `t` and if it introduces any names with `_1` suffix,
    changes this suffix to `_old` -/
elab "with_rename_old" t:tactic : tactic => withMainContext do
  let hyps <- getLCtx
  withMainContext $ evalTactic t
  withMainContext do
    let hypNews <- getLCtx
    for hyp in hypNews.decls.toArray.reverse do
      if hyp.isSome then
        let hyp := hyp.get!
        unless hyps.findFromUserName? hyp.userName |> Option.isSome do
          let nms := (hyp.userName.toString.splitOn "_")
          let new_name := String.intercalate "_" nms.dropLast ++ "_old" |>.toName
          evalTactic $ <- `(tactic| (revert $(mkIdent hyp.userName):ident; intros $(mkIdent new_name):ident))

/- Expanding `unchanged` statement -/
macro_rules
  | `([unchanged| $id:ident]) =>
    let id_old := id.getId.toString ++ "_old" |>.toName
    `($id = $(mkIdent id_old))
  | `([unchanged| $id $ids*]) => `([unchanged| $id] ∧ [unchanged| $ids*])
  | `([unchanged|]) => `(True)

/- One can omit the result variable from [ensures] -/
macro_rules
  | `(requires $pre ensures $post:term $un:unchanged ?) => `(requires $pre ensures (_ : Unit), $post:term $un:unchanged ?)

def getPrePost (spec : TSyntax `doSeqVeil) [Monad m] [MonadError m] [MonadQuotation m] :
  m (Term × TSyntax `rcasesPat × Term) := do
  match spec with
  | `(doSeqVeil| requires $pre ensures $id, $post:term $_:unchanged ?) => pure (pre, id, post)
  | `(doSeqVeil| requires $pre ensures $post:term $_:unchanged ?) => pure (pre, <- `(rcasesPat|(_ : Unit)), post)
  | _ => throwErrorAt spec "Invalid sepcification: expected `requires ... ensures ...`"

elab_rules : term
  /- if the list of unchanged state fileds is omitted, we can restore it by
     checking witch of them are mentioned in the [ensures] body. By default
     we assume that if the state filed is not mentioned, then it is left
     unchanged  -/
  | `(requires $pre ensures $r, $post:term) => do
    let fields : Array Name <- getFields
    let mut unchangedFields := #[]
    for f in fields do
      unless post.raw.find? (·.getId == f) |>.isSome do
        unchangedFields := unchangedFields.push $ mkIdent f
    elabTerm (<- `(requires $pre ensures $r, $post:term with unchanged[$[$unchangedFields],*])) none
  | `(requires $pre ensures $r, $post:term with unchanged[$[$ids],*]) => do
    -- withRef t $
    elabTerm (<- `(term| @Wlp.spec [State] _ (funcases $pre) (
      by rintro st $r st';
         unhygienic cases st';
         with_rename_old unhygienic cases st;
         exact $post ∧ [unchanged|$ids*]))) none

attribute [actSimp] Bind.bind Pure.pure

end Veil
