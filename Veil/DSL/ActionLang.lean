import Lean
import Lean.Parser
import Veil.State
import Veil.DSL.Util
import Veil.DSL.Base
import Veil.DSL.StateExtensions
import Veil.DSL.ActionTheory


open Lean Elab Command Term Meta Lean.Parser

/-!
  # Action Language

  This file defines the syntax and semantics for the imperative language
  we use to define initializers and actions.
-/
section Veil

attribute [actSimp] modify modifyGet MonadStateOf.modifyGet get
  getThe MonadStateOf.get MonadStateOf.set instMonadStateOfMonadStateOf
  instMonadStateOfWlp

macro "unfold_wlp" : conv =>
  `(conv| unfold
    -- unfold actions defined via Veil do-notation
    Wlp.pure
    Wlp.bind
    Wlp.assume
    Wlp.fresh
    -- unfold state monad actions
    set
    modify
    modifyGet
    get
    instMonadStateOfMonadStateOf
    getThe
    MonadStateOf.modifyGet
    MonadStateOf.get
    MonadStateOf.set
    instMonadStateOfWlp
    -- unfold specifications
    Wlp.spec
    -- unfold actions defined via two-state relations
    Function.toWlp
    -- unfold actions definded via lifting
    monadLift
    restrictTo
    extendWith)

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

-- declare_syntax_cat doSeq
-- declare_syntax_cat doSeqItem

-- syntax (priority := low) doElem : doSeqItem

syntax (priority := high) atomic(term ":=" "*") : doElem

-- syntax "if" term "then" doSeq colGe "else" doSeq : doSeqItem
-- syntax "if" term "then" doSeq : doSeqItem
-- syntax "if" ident ":" term "then" doSeq colGe "else" doSeq : doSeqItem
-- syntax "if" ident ":" term "then" doSeq : doSeqItem


declare_syntax_cat unchanged_decl
declare_syntax_cat spec
syntax "requires" term colGe "ensures" rcasesPat  "," term : spec
syntax (priority := high) "requires" term colGe "ensures" term : spec
syntax "with" "unchanged" "[" ident,* "]" : unchanged_decl
syntax spec (colGe unchanged_decl)? : term
syntax "[unchanged|" ident* "]" : term

abbrev doSeq := TSyntax ``Term.doSeq
abbrev doSeqItem := TSyntax ``Term.doSeqItem

mutual
partial def expandDoSeqVeil (stx : doSeq) : TermElabM (TSyntax ``Term.doSeq) :=
  match stx with
  | `(doSeq| $doS:doSeqItem*) => do
    let doS <- doS.mapM expandDoElemVeil
    `(doSeq| $[$doS]*)
  | _ => throwErrorAt stx s!"unexpected syntax of Veil `do`-notation sequence {stx}"

partial def expandDoElemVeil (stx : doSeqItem) : TermElabM doSeqItem := do
  trace[dsl.debug] "[expand doElem] {stx}"
  match stx with
  | `(Term.doSeqItem| $stx ;) => expandDoElemVeil $ <- `(Term.doSeqItem| $stx:doElem)
  -- Expand `if` statements
  | `(Term.doSeqItem| if $h:ident : $t:term then $thn:doSeqItem* else $els:doSeq) =>
    let fs <- `(Term.doSeqItem| let $h:ident <- fresh)
    let t' <- `(Term.doSeqItem| require $t)
    let thn := fs :: t' :: thn.toList |>.toArray
    expandDoElemVeil $ <-
      `(Term.doSeqItem| if (∃ $h:ident, $t) then $thn* else $els)
  | `(Term.doSeqItem| if $t:term then $thn:doSeq) =>
    expandDoElemVeil $ <- `(Term.doSeqItem| if $t then $thn:doSeq else pure ())
  -- Expand `if-some` statements
  | `(Term.doSeqItem| if $h:ident : $t:term then $thn) =>
    expandDoElemVeil $ <- `(Term.doSeqItem| if $h:ident : $t:term then $thn else pure ())
  | `(Term.doSeqItem| if $t:term then $thn:doSeq else $els:doSeq) =>
    let thn <- expandDoSeqVeil thn
    let els <- expandDoSeqVeil els
    `(Term.doSeqItem| if $t then $thn else $els)
  -- Expand non-determenistic assigments statements
  | `(Term.doSeqItem| $id:ident := *) =>
    let .some typeStx ← (<- localSpecCtx.get) |>.spec.getStateComponentTypeStx (id.getId)
      | throwErrorAt stx "trying to assign to undeclared state component {id}"
    expandDoElemVeil $ <- `(Term.doSeqItem|if True then let y <- fresh ($typeStx); $id:ident := y)
  | `(Term.doSeqItem| $idts:term := *) =>
    let some (id, ts) := idts.isApp? | throwErrorAt stx "wrong syntax for non-deterministic assignment {stx}"
    let .some typeStx ← (<- localSpecCtx.get) |>.spec.getStateComponentTypeStx (id.getId)
      | throwErrorAt stx "trying to assign to undeclared state component {id}"
    expandDoElemVeil $ <- `(Term.doSeqItem|if True then let y <- fresh ($typeStx); $idts:term := y $ts*)
  -- Expand determenistic assigments statements
  | `(Term.doSeqItem| $id:ident := $t:term) =>
    trace[dsl.debug] "[expand assignmet with args] {stx}"
    let id' <- `(Term.structInstLVal| $id:ident)
    let fields <- getFields
    if id.getId ∈ fields then
      throwIfImmutable id'
      `(Term.doSeqItem| if True then
        modify (fun st => {st with $id:ident := $t })
        $id:ident := (<- get).$id)
    else
      `(Term.doSeqItem| $id:ident := $t:term)
  | `(Term.doSeqItem| $idts:term := $t:term) =>
    trace[dsl.debug] "[expand assignmet with args] {stx}"
    let some (id, ts) := idts.isApp? | return stx
    let stx' <- `(term| $id[ $[$ts],* ↦ $t:term ])
    let stx <- withRef stx `(Term.doSeqItem| $id:ident := $stx')
    expandDoElemVeil stx
  | doE =>
    trace[dsl.debug] "[expand just a doElem] {stx}"
    return doE
end


elab "do'" stx:doSeq : term => do
  let mut stateAssns : Array doSeqItem := #[]
  let doS := match stx with
  | `(doSeq| $doE*) => doE
  | `(doSeq| { $doE* }) => doE
  | _ => unreachable!
  let fs := (<- getFields).map Lean.mkIdent
  for f in fs do
    stateAssns := stateAssns.push <| ← `(Term.doSeqItem| let mut $f:ident := (<- get).$f)
  let doS := stateAssns.append doS
  let stx' <- expandDoSeqVeil (<- `(doSeq| $doS*))
  trace[dsl.debug] "{stx}\n→\n{stx'}"
  elabTerm (<- `(term| ((do $stx') : Wlp [State] _))) none

macro_rules
  | `(require $t) => `(Wlp.assume $t)
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
  | `(requires $pre ensures $post:term $un:unchanged_decl ?) => `(requires $pre ensures (_ : Unit), $post:term $un:unchanged_decl ?)

def getPrePost (spec : doSeq) [Monad m] [MonadError m] [MonadQuotation m] :
  m (Term × TSyntax `rcasesPat × Term) := do
  match spec with
  | `(doSeq| requires $pre ensures $id, $post:term $_:unchanged_decl ?) => pure (pre, id, post)
  | `(doSeq| requires $pre ensures $post:term $_:unchanged_decl ?) => pure (pre, <- `(rcasesPat|(_ : Unit)), post)
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
