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
    Wlp.assert
    Wlp.require
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
    extendWith
    instMonadLiftTOfMonadLift
    MonadLift.monadLift
    instMonadLiftWlpOfIsStateExtension
    instMonadLiftT)

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

def getFields [Monad m] [MonadEnv m] : m (Array Name) := do
  let spec := (← localSpecCtx.get).spec
  pure $ spec.signature.map (·.name)

def getSubActions : TermElabM (Array (Ident × Term)) := do
  /- FIXME: principled way to fix this would be to iterate
    over all already defined actions in `(← localSpecCtx.get).spec.actions`
    but at this point it is somehow empty (it should contain actions from
    dependent modules). -/
  let mut names := #[]
  for (depName, ts, al) in (← localSpecCtx.get).spec.dependencies do
    let spec := (← globalSpecCtx.get)[depName]!
    for act in spec.actions do
      let actArgs := List.replicate spec.typeClassNum (<- `(_)) |>.toArray
      let actName := mkIdent <| al ++ act.name
      let actTerm <- `(@$actName $ts* $actArgs*)
      let currMod := (← localSpecCtx.get).stateBaseName.get!
      if (<- getEnv).find? (currMod ++ actName.getId) |>.isSome then
        names := names.push (actName, actTerm)
  pure names


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

/-- `require s` admits fact `s`   -/
syntax "require" term      : term
/-- `assert s` checks if `s` is true on the current state -/
syntax "assert" term      : term
/-- `assume s` checks if `s` is true on the current state -/
syntax "assume" term      : term
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
syntax "[unchanged|" str "|" ident* "]" : term

abbrev doSeq := TSyntax ``Term.doSeq
abbrev doSeqItem := TSyntax ``Term.doSeqItem

structure Vars where
  name : Ident
  type : Term

abbrev VeilM := StateT (Array Vars) TermElabM

mutual
partial def expandDoSeqVeil (stx : doSeq) : VeilM (Array doSeqItem) :=
  match stx with
  | `(doSeq| $doS:doSeqItem*) => doS.mapM expandDoElemVeil
  | _ => throwErrorAt stx s!"unexpected syntax of Veil `do`-notation sequence {stx}"



partial def expandDoElemVeil (stx : doSeqItem) : VeilM doSeqItem := do
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
    `(Term.doSeqItem| if $t then $thn* else $els*)
  -- Expand non-determenistic assigments statements
  | `(Term.doSeqItem| $id:ident := *) =>
    let typeStx ← (<- localSpecCtx.get) |>.spec.getStateComponentTypeStx (id.getId)
    let fr := mkIdent <| <- mkFreshUserName `fresh
    modify (·.push ⟨fr, typeStx.getD (<- `(_))⟩)
    expandDoElemVeil $ <- `(Term.doSeqItem|$id:ident := $fr)
  | `(Term.doSeqItem| $idts:term := *) =>
    let some (id, ts) := idts.isApp? | throwErrorAt stx "wrong syntax for non-deterministic assignment {stx}"
    let typeStx ← (<- localSpecCtx.get) |>.spec.getStateComponentTypeStx (id.getId)
    let fr := mkIdent <| <- mkFreshUserName `fresh
    modify (·.push ⟨fr, typeStx.getD (<- `(_))⟩)
    expandDoElemVeil $ <- `(Term.doSeqItem|$idts:term := $fr:ident $ts*)
  -- Expand determenistic assigments statements
  | `(Term.doSeqItem| $id:ident := $t:term) =>
    trace[dsl.debug] "[expand assignmet with args] {stx}"
    let name := id.getId
    if name.isAtomic then
      let id' <- `(Term.structInstLVal| $id:ident)
      let fields <- getFields
      if id.getId ∈ fields then
        throwIfImmutable id'
        -- NOTE: It is very important that we return a single `doSeqItem`;
        -- otherwise syntax highlighting gets broken very badly
        withRef stx `(Term.doSeqItem| $id:ident ← modifyGet
            (fun st => (($t, {st with $id:ident := $t}))))
      else
        `(Term.doSeqItem| $id:ident := $t:term)
    else
      let base := mkIdent name.getPrefix
      let suff := mkIdent $ name.updatePrefix default
      expandDoElemVeil $ <- withRef stx `(Term.doSeqItem| $base:ident := { $base with $suff:ident := $t })
  | `(Term.doSeqItem| $idts:term := $t:term) =>
    trace[dsl.debug] "[expand assignmet with args] {stx}"
    let some (id, ts) := idts.isApp? | return stx
    let stx' <- withRef t `(term| $id[ $[$ts],* ↦ $t:term ])
    let stx <- withRef stx `(Term.doSeqItem| $id:ident := $stx')
    expandDoElemVeil stx
  | doE =>
    trace[dsl.debug] "[expand just a doElem] {stx}"
    return doE
end

elab (name := VeilDo) "do'" mode:term "in" stx:doSeq : term => do
  /- Array containing all auxilary let-bingings to be inserted in the
    beginning of the `do`-block. It consists of
    - `let mut feild := (<- get). field` for each field of the protocol state. We do this
      to be able to access and modify the state fields without the need to use
      `get` and `modify` functions
    - [HACK] `let submodule.act := submodule.act` for each action `act` inherited from
      submodules. As for each submodule, the previous step defines a local variable
      `submodule`, `submodule.act` will be treated as an access to `submodule`'s filed `act`,
      rather than an action `act` operation on `submodule`
    - `let freshName <- fresh` for each non-determenistic assigment. We hoist all fresh
      variables to make all the quantifiers top level -/
  let mut preludeAssn : Array doSeqItem := #[]
  let doS <- match stx with
  | `(doSeq| $doE*) => pure doE
  | `(doSeq| { $doE* }) => pure doE
  | _ => throwErrorAt stx "unexpected syntax of Veil `do`-notation sequence {stx}"
  let (doS, vars) <- (expandDoSeqVeil (<- `(doSeq| $doS*))).run #[]

  let as := (<- getSubActions)
  for a in as do
    preludeAssn := preludeAssn.push <| ← `(Term.doSeqItem| let $(a.1):ident := $(a.snd))
  let fs := (<- getFields).map Lean.mkIdent
  for f in fs do
    preludeAssn := preludeAssn.push <| ← `(Term.doSeqItem| let mut $f:ident := (<- get).$f)
  for v in vars do
    preludeAssn := preludeAssn.push <| ← `(Term.doSeqItem| let $v.name:ident <- fresh $v.type)
  let doS := preludeAssn.append doS
  trace[dsl.debug] "{stx}\n→\n{doS}"
  elabTerm (<- `(term| ((do $doS*) : Wlp $mode [State] _))) none

macro_rules
  | `(require $t) => `(Wlp.require $t)
  | `(assert  $t) => `(Wlp.assert $t)
  | `(assume  $t) => `(Wlp.assume $t)
  | `(fresh   $t) => `(Wlp.fresh  $t)
  | `(fresh)      => `(Wlp.fresh  _)

/- Ensures statement -/

open Tactic in
/-- ```with_rename_old t``` runs tactic `t` and if it introduces any names with `_1` suffix,
    changes this suffix to `_old` -/
elab "with_rename" s:str t:tactic : tactic => withMainContext do
  let hyps <- getLCtx
  withMainContext $ evalTactic t
  withMainContext do
    let hypNews <- getLCtx
    for hyp in hypNews.decls.toArray.reverse do
      if hyp.isSome then
        let hyp := hyp.get!
        unless hyps.findFromUserName? hyp.userName |> Option.isSome do
          let nms := (hyp.userName.toString.splitOn "_")
          let new_name := String.intercalate "_" nms.dropLast ++ s.getString |>.toName
          evalTactic $ <- `(tactic| (revert $(mkIdent hyp.userName):ident; intros $(mkIdent new_name):ident))

/- Expanding `unchanged` statement -/
macro_rules
  | `([unchanged|$s:str| $id:ident]) =>
    let id_old := id.getId.toString ++ s.getString |>.toName
    `($id = $(mkIdent id_old))
  | `([unchanged|$s| $id $ids*]) => `([unchanged|$s| $id] ∧ [unchanged|$s| $ids*])
  | `([unchanged|$_|]) => `(True)

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
    elabTerm (<- `(term| @Wlp.spec [State] _ _ (funcases $pre) (
      by rintro st $r st';
         unhygienic cases st';
         with_rename "_old" unhygienic cases st;
         exact $post ∧ [unchanged|"_old"|$ids*]))) none

attribute [actSimp] Bind.bind Pure.pure

/- We need those to simplify `Wlp` goals  -/
attribute [ifSimp] ite_self ite_true_same ite_false_same if_true_left
  if_true_right if_false_left if_false_right


end Veil
