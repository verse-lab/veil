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

section Lang
/-! Our language is parametric over the state type. -/
variable (σ : Type)

/-- Imperative language for defining actions. -/
inductive Lang.{u} : Type u → Type (u + 1) where
  /-- Pre-condition. All capital variables will be quantified. -/
  | require (rq : σ -> Prop) : Lang PUnit
  | bind    {ρ ρ' : Type u} (act : Lang ρ') (act' : ρ' -> Lang ρ) : Lang ρ
  -- τ is a first order type, so it can be quantified in FOL
  | fresh   {τ : Type u} {ρ : Type u} (act : τ -> Lang ρ) : Lang ρ
  /-- Deterministic changes to the state, although mostly used for assignments. All
      capital variables will be quantified. -/
  | det     {ρ' : Type u} (act : σ -> σ × ρ') : Lang ρ'
  /-- Non-deterministic changes to the state. -/
  | nondet  {ρ' : Type u} (act :  σ -> σ × ρ' -> Prop) : Lang ρ'
  /-- If-then-else. `open Classical` to allow propositions in the condition. -/
  | ite     {ρ : Type u} (cnd : σ -> Bool) (thn : Lang ρ) (els : Lang ρ) : Lang ρ
  /-- If-then-else. `open Classical` to allow propositions in the condition. -/
  | iteSome {ρ : Type u} {ρ' : Type} (cnd : ρ' -> σ -> Bool) (thn : ρ' -> Lang ρ) (els : Lang ρ) : Lang ρ

  /-- Sequence -/
  | seq     {ρ ρ' : Type u} (l1 : Lang ρ') (l2 : Lang ρ) : Lang ρ
  | ret     {ρ : Type u} (ret : ρ) : Lang ρ

/-- One-state formula -/
@[inline] abbrev sprop := σ -> Prop
/-- One-state formula that also talks about the return value. -/
@[inline] abbrev rprop (ρ : Type u) := ρ → sprop σ
/-- Two-state formula -/
@[inline] abbrev actprop := σ -> σ -> Prop

-- abbrev triple (t : ρ) (H : sprop σ) (P : rprop σ ρ) := ∀ s, H s → P t s

open Classical in
/-- Weakest liberal precondition transformer. It takes a post-condition and
    a program and returns the weakest pre-condition that guarantees the
    post-condition IF the program terminates.
    This defines the axiomatic semantics of our language. -/
@[actSimp] def wlp (post : rprop σ ρ) : Lang σ ρ -> sprop σ
  -- `require` enhances the pre-condition, restricting the possible states
  -- it has the same effect as `assume` in Hoare logic
  | Lang.require rq       => fun s => rq s ∧ post () s
  -- | Lang.assume  as       => fun s => as s → post () s
  -- a deterministic `act` transforms the state
  | Lang.det act          => fun s => let (s', ret) := act s ; post ret s'
  -- A non-deterministic action satisfies the post-condition if there is
  -- _some_ possible post-state that satisfies the post-condition.
  -- This corresponds to the semantics in Ivy and matches the intuition that
  -- a call to an action is morally equivalent to inlining that action.
  | Lang.nondet act       => fun s => ∃ s' ret, act s (s', ret) ∧ post ret s'
--| Lang.ensure p         => fun s => ∃ s' ret, p s s' ∧ post ret s'
  -- the meaning of `ite` depends on which branch is taken
  | Lang.ite cnd thn els  => fun s => if cnd s then wlp post thn s else wlp post els s
  | Lang.iteSome cnd thn els  => fun s =>
    -- The "natural" meaning would be something like this:
    -- `(∃ r, cnd r s ∧ wlp post (thn r) s) ∨ ((∀ r, ¬ cnd r s) ∧ wlp post els s)`
    -- but this requires us to distribute ∧ over ∨ in the goals (in a way that
    -- requires us to write a custom `simproc` and blows up goal size), so we
    -- instead use the following form:
      if ∃ r, cnd r s then ∃ r, cnd r s ∧ wlp post (thn r) s else wlp post els s
  -- `seq` is a composition of programs, so we need to compute the wlp of
  -- the first program, given the wlp of the second
  | Lang.seq l1 l2        =>
    wlp (fun _ => wlp post l2) l1
  | Lang.ret ret    => post ret
  | Lang.bind l1 l2 =>
    wlp (fun ret => wlp post (l2 ret)) l1
  | Lang.fresh act => fun s => ∃ t, wlp post (act t) s

declare_syntax_cat left_arrow
syntax "<-" : left_arrow
syntax "←" : left_arrow

declare_syntax_cat langSeq
declare_syntax_cat lang

syntax sepByIndentSemicolon(lang) : langSeq

-- syntax lang ";" colGe lang : lang
-- syntax lang : lang
syntax "skip"              : lang
/-- Non-deterministic value. -/
syntax (name := nondetVal) "*" : lang
syntax "require" term      : lang
syntax "do" term           : lang

declare_syntax_cat some_if
syntax ident "where" : some_if
syntax (priority := high) "if" (some_if)? term:max "{" langSeq "}" "else\n" "{" langSeq "}" : lang
syntax (priority := low) "if" (some_if)? term:max "{" langSeq "}" : lang
/-- intermediate syntax for assigment, e.g. `pending := pending[n, s ↦ true]` -/
syntax Term.structInstLVal ":=" term    : lang
/-- syntax for assigment, e.g. `pending n s := true` -/
syntax Term.structInstLVal (term:max)+ ":=" (term <|> nondetVal)    : lang
syntax term (":" term)? left_arrow lang "in" langSeq : lang
syntax "fresh" ident ":" term "in" langSeq : lang
syntax "return" term : lang
syntax "call" term : lang

declare_syntax_cat unchanged
syntax "with unchanged" "[" ident,* "]" : unchanged

syntax "ensure" rcasesPat  "," term unchanged ? : lang
syntax "ensure" term unchanged ? : lang
syntax "[unchanged|" ident* "]" : term

/-- Syntax to trigger the expantion into a code which may
    depend on the prestate -/
syntax "[langSeq|" langSeq "]" : term
syntax "[lang|" lang "]" : term


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

/-- Alternate version of `Term.adaptExpander`, which gives an extra
`TSyntax term` argument to `exp`. We use this to provide type
annotations to the state type in the expansion of the imperative DSL.
(Without this, when type inference fails, the user sees a cryptic
"expected structure" error.) For action return values, we rely on Lean's
type inference. -/
def adaptExpander' (exp : Syntax → TSyntax `term → TermElabM Syntax) : Syntax → TSyntax `term → TermElabM Expr := fun stx expectedType => do
  let stx' ← exp stx expectedType
  withMacroExpansion stx stx' <| elabTerm stx' .none

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

/-- This is used in `require` were we define a predicate over a state.
    Instead of writing `fun st => Pred` this command will pattern match over
    `st` making all its fields accessible for `Pred` -/
macro "funcases" t:term : term => `(term| by intros st; unhygienic cases st; exact $t)

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


/-- This is used wherener we want to define a predicate over a state
    which should not depend on the state (for instance in `after_init`). -/
macro "funclear" t:term : term => `(term| by intros st; clear st; exact $t)

macro_rules
  | `([unchanged| $id:ident]) =>
    let id_old := id.getId.toString ++ "_old" |>.toName
    `($id = $(mkIdent id_old))
  | `([unchanged| $id $ids*]) => `([unchanged| $id] ∧ [unchanged| $ids*])
  | `([unchanged|]) => `(True)

/-- This is used when we want to define a predicate over a state
    which should not depend on the pre-state. -/
macro "funclear" t:term : term => `(term| by intros st; clear st; exact $t)

def getFreshIdents (is : Array Term) [Monad m] [MonadQuotation m] : m (Array Ident) := do
  let mut x : Array $ Lean.TSyntax `ident := #[]
  for i in is do
    if isCapital i then
      x := x.push ⟨i.raw⟩
    else
      x := x.push (<- mkFreshIdent (Lean.mkIdent `x))
  return x


elab_rules : term
  | `([lang| $id:structInstLVal $ts: term * := *]) => do
    throwIfImmutable id
    let `(Lean.Parser.Term.structInstLVal| $id:ident) := id
      | throwErrorAt id "{id} is not a valid LHS for an assignment"
    let id_old := mkIdent $ id.getId.toString ++ "_old" |>.toName
    let ts' <- getFreshIdents ts
    let tsTup  <- `(term| [tupl| $ts:term *])
    let ts'Tup <- `(term| [tupl| $ts':ident *] )
    let stx <- `([lang| ensure ∀ $ts'*, $tsTup:term = $ts'Tup:term ∨ $id:ident $ts'* = $id_old $ts'*] )
    -- trace[dsl] stx
    elabTerm stx none
  | `([lang| $id:structInstLVal $ts: term * := $t:term ]) => do
    let stx <- withRef id `($(⟨id.raw.getHead?.get!⟩)[ $[$ts],* ↦ $t:term ])
    elabTerm (<- `([lang| $id:structInstLVal := $stx])) none


elab_rules : term
  | `([lang|skip]) => do
    let stateTp := (← localSpecCtx.get).spec.stateStx
    elabTerm (<- `(term| @Lang.det _ _ (fun (st : $stateTp) => (st, ())))) none
  | `([langSeq| ]) => do
    let stateTp := (← localSpecCtx.get).spec.stateStx
    elabTerm (<- `(term| @Lang.det _ _ (fun (st : $stateTp) => (st, ())))) none
  | `([langSeq| $l1:lang]) => do elabTerm (<- `([lang|$l1])) none
  | `([langSeq| $l1:lang*]) => do
    elabTerm (<- `(@Lang.seq _ _ _ [lang|$(l1.getElems[0]!)] [langSeq| $[$(l1.getElems[1:])]*])) none
  | `([lang|ensure $r, $t:term]) => do
    let fields : Array Name := (<- localSpecCtx.get).spec.signature.map (·.name)
    let mut unchangedFields := #[]
    for f in fields do
      unless t.raw.find? (·.getId == f) |>.isSome do
        unchangedFields := unchangedFields.push $ mkIdent f
    elabTerm (<- `(term| [lang|ensure $r, $t:term with unchanged[$[$unchangedFields],*]])) none
  | `([lang|ensure $r, $t:term with unchanged[$ids,*]]) => do
    withRef t $
    elabTerm (<- `(term| @Lang.nondet _ _ (
      by rintro st ⟨st', $r⟩;
         unhygienic cases st';
         with_rename_old unhygienic cases st;
         exact $t ∧ [unchanged|$ids*]))) none
  -- expansion of the intermediate syntax for assignment
  -- for instance `pending := pending[n, s ↦ true]` will get
  -- expanded to `Lang.det (fun st => { st with pending := st.pending[n, s ↦ true] })`
  | `([lang| $id:structInstLVal := $t:term]) => do
    throwIfImmutable id
    let stateTp := (← localSpecCtx.get).spec.stateStx
    elabTerm (<- `(@Lang.det _ _ (fun (st : $stateTp) =>
      ({ st with $id := (by unhygienic cases st; exact $t)}, ())))) none
  -- expansion of the actual syntax for assignment
  -- for instance `pending n s := true` will get
  -- expanded to `pending := pending[n, s ↦ true]`

macro_rules
  | `([lang|require $t:term]) => do
    let t' <- closeCapitals t
    withRef t $
      -- require a proposition on the state
     `(@Lang.require _ (funcases ($t' : Prop) : _ -> Prop))
  --
  | `([lang|if $some_if ? $cnd:term { $thn:langSeq }]) => `([lang|if $some_if ? $cnd { $thn } else { skip }])
  | `([lang|if $cnd:term { $thn:langSeq } else { $els:langSeq }]) => do
    let cnd' <- closeCapitals cnd
    -- condition might depend on the state as well
    let cnd <- withRef cnd `(funcases ($cnd' : Bool))
    `(@Lang.ite _ _ ($cnd: term) [langSeq|$thn] [langSeq|$els])
  | `([lang|if $x:ident where $cnd:term { $thn:langSeq } else { $els:langSeq }]) => do
    let cnd' <- closeCapitals cnd
    -- condition might depend on the state as well
    let cnd <- withRef cnd `(funcases ($cnd' : Bool))
    `(@Lang.iteSome _ _ _ (fun $x:ident => $cnd:term) (fun $x => [langSeq|$thn]) [langSeq|$els])
  --
  | `([lang|ensure $t:term $un:unchanged ?] ) =>
    `([lang|ensure (_ : Unit), $t:term $un:unchanged ?])
  | `([lang| do $t:term ]) => `(@Lang.det _ _ $t)
    -- expansion of the actual syntax for assigment
    -- for instance `pending n s := true` will get
    -- expanded to `pending := pending[n, s ↦ true]`
  -- NOTE: the following two cases describe the same construct
  -- there's probably a way to unify them
  | `([lang| $id:term $_:left_arrow $l1:lang in $l2:langSeq]) => do
      `(@Lang.bind _ _ _ [lang|$l1] (fun $id => [langSeq|$l2]))
  | `([lang| $id:term : $t:term $_:left_arrow $l1:lang in $l2:langSeq]) => do
      `(@Lang.bind _ _ _ [lang|$l1] (fun ($id : $t) => [langSeq|$l2]))
  | `([lang|fresh $id:ident : $t in $l2:langSeq]) =>
      `(@Lang.fresh _ _ _ (fun $id : $t => [langSeq|$l2]))
  | `([lang|return $t:term]) => `(@Lang.ret _ _ (by unhygienic cases $(mkIdent `st):ident; exact $t))
  | `([lang|call $t:term]) => `(@Lang.nondet _ _ (by unhygienic cases $(mkIdent `st):ident; exact $t))

end Lang
