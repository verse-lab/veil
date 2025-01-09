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
  | fresh   (τ : Type u) : Lang τ
  /-- Deterministic changes to the state, although mostly used for assignments. All
      capital variables will be quantified. -/
  | det     {ρ' : Type u} (act : σ -> σ × ρ') : Lang ρ'
  /-- Non-deterministic changes to the state. -/
  | nondet  {ρ' : Type u} (act :  σ -> σ × ρ' -> Prop) : Lang ρ'
  /-- If-then-else. `open Classical` to allow propositions in the condition. -/
  | ite     {ρ : Type u} (cnd : σ -> Bool) (thn : Lang ρ) (els : Lang ρ) : Lang ρ
  /-- If-then-else. `open Classical` to allow propositions in the condition. -/
  | iteSome {ρ : Type u} {ρ' : Type} (cnd : ρ' -> σ -> Bool) (thn : ρ' -> Lang ρ) (els : Lang ρ) : Lang ρ
  | ret     {ρ : Type u} (ret : ρ) : Lang ρ

/-- One-state formula -/
@[inline] abbrev sprop := σ -> Prop
/-- One-state formula that also talks about the return value. -/
@[inline] abbrev rprop (ρ : Type u) := ρ → sprop σ
/-- Two-state formula -/
@[inline] abbrev actprop := σ -> σ -> Prop


def Wlp (σ : Type) (ρ : Type) := rprop σ ρ -> sprop σ

section

variable {σ ρ : Type}

def Wlp.pure {σ ρ} (r : ρ) : Wlp σ ρ := fun post s => post r s
def Wlp.bind {σ ρ} (wp : Wlp σ ρ) (wp_cont : ρ -> Wlp σ ρ') : Wlp σ ρ' :=
  fun post s => wp (fun r s' => wp_cont r post s') s

instance : Monad (Wlp σ) where
  pure := Wlp.pure
  bind := Wlp.bind

def Wlp.require (rq : sprop σ) : Wlp σ PUnit := fun post s => rq s ∧ post () s
def Wlp.det (act : σ -> σ × ρ) : Wlp σ ρ := fun post s => let (s', ret) := act s ; post ret s'
def Wlp.nondet (act : σ -> σ × ρ -> Prop) : Wlp σ ρ := fun post s => ∃ s' ret, act s (s', ret) ∧ post ret s'
def Wlp.ite (cnd : σ -> Bool) (thn : Wlp σ ρ) (els : Wlp σ ρ) : Wlp σ ρ :=
  fun post s => if cnd s then thn post s else els post s
def Wlp.iteSome (cnd : ρ -> σ -> Bool) (thn : ρ -> Wlp σ ρ) (els : Wlp σ ρ) : Wlp σ ρ :=
  fun post s => (∃ r, cnd r s ∧ thn r post s) ∨ (∀ r, ¬ cnd r s) ∧ els post s
def Wlp.fresh (τ : Type) : Wlp σ τ := fun post s => ∃ t, post t s
def Wlp.skip : Wlp σ PUnit := Wlp.pure ()

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

/-- This is used in `require` were we define a predicate over a state.
    Instead of writing `fun st => Pred` this command will pattern match over
    `st` making all its fields accessible for `Pred` -/
macro "funcases" t:term : term => `(term| by intros st; unhygienic cases st; exact $t)
macro "funcases" id:ident t:term : term => `(term| by unhygienic cases $id:ident; exact $t)

/-- `require s` checks if `s` is true on the current state -/
syntax "require" term      : doElem
/-- `call s` calls action `s` on a current state -/
syntax "call" term : doElem

/-- Non-deterministic value. -/
syntax (name := nondetVal) "*" : term
/-- syntax for assigment, e.g. `pending n s := true` -/
syntax atomic(Term.structInstLVal (term:max)* ":==") (term <|> nondetVal)    : doElem

elab "throw_if_immutable" id:Term.structInstLVal t:term : term => do
  throwIfImmutable id; elabTerm t none

macro_rules
  | `(doElem| require $t)           => `(doElem| Wlp.require (funcases $t))
  | `(doElem| call $t)              => `(doElem| @Wlp.nondet _ _ (funcases $t))
  -- expansion of the intermediate syntax for assigment
  -- for instance `pending := pending[n, s ↦ true]` will get
  -- expanded to `Lang.det (fun st => { st with pending := st.pending[n, s ↦ true] })`
  | `(doElem| $id:structInstLVal :== $t:term) =>
    `(doElem|
            /- TODO: uncomment -/
            -- throw_if_immutable $id
            @Wlp.det _ _ (fun st => ({ st with $id := (funcases st $t)}, ())))
  -- expansion of the actual syntax for assignment
  -- for instance `pending n s := true` will get
  -- expanded to `pending := pending[n, s ↦ true]`
  | `(doElem| $id:structInstLVal $ts: term * :== $t:term) => do
    let stx <- withRef id `($(⟨id.raw.getHead?.get!⟩)[ $[$ts],* ↦ $t:term ])
    `(doElem| $id:structInstLVal :== $stx)


elab_rules : term
  -- expansion of the intermediate syntax for assigment
  -- for instance `pending := pending[n, s ↦ true]` will get
  -- expanded to `Lang.det (fun st => { st with pending := st.pending[n, s ↦ true] })`
  | `(doElem| $id:structInstLVal :== $t:term) => do
    throwIfImmutable id
    elabTerm (<- `(doElem|@Wlp.det _ _ (fun (st : [State]) =>
      ({ st with $id := (funcases st $t)}, ())))) none
  -- expansion of the actual syntax for assignment
  -- for instance `pending n s := true` will get
  -- expanded to `pending := pending[n, s ↦ true]`


structure state where
  r : Int
  s : Bool
  m : Bool -> Bool


open Wlp in
def k : Wlp state Nat := do
  let mut y := 0
  require r = y
  if true then
    y := (<- fresh Nat) + 1
  else y := y + 2
  m B :== true
  return y

example {P : _ -> Prop} : P (k (fun r s => r = r' ∧ s = s') s) := by
  simp [k, Wlp.fresh, bind, Wlp.bind, Wlp.require, pure, Wlp.pure, Wlp.det ]







end

#exit
-- abbrev triple (t : ρ) (H : sprop σ) (P : rprop σ ρ) := ∀ s, H s → P t s

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
  -- the meaning of `ite` depends on which branch is taken
  | Lang.ite cnd thn els  => fun s => if cnd s then wlp post thn s else wlp post els s
  | Lang.iteSome cnd thn els  =>
    fun s =>
    (∃ r, cnd r s ∧ wlp post (thn r) s) ∨ (∀ r, ¬ cnd r s) ∧ wlp post els s
  -- `seq` is a composition of programs, so we need to compute the wlp of
  -- the first program, given the wlp of the second
  | Lang.ret ret    => post ret
  | Lang.bind l1 l2 => wlp (fun ret => wlp post (l2 ret)) l1
  | Lang.fresh τ => fun s => ∃ t, post t s

declare_syntax_cat left_arrow
syntax "<-" : left_arrow
syntax "←" : left_arrow

/-- Sequense of [lang] commands -/
declare_syntax_cat langSeq
/-- Let binding or a single [lang] statement -/
declare_syntax_cat langElem
/-- Single [lang] statement -/
declare_syntax_cat lang

syntax lang : langElem
/- [lang] let binging -/
syntax "let" ident left_arrow lang : langElem

/-- Sequense of [lang] commands -/
syntax sepByIndentSemicolon(langElem) : langSeq

/-- [skip] statement which does nothing -/
syntax "skip"              : lang
/-- Non-deterministic value. -/
syntax (name := nondetVal) "*" : lang
/-- `require s` checks if `s` is true on the current state -/
syntax "require" term      : lang
/-- `fresh [Type]?` creates a fresh variable of type `Type`, or of an implicit type if `Type` is ommited -/
syntax "fresh" term ? : lang
/-- `return t` returns `t`  -/
syntax "return" term : lang
syntax term : lang

declare_syntax_cat some_if
syntax ident "where" : some_if
syntax (priority := high) "if " (some_if)? term " then" langSeq colGe "else\n" langSeq : lang
syntax (priority := low) "if " (some_if)? term " then" langSeq : lang

/-- intermediate syntax for assigment, e.g. `pending := pending[n, s ↦ true]` -/
syntax Term.structInstLVal ":=" term    : lang
/-- syntax for assigment, e.g. `pending n s := true` -/
syntax Term.structInstLVal (term:max)+ ":=" (term <|> nondetVal)    : lang
syntax term (":" term)? left_arrow lang "in" langSeq : lang

declare_syntax_cat unchanged
syntax "with unchanged" "[" ident,* "]" : unchanged
syntax "ensure" rcasesPat  "," term unchanged ? : lang
syntax "ensure" term unchanged ? : lang
syntax "[unchanged|" ident* "]" : term

/-- Syntax to trigger the expantion into a code -/
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
macro "funcases" id:ident t:term : term => `(term| by unhygienic cases $id:ident; exact $t)

/-====== Macro expansion for [lang] ======-/

/-- In some cases, during the macro expansion, we need to annotate certain
    arguments with the state type. To get the state type, we need an access to an
    eviorment with we don't have at the macro-expansion stage. To overcome this, we
    introduce the following notation, witch gets resolved to a current state type
    during the elaboration stage  -/
syntax "[State]" : term
elab_rules : term
  | `([State]) => do
    let stateTp := (← localSpecCtx.get).spec.stateStx
    elabTerm (<- `(term| $stateTp)) none

/- Fisrt, we handle sequensial composiotin and let-bindings -/

macro_rules
  | `([langSeq| ]) => `([lang|skip])
  | `([lang|skip]) => do
    `(term| @Lang.det _ _ (fun (st : [State]) => (st, ())))
  | `([langSeq|$l:lang]) => `([lang|$l])
  | `([langSeq| $ls:langElem*]) => do
    let l₁ := ls.getElems[0]!
    let ls := ls.getElems[1:]
    let mut (id, l) := (default, default)
    match l₁ with
    | `(langElem| let $i:ident $_:left_arrow $lb:lang) =>
      id <- `(Term.funBinder| $i); l := lb
    | `(langElem| $lb:lang) =>
      id <- `(Term.funBinder| _); l := lb
    | _ => Macro.throwError "unexpected syntax"
    `(@Lang.bind _ _ _ [lang|$l] (fun $id => [langSeq|$[$ls]*]))


/- Simple single statements: `require`, `return`, `fresh` and `call` -/

macro_rules
  | `([lang|return $t:term]) => `(@Lang.ret _ _ (funcases $(mkIdent `st):ident $t))
  | `([lang|$t:term])   => `(@Lang.nondet _ _ (funcases $(mkIdent `st):ident $t))
  | `([lang|require $t:term]) => do
    -- universally close term [t] under free variables starting with a capital letter
    let t' <- closeCapitals t
    withRef t $ `(@Lang.require _ (funcases ($t' : Prop) : _ -> Prop))
    -- infer the type of a fresh variable, if it is not given
  | `([lang|fresh]) => `([lang|fresh _])
  | `([lang|fresh $t:term]) => `(@Lang.fresh _ $t)

/- If-then-else -/

macro_rules
  | `([lang|if $some_if ? $cnd:term then $thn:langSeq]) => `([lang|if $some_if ? $cnd then $thn else skip])
  | `([lang|if $cnd:term then $thn:langSeq else $els:langSeq]) => do
    let cnd' <- closeCapitals cnd
    -- condition might depend on the state as well
    let cnd <- withRef cnd `(funcases ($cnd' : Bool))
    `(@Lang.ite _ _ ($cnd: term) [langSeq|$thn] [langSeq|$els])
  | `([lang|if $x:ident where $cnd:term then $thn:langSeq else $els:langSeq]) => do
    let cnd' <- closeCapitals cnd
    -- condition might depend on the state as well
    let cnd <- withRef cnd `(funcases ($cnd' : Bool))
    `(@Lang.iteSome _ _ _ (fun $x:ident => $cnd:term) (fun $x => [langSeq|$thn]) [langSeq|$els])

/- Assignments -/

elab_rules : term
  -- expansion of the intermediate syntax for assigment
  -- for instance `pending := pending[n, s ↦ true]` will get
  -- expanded to `Lang.det (fun st => { st with pending := st.pending[n, s ↦ true] })`
  | `([lang| $id:structInstLVal := $t:term]) => do
    throwIfImmutable id
    elabTerm (<- `(@Lang.det _ _ (fun (st : [State]) =>
      ({ st with $id := (funcases st $t)}, ())))) none
  -- non-deterministic assignment
  | `([lang| $id:structInstLVal $ts: term * := *]) => do
    throwIfImmutable id
    elabTerm (<- `(@Lang.fresh _ _ _ (fun v => @Lang.nondet _ _ _ (fun (st : [State]) =>
      ({ st with $id := (funcases st ($(⟨id.raw.getHead?.get!⟩)[ $[$ts],* ↦ v ]))}, ()))))) none
  -- expansion of the actual syntax for assignment
  -- for instance `pending n s := true` will get
  -- expanded to `pending := pending[n, s ↦ true]`
  | `([lang| $id:structInstLVal $ts: term * := $t:term]) => do
    throwIfImmutable id
    let stx <- withRef id `($(⟨id.raw.getHead?.get!⟩)[ $[$ts],* ↦ $t:term ])
    elabTerm (<- `([lang| $id:structInstLVal := $stx])) none

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

/- Expanding unchanged statement -/
macro_rules
  | `([unchanged| $id:ident]) =>
    let id_old := id.getId.toString ++ "_old" |>.toName
    `($id = $(mkIdent id_old))
  | `([unchanged| $id $ids*]) => `([unchanged| $id] ∧ [unchanged| $ids*])
  | `([unchanged|]) => `(True)

/- One can omit the result variable from [ensures] -/
macro_rules
  | `([lang|ensure $t:term $un:unchanged ?] ) => `([lang|ensure (_ : Unit), $t:term $un:unchanged ?])

elab_rules : term
  /- if the list of unchanged state fileds is omitted, we can restore it by
     checking witch of them are mentioned in the [ensures] body. By default
     we assume that if the state filed is not mentioned, then it is left
     unchanged  -/
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

end Lang
