import Lean
import Lean.Parser
import Veil.State
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
  | Lang.seq l1 l2        =>
    wlp (fun _ => wlp post l2) l1
  | Lang.ret ret    => post ret
  | Lang.bind l1 l2 =>
    wlp (fun ret => wlp post (l2 ret)) l1
  | Lang.fresh act => fun s => ∃ t, wlp post (act t) s

declare_syntax_cat left_arrow
syntax "<-" : left_arrow
syntax "←" : left_arrow


declare_syntax_cat lang
syntax lang ";" colGe lang : lang
syntax "skip"              : lang
/-- Non-deterministic value. -/
syntax (name := nondetVal) "*" : lang
syntax "require" term      : lang
syntax "do" term           : lang

declare_syntax_cat some_if
syntax ident "where" : some_if

syntax (priority := high) "if" (some_if)? term:max "{" lang "}" "else\n" "{" lang "}" : lang
syntax (priority := low) "if" (some_if)? term:max "{" lang "}" : lang


/-- intermediate syntax for assigment, e.g. `pending := pending[n, s ↦ true]` -/
syntax Term.structInstLVal ":=" term    : lang
/-- syntax for assigment, e.g. `pending n s := true` -/
syntax Term.structInstLVal (term:max)+ ":=" (term <|> nondetVal)    : lang
syntax term (":" term)? left_arrow lang "in" lang : lang
syntax "fresh" ident ":" term "in" lang : lang
syntax "return" term : lang
syntax "call" term : lang
/-- Syntax to trigger expansion of a Veil imperative fragment into a
two-state transition with the state type `term`. -/
syntax "[Veil|" term "|" lang "]" : term
/-- Syntax to trigger the expantion into a code which doesn't
    depend on the prestate -/
syntax "[lang1|" lang "]" : term

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
def closeCapitals (s : Term) : CoreM Term :=
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
    `st` making all its fileds accessible for `Pred` -/
macro "funcases" t:term : term => `(term| by intros st; unhygienic cases st; exact $t)

/-- This is used wherener we want to define a predicate over a state
    which should not depend on the state (for instance in `after_init`). -/
macro "funclear" t:term : term => `(term| by intros st; clear st; exact $t)

def elabLang : Syntax → TSyntax `term → TermElabM Expr := adaptExpander' fun stx stateTp => do
  match stx with
  | `(lang|skip) => `(@Lang.det _ _ (fun (st : $stateTp) => (st, ())))
  | `(lang|$l1:lang; $l2:lang) => `(@Lang.seq _ _ _ [Veil|$stateTp|$l1] [Veil|$stateTp|$l2])
  | `(lang|require $t:term) => do
    let t' <- closeCapitals t
    withRef t $
      -- require a proposition on the state
     `(@Lang.require _ (funcases ($t' : Prop) : _ -> Prop))
  | `(lang|if $some_if ? $cnd:term { $thn:lang }) => `([Veil|$stateTp|if $some_if ? $cnd { $thn } else { skip }])
  | `(lang|if $cnd:term { $thn:lang } else { $els:lang }) => do
    let cnd' <- closeCapitals cnd
    -- condition might depend on the state as well
    let cnd <- withRef cnd `(funcases ($cnd' : Bool))
    `(@Lang.ite _ _ ($cnd: term) [Veil|$stateTp|$thn] [Veil|$stateTp|$els])
  | `(lang|if $x:ident where $cnd:term { $thn:lang } else { $els:lang }) => do
    let cnd' <- closeCapitals cnd
    -- condition might depend on the state as well
    let cnd <- withRef cnd `(funcases ($cnd' : Bool))
    `(@Lang.iteSome _ _ _ (fun $x:ident => $cnd:term) (fun $x => [Veil|$stateTp|$thn]) [Veil|$stateTp|$els])
  | `(lang| do $t:term ) => `(@Lang.det _ _ $t)
  -- non-deterministic assignment
  | `(lang| $id:structInstLVal $ts: term * := * ) => do
    throwIfImmutable id
    `(@Lang.fresh _ _ _ (fun v => @Lang.nondet _ _ _ (fun (st : $stateTp) =>
      ({ st with $id := (by unhygienic cases st; exact ($(⟨id.raw.getHead?.get!⟩)[ $[$ts],* ↦ v ]))}, ()))))
    -- expansion of the intermediate syntax for assignment
    -- for instance `pending := pending[n, s ↦ true]` will get
    -- expanded to `Lang.det (fun st => { st with pending := st.pending[n, s ↦ true] })`
  | `(lang| $id:structInstLVal := $t:term ) => do
    throwIfImmutable id
    `(@Lang.det _ _ (fun (st : $stateTp) =>
      ({ st with $id := (by unhygienic cases st; exact $t)}, ())))
  -- expansion of the actual syntax for assignment
  -- for instance `pending n s := true` will get
  -- expanded to `pending := pending[n, s ↦ true]`
  | `(lang| $id:structInstLVal $ts: term * := $t:term ) => do
    throwIfImmutable id
    let stx <- withRef id `($(⟨id.raw.getHead?.get!⟩)[ $[$ts],* ↦ $t:term ])
    `([Veil|$stateTp| $id:structInstLVal := $stx])
  -- NOTE: the following two cases describe the same construct
  -- there's probably a way to unify them
  | `(lang| $id:term $_:left_arrow $l1:lang in $l2:lang) => do
      `(@Lang.bind _ _ _ [Veil|$stateTp|$l1] (fun $id => [Veil|$stateTp|$l2]))
  | `(lang| $id:term : $t:term $_:left_arrow $l1:lang in $l2:lang) => do
      `(@Lang.bind _ _ _ [Veil|$stateTp|$l1] (fun ($id : $t) => [Veil|$stateTp|$l2]))
  | `(lang|fresh $id:ident : $t in $l2:lang) =>
      `(@Lang.fresh _ _ _ (fun $id : $t => [Veil|$stateTp|$l2]))
  | `(lang|return $t:term) => `(@Lang.ret _ _ (by unhygienic cases $(mkIdent `st):ident; exact $t))
  | `(lang|call $t:term) => `(@Lang.nondet _ _ (by unhygienic cases $(mkIdent `st):ident; exact $t))
  | _ => throwUnsupportedSyntax

elab_rules : term
  | `([Veil|$stateTp:term|$l:lang]) => do elabLang l stateTp

/- TODO: avoid code duplication -/
/-- Same expansion as above but, intead of `funcases` we use `funclear` to
    prevent the generated code from depending on the pre-state -/
macro_rules
  | `([lang1|skip]) => `(@Lang.det _ _ (fun st => (st, ())))
  | `([lang1| $l1:lang; $l2:lang]) => `(@Lang.seq _ _ _ [lang1|$l1] [lang1|$l2])
  | `([lang1|require $t:term]) => do
      withRef t $ `(@Lang.require _ (funcases ($t : Prop) : _ -> Prop))
  | `([lang1|if $s:some_if ? $cnd:term { $thn:lang }]) => `([lang1|if $s:some_if ? $cnd { $thn } else { skip }])
  | `([lang1|if $cnd:term { $thn:lang } else { $els:lang }]) => do
    let cnd <- withRef cnd `(funclear ($cnd : Bool))
    `(@Lang.ite _ _ ($cnd: term) [lang1|$thn] [lang1|$els])
  | `([lang1| $id:structInstLVal := $t:term ]) =>
    `(@Lang.det _ _ (fun st => ({ st with $id := (by clear st; exact $t)}, ())))
  | `([lang1| $id:structInstLVal $ts: ident * := $t:term ]) =>
    `([lang1| $id:structInstLVal := fun $ts * => $t])
  | `([lang1|fresh $id:ident : $t in $l2:lang]) =>
      `(@Lang.fresh _ _ _ (fun $id : $t => [lang1|$l2]))
  -- | `([lang1| $id:structInstLVal $ts: term * := * ]) => do
  --   `(@Lang.nondet _ _ (fun st (st', ret) =>
  --     (∃ v, st' = { st with $id := ($(⟨id.raw.getHead?.get!⟩)[ $[$ts],* ↦ v ])}, ())))

end Lang
