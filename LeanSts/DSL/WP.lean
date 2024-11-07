import Lean
import Lean.Parser
import LeanSts.State
import LeanSts.DSL.Util

open Lean Elab Command Term Meta Lean.Parser

section WP

variable (σ : Type)
/-- Imperative language for defining actions. -/
inductive Lang.{u} : Type u → Type (u + 1) where
  /-- Pre-condition. All capital variables will be quantified. -/
  | require (rq : σ -> Prop) : Lang PUnit
  | assume  (as : σ -> Prop) : Lang PUnit
  | bind    {ρ ρ' : Type u} (act : Lang ρ') (act' : ρ' -> Lang ρ) : Lang ρ
  /-- Deterministic changes to the state, although mostly used for assignments. All
      capital variables will be quantified. -/
  | det     {ρ' : Type u} (act : σ -> σ × ρ') : Lang ρ'
  /-- Non-deterministic changes to the state. -/
  | nondet  {ρ' : Type u} (act :  σ -> σ × ρ' -> Prop) : Lang ρ'
  -- τ is a first order type, so it can be quantified in FOL
  | nondetVal {τ : Type} {ρ' : Type u} (act : τ -> σ -> σ × ρ') : Lang ρ'
  /-- If-then-else. `open Classical` to allow propositions in the condition. -/
  | ite     {ρ : Type u} (cnd : σ -> Bool) (thn : Lang ρ) (els : Lang ρ) : Lang ρ
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
  | Lang.assume  as       => fun s => as s → post () s
  -- a deterministic `act` transforms the state
  | Lang.det act          => fun s => let (s', ret) := act s ; post ret s'
  -- a non-deterministic `nondet`
  | Lang.nondet act       => fun s => ∀ s' ret, act s (s', ret) → post ret s'
  | Lang.nondetVal act    => fun s => ∃ t, let (s', ret) := act t s ; post ret s'
  -- the meaning of `ite` depends on which branch is taken
  | Lang.ite cnd thn els  => fun s => if cnd s then wlp post thn s else wlp post els s
  -- `seq` is a composition of programs, so we need to compute the wlp of
  -- the first program, given the wlp of the second
  | Lang.seq l1 l2        =>
    wlp (fun _ => wlp post l2) l1
  | Lang.ret ret    => post ret
  | Lang.bind l1 l2 =>
    wlp (fun ret => wlp post (l2 ret)) l1

declare_syntax_cat lang
syntax lang ";" colGe lang : lang
syntax "skip"              : lang
/-- Non-deterministic value. -/
syntax (name := nondetVal) "*" : lang
syntax "require" term      : lang
syntax "assume" term       : lang
syntax "do" term           : lang
syntax (priority := high) "if" term:max "{" lang "}" "else\n" "{" lang "}" : lang
syntax (priority := low) "if" term:max "{" lang "}" : lang
/-- intermediate syntax for assigment, e.g. `pending := pending[n, s ↦ true]` -/
syntax Term.structInstLVal ":=" term    : lang
/-- syntax for assigment, e.g. `pending n s := true` -/
syntax Term.structInstLVal (term:max)+ ":=" (term <|> nondetVal)    : lang
syntax ident "<-" lang "in" lang : lang
syntax "return" term : lang
syntax "call" term : lang
/-- Syntax to trigger the expantion into a code which may
    depend on the prestate -/
syntax "[lang|" lang "]" : term
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
def closeCapitals (s : Term) : MacroM Term :=
  let caps := getCapitals s
  `(forall $[$caps]*, $s)


macro_rules
  | `([lang|skip]) => `(@Lang.det _ _ (fun st => (st, ())))
  | `([lang|$l1:lang; $l2:lang]) => `(@Lang.seq _ _ _ [lang|$l1] [lang|$l2])
  | `([lang|require $t:term]) => do
    let t' <- closeCapitals t
    withRef t $
      -- require a proposition on the state
     `(@Lang.require _ (funcases ($t' : Prop) : $(mkIdent `State) .. -> Prop))
  | `([lang|assume $t:term]) => do
    let t' <- closeCapitals t
    withRef t $ `(@Lang.assume _ (funcases ($t' : Prop) : $(mkIdent `State) .. -> Prop))
  | `([lang|if $cnd:term { $thn:lang }]) => `([lang|if $cnd { $thn } else { skip }])
  | `([lang|if $cnd:term { $thn:lang } else { $els:lang }]) => do
    let cnd' <- closeCapitals cnd
    -- condition might depend on the state as well
    let cnd <- withRef cnd `(funcases ($cnd' : Bool))
    `(@Lang.ite _ _ ($cnd: term) [lang|$thn] [lang|$els])
  | `([lang| do $t:term ]) => `(@Lang.det _ _ $t)
    -- expansion of the intermediate syntax for assigment
    -- for instance `pending := pending[n, s ↦ true]` will get
    -- expanded to `Lang.det (fun st => { st with pending := st.pending[n, s ↦ true] })`
  | `([lang| $id:structInstLVal := $t:term ]) => do
    `(@Lang.det _ _ (fun st =>
      ({ st with $id := (by unhygienic cases st; exact $t)}, ())))
  -- for instance `pending n s := *` will get
  -- | `([lang| $id:structInstLVal $ts: term * := * ]) => do
  --   `(@Lang.nondet _ _ (fun st (st', ()) =>
  --     (∃ v, st' = { st with $id := (by unhygienic cases st; exact ($(⟨id.raw.getHead?.get!⟩)[ $[$ts],* ↦ v ]))})))
  | `([lang| $id:structInstLVal $ts: term * := * ]) => do
    `(@Lang.nondetVal _ _ _ (fun v st =>
      ({ st with $id := (by unhygienic cases st; exact ($(⟨id.raw.getHead?.get!⟩)[ $[$ts],* ↦ v ]))}, ())))
  --   -- expansion of the actual syntax for assigment
    -- for instance `pending n s := true` will get
    -- expanded to `pending := pending[n, s ↦ true]`
  | `([lang| $id:structInstLVal $ts: term * := $t:term ]) => do
    let stx <- withRef id `($(⟨id.raw.getHead?.get!⟩)[ $[$ts],* ↦ $t:term ])
    `([lang| $id:structInstLVal := $stx])
  | `([lang| $id:ident <- $l1:lang in $l2:lang]) => do
      `(@Lang.bind _ _ _ [lang|$l1] (fun $id => [lang|$l2]))
  | `([lang|return $t:term]) => `(@Lang.ret _ _ (by unhygienic cases $(mkIdent `st):ident; exact $t))
  | `([lang|call $t:term]) => `(@Lang.nondet _ _ (by unhygienic cases $(mkIdent `st):ident; exact $t))


/- TODO: avoid code duplication -/
/-- Same expansion as above but, intead of `funcases` we use `funclear` to
    prevent the generated code from depending on the pre-state -/
macro_rules
  | `([lang1|skip]) => `(@Lang.det _ _ (fun st => (st, ())))
  | `([lang1| $l1:lang; $l2:lang]) => `(@Lang.seq _ _ _ [lang1|$l1] [lang1|$l2])
  | `([lang1|require $t:term]) => do
      withRef t $ `(@Lang.require _ (funcases ($t : Prop) : $(mkIdent `State) .. -> Prop))
  | `([lang1|assume $t:term]) => do
      withRef t $ `(@Lang.assume _ (funcases ($t : Prop) : $(mkIdent `State) .. -> Prop))
  | `([lang1|if $cnd:term { $thn:lang }]) => `([lang1|if $cnd { $thn } else { skip }])
  | `([lang1|if $cnd:term { $thn:lang } else { $els:lang }]) => do
    let cnd <- withRef cnd `(funclear ($cnd : Bool))
    `(@Lang.ite _ _ ($cnd: term) [lang1|$thn] [lang1|$els])
  | `([lang1| $id:structInstLVal := $t:term ]) =>
    `(@Lang.det _ _ (fun st => ({ st with $id := (by clear st; exact $t)}, ())))
  | `([lang1| $id:structInstLVal $ts: ident * := $t:term ]) =>
    `([lang1| $id:structInstLVal := fun $ts * => $t])
  -- | `([lang1| $id:structInstLVal $ts: term * := * ]) => do
  --   `(@Lang.nondet _ _ (fun st (st', ret) =>
  --     (∃ v, st' = { st with $id := ($(⟨id.raw.getHead?.get!⟩)[ $[$ts],* ↦ v ])}, ())))

end WP
