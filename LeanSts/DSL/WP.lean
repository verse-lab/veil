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
  | require (rq  : σ -> Prop) : Lang PUnit
  /-- Deterministic actions, although mostly used for assignments. All
      capital variables will be quantified. -/
  | act     {ρ' : Type u} (act : σ -> σ × ρ') : Lang ρ'
  /-- If-then-else. `open Classical` to allow propositions in the condition. -/
  | ite     {ρ : Type u} (cnd : σ -> Bool) (thn : Lang ρ) (els : Lang ρ) : Lang ρ
  /-- Sequence of actions -/
  | seq     {ρ ρ' : Type u} (l1 : Lang ρ') (l2 : Lang ρ) : Lang ρ

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
abbrev wlp (post : rprop σ ρ) : Lang σ ρ -> sprop σ
  -- `require` enhances the pre-condition, restricting the possible states
  -- it has the same effect as `assume` in Hoare logic
  | Lang.require rq       => fun s => rq s ∧ post () s
  -- a deterministic `act` transforms the state
  | Lang.act act          => fun s => let (s', ret) := act s ; post ret s'
  -- the meaning of `ite` depends on which branch is taken
  | Lang.ite cnd thn els  => fun s => if cnd s then wlp post thn s else wlp post els s
  -- `seq` is a composition of programs, so we need to compute the wlp of
  -- the first program, given the wlp of the second
  | Lang.seq l1 l2        =>
    let l2_wlp := wlp post l2
    -- the return value is not used in the pre-condition
    let l2_post := fun _ret s => l2_wlp s
    wlp l2_post l1

declare_syntax_cat lang
syntax lang ";" colGe lang : lang
syntax "skip"              : lang
syntax "require" term      : lang
syntax "do" term           : lang
syntax "if" term:max "then\n" lang "else\n" lang : lang
/-- intermediate syntax for assigment. The actual syntax is
    `pending := pending[n, s ↦ true]` -/
syntax Term.structInstLVal ":=" term    : lang
/-- syntax for assigment -/
syntax Term.structInstLVal (term:max)+ ":=" term    : lang
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
  | `([lang|skip]) => `(@Lang.act _ _ (fun st => (st, ())))
  | `([lang|$l1:lang; $l2:lang]) => `(@Lang.seq _ _ _ [lang|$l1] [lang|$l2])
  | `([lang|require $t:term]) => do
    let t' <- closeCapitals t
    withRef t $
      -- require a proposition on the state
     `(@Lang.require _ (funcases ($t' : Prop) : $(mkIdent `State) .. -> Prop))
  | `([lang|if $cnd:term then $thn:lang else $els:lang]) => do
    let cnd' <- closeCapitals cnd
    -- condition might depend on the state as well
    let cnd <- withRef cnd `(funcases ($cnd' : Bool))
    `(@Lang.ite _ _ ($cnd: term) [lang|$thn] [lang|$els])
  | `([lang| do $t:term ]) => `(@Lang.act _ _ $t)
    -- expansion of the intermediate syntax for assigment
    -- for instance `pending := pending[n, s ↦ true]` will get
    -- expanded to `Lang.act (fun st => { st with pending := st.pending[n, s ↦ true] })`
  | `([lang| $id:structInstLVal := $t:term ]) => do
    `(@Lang.act _ _ (fun st =>
      ({ st with $id := (by unhygienic cases st; exact $t)}, ())))
    -- expansion of the actual syntax for assigment
    -- for instance `pending n s := true` will get
    -- expanded to `pending := pending[n, s ↦ true]`
  | `([lang| $id:structInstLVal $ts: term * := $t:term ]) => do
    let stx <- withRef id `($(⟨id.raw.getHead?.get!⟩)[ $[$ts],* ↦ $t:term ])
    `([lang| $id:structInstLVal := $stx])

/- TODO: avoid code duplication -/
/-- Same expansion as above but, intead of `funcases` we use `funclear` to
    prevent the generated code from depending on the prestate -/
macro_rules
  | `([lang1|skip]) => `(@Lang.act _ _ (fun st => (st, ())))
  | `([lang1| $l1:lang; $l2:lang]) => `(@Lang.seq _ _ _ [lang1|$l1] [lang1|$l2])
  | `([lang1|require $t:term]) => do
      withRef t $
        `(@Lang.require _ _ (funclear ($t : Prop) : $(mkIdent `State) .. -> Prop))
  | `([lang1|if $cnd:term then $thn:lang else $els:lang]) => do
    let cnd <- withRef cnd `(funclear ($cnd : Bool))
    `(@Lang.ite _ _ ($cnd: term) [lang1|$thn] [lang1|$els])
  | `([lang1| $id:structInstLVal := $t:term ]) =>
    `(@Lang.act _ _ (fun st => ({ st with $id := (by clear st; exact $t)}, ())))
  | `([lang1| $id:structInstLVal $ts: ident * := $t:term ]) =>
    `([lang1| $id:structInstLVal := fun $ts * => $t])


end WP
