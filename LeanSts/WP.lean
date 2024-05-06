import Lean
import Lean.Parser
import LeanSts.DSLUtil
import LeanSts.State

open Lean Elab Command Term Meta Lean.Parser

section WP

variable (σ : Type)
/--
Language for defining programs in relational transition systems.
-/
inductive Lang where
    /-- All capital variables will be quantified -/
  | require (rq  : σ -> Prop)
    /-- this is mostly used for assignments. But we can have a command that arbitrarily changes the state
         All capital variables will be quantifiedl -/
  | act     (act : σ -> σ)
  | ite     (cnd : σ -> Bool) (thn : Lang) (els : Lang)
  | seq     (l1 : Lang) (l2 : Lang)

@[inline] abbrev hprop := σ -> Prop

@[actSimp] abbrev wp (post : hprop σ) : Lang σ -> hprop σ
  | Lang.require rq      => fun s => rq s ∧ post s
  | Lang.act act         => fun s => post (act s)
  | Lang.ite cnd thn els => fun s => if cnd s then wp post thn s else wp post els s
  | Lang.seq l1 l2       => wp (wp post l2) l1

declare_syntax_cat lang
syntax lang ";" colGe lang : lang
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
  | `([lang|$l1:lang; $l2:lang]) => `(@Lang.seq _ [lang|$l1] [lang|$l2])
  | `([lang|require $t:term]) => do
    let t' <- closeCapitals t
    withRef t $
      -- require a proposition on the state
     `(@Lang.require _ (funcases ($t' : Prop) : $(mkIdent "State") .. -> Prop))
  | `([lang|if $cnd:term then $thn:lang else $els:lang]) => do
    let cnd' <- closeCapitals cnd
    -- condition might depend on the state as well
    let cnd <- withRef cnd `(funcases ($cnd' : Bool))
    `(@Lang.ite _ ($cnd: term) [lang|$thn] [lang|$els])
  | `([lang| do $t:term ]) => `(@Lang.act _ $t)
    -- expansion of the intermediate syntax for assigment
    -- for intance `pending := pending[n, s ↦ true]` will get
    -- expanded to `Lang.act (fun st => { st with pending := st.pending[n, s ↦ true] })`
  | `([lang| $id:structInstLVal := $t:term ]) => do
    `(@Lang.act _ (fun st =>
      { st with $id := (by unhygienic cases st; exact $t)}))
    -- expansion of the actual syntax for assigment
    -- for intance `pending n s := true` will get
    -- expanded to `pending := pending[n, s ↦ true]`
  | `([lang| $id:structInstLVal $ts: term * := $t:term ]) => do
    let stx <- withRef id `($(⟨id.raw.getHead?.get!⟩)[ $[$ts],* ↦ $t:term ])
    `([lang| $id:structInstLVal := $stx])

/- TODO: avoid code duplication -/
/-- Same expansion as above but, intead of `funcases` we use `funclear` to
    prevent the generated code from depending on the prestate -/
macro_rules
  | `([lang1| $l1:lang; $l2:lang]) => `(@Lang.seq _ [lang1|$l1] [lang1|$l2])
  | `([lang1|require $t:term]) => do
      withRef t $
        `(@Lang.require _ (funclear ($t : Prop) : $(mkIdent "State") .. -> Prop))
  | `([lang1|if $cnd:term then $thn:lang else $els:lang]) => do
    let cnd <- withRef cnd `(funclear ($cnd : Bool))
    `(@Lang.ite _ ($cnd: term) [lang1|$thn] [lang1|$els])
  | `([lang1| $id:structInstLVal := $t:term ]) =>
    `(@Lang.act _ (fun st => { st with $id := (by clear st; exact $t)}))
  | `([lang1| $id:structInstLVal $ts: ident * := $t:term ]) =>
    `([lang1| $id:structInstLVal := fun $ts * => $t])


end WP
