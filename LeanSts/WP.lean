import Lean
import Lean.Parser
import LeanSts.DSLUtil
import LeanSts.State

open Lean Elab Command Term Meta Lean.Parser

section WP

variable (σ : Type)

inductive Lang where
  | require (rq  : σ -> Prop)
  | act    (act : σ -> σ)
  | ite    (cnd : σ -> Bool) (thn : Lang) (els : Lang)
  | seq    (l1 : Lang) (l2 : Lang)

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
syntax Term.structInstLVal ":=" term    : lang
syntax Term.structInstLVal (term:max)+ ":=" term    : lang
syntax "[lang|" lang "]" : term
syntax "[lang1|" lang "]" : term

macro_rules
  | `([lang|$l1:lang; $l2:lang]) => `(@Lang.seq _ [lang|$l1] [lang|$l2])
  | `([lang|require $t:term]) =>
    withRef t $
     `(@Lang.require _ (funcases ($t : Prop) : $(mkIdent "State") .. -> Prop))
  | `([lang|if $cnd:term then $thn:lang else $els:lang]) => do
    let cnd <- withRef cnd `(funcases ($cnd : Bool))
    `(@Lang.ite _ ($cnd: term) [lang|$thn] [lang|$els])
  | `([lang| do $t:term ]) => `(@Lang.act _ $t)
  | `([lang| $id:structInstLVal := $t:term ]) =>
    `(@Lang.act _ (fun st =>
      { st with $id := (by unhygienic cases st; exact $t)}))
  | `([lang| $id:structInstLVal $ts: term * := $t:term ]) => do
    -- dbg_trace id.raw.getHead?.get!
    let stx <- withRef id `($(⟨id.raw.getHead?.get!⟩)[ $[$ts],* ↦ $t:term ])
    `([lang| $id:structInstLVal := $stx])


/- TODO: avoid code duplication -/
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
