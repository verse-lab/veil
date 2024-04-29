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
syntax "{|" lang "|}" : term

macro_rules
  | `({|$l1:lang; $l2:lang|}) => do
    `(@Lang.seq _ {|$l1|} {|$l2|})
  | `({|require $t:term|}) => do
     `(@Lang.require _
       ((by intro st;
            unhygienic cases st;
            exact ($t : Prop)) : $(mkIdent "State") .. -> Prop))
  | `({|if $cnd:term then $thn:lang else $els:lang|}) => do
    `(@Lang.ite _ (by intro st;
                      unhygienic cases st;
                      exact ($cnd : Bool)) {|$thn|} {|$els|})
  | `({| do $t:term |}) => `(@Lang.act _ $t)
  | `({| $id:structInstLVal := $t:term |}) =>
    `(@Lang.act _ (fun st =>
      { st with $id := (
        (by unhygienic cases st;
            exact $t))}))

-- macro "{{" l:lang "}}" : term =>
--   `(fun st st' => @wp _ (fun st => st' = st) {| $l |} st)

end WP
