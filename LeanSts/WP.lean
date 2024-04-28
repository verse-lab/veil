import Lean
import Lean.Parser
import LeanSts.DSLUtil
import LeanSts.DSL
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

def σTp (vs : Array Expr) : TermElabM Expr :=
  return mkAppN (<- stsExt.get).typ vs


def langTp (vs : Array Expr) : TermElabM Expr := do
  let σTp <- σTp vs
  mkAppM ``Lang #[σTp]

-- elab_rules : term
--   | `(lang| $l1:lang; $l2:lang) =>
--     liftCommandElabM $ runTermElabM fun vs => do
--     let l1  <- elabTerm l1 (<- langTp vs)
--     let l2  <- elabTerm l2 (<- langTp vs)
--     mkAppOptM ``Lang.seq #[none, l1, l2]
--   | `(lang| if $cnd:term then $thn:lang else $els:lang) =>
--     liftCommandElabM $ runTermElabM fun vs => do
--     let thn  <- elabTerm thn (<- langTp vs)
--     let els  <- elabTerm els (<- langTp vs)
--     let stx <- `(Term.byTactic| by intro st; unhygienic cases st; exact ($cnd : Bool))
--     let cnd <- elabByTactic stx (<- mkArrow (<- σTp) (mkConst ``Bool))
--     mkAppOptM ``Lang.ite #[none, cnd, thn, els]
--   | `(lang| require $t:term) =>
--       liftCommandElabM $ runTermElabM fun vs => do
--       let stx <- `(Term.byTactic| by intro st; unhygienic cases st; exact $t)
--       let rq <- elabByTactic stx (<- mkArrow (mkAppN (<- σTp) vs) prop)
--       mkAppOptM ``Lang.require #[none, rq]
--   | `(lang| do $t:term) =>
--       liftCommandElabM $ runTermElabM fun vs => do
--       let act <- elabTerm t (<- mkArrow (mkAppN (<- σTp) vs) (mkAppN (<- σTp) vs))
--       mkAppOptM ``Lang.act #[none, act]
--   | `(lang| $id:structInstLVal := $t:term) =>
--     liftCommandElabM $ runTermElabM fun vs => do
--     let st := mkIdent "st"
--     let act <- `(Term.byTactic| by unhygienic cases $st: ident; exact $t)
--     let stx <- `(Term.structInstField| $id: structInstLVal := $act:byTactic)
--     let stx <- `(lang| do (fun $st => { $st: ident with $stx: structInstField}))
--     elabTerm stx (<- langTp vs)

partial def elabLang (vs : Array Expr) : TSyntax `lang -> TermElabM Expr
  | `(lang| $l1:lang; $l2:lang) => do
    let l1  <- elabLang vs l1 --(<- langTp vs)
    let l2  <- elabLang vs l2 --(<- langTp vs)
    mkAppOptM ``Lang.seq #[none, l1, l2]
  | `(lang| if $cnd:term then $thn:lang else $els:lang) => do
    let thn  <- elabLang vs thn --(<- langTp vs)
    let els  <- elabLang vs els --(<- langTp vs)
    let stx <- `(Term.byTactic| by intro st; unhygienic cases st; exact ($cnd : Bool))
    let cnd <- elabByTactic stx (<- mkArrow (<- σTp vs) (mkConst ``Bool))
    mkAppOptM ``Lang.ite #[none, cnd, thn, els]
  | `(lang| require $t:term) => do
      let stx <- `(Term.byTactic| by intro st; unhygienic cases st; exact $t)
      let rq <- elabByTactic stx (<- mkArrow (<- σTp vs) prop)
      mkAppOptM ``Lang.require #[none, rq]
  | `(lang| do $t:term) => do
      let act <- elabTerm t (<- mkArrow (<- σTp vs) (<- σTp vs))
      mkAppOptM ``Lang.act #[none, act]
  | `(lang| $id:structInstLVal := $t:term) => do
    let st := mkIdent "st"
    let act <- `(Term.byTactic| by unhygienic cases $st: ident; exact $t)
    let stx <- `(Term.structInstField| $id: structInstLVal := $act:byTactic)
    let stx <- `(lang| do (fun $st => { $st: ident with $stx: structInstField}))
    elabLang vs stx --(<- langTp vs)
  | _ => throwUnsupportedSyntax

end WP

syntax "action" declId (explicitBinders)? " = " "{{" lang "}}" : command

elab_rules : command
  | `(command| action $nm:declId $br:explicitBinders ? = {{ $l:lang }}) => do
    elabCommand <| <- Command.runTermElabM fun vs => do
      let l <- elabLang vs l
      dbg_trace l
      let l <- PrettyPrinter.delab l
      let l <- `(term| fun st st' => wp _ (fun st => st' = st) $l st)
      `(action $nm $br ? := $l)


-- elab "{|" l:lang "|}" : term =>
--   liftCommandElabM $ runTermElabM fun vs => do
--   let lTp <- langTp vs
--   elabTerm l lTp

-- macro "{{" l:lang "}}" : term =>
--   `(term| fun st st' => wp _ (fun st => st' = st) {| $l |} st)

-- relation foo : Nat -> Prop
-- relation bar : Bool -> Prop
-- #gen_state

-- example st' st (n : Nat):
--       {{ require foo 5;
--          require bar true;
--          if (n = 5) then
--             bar := bar[true ↦ True]
--          else foo := foo[5 ↦ True] }} st st' := by
--   simp [actSimp]
--   sorry
