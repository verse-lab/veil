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

-- def σTp (vs : Array Expr) : TermElabM Expr :=
--   return mkAppN (<- stsExt.get).typ vs


-- def langTp (vs : Array Expr) : TermElabM Expr := do
--   let σTp <- σTp vs
--   mkAppM ``Lang #[σTp]

def σTp : TermElabM Expr :=
  return (<- stsExt.get).typ_vs


def langTp : TermElabM Expr := do
  mkAppOptM ``Lang #[<- σTp]

elab_rules : term
  | `(lang| $l1:lang; $l2:lang) => do
    let l1 <- elabTerm l1 (<- langTp)
    let l2  <- elabTerm l2 (<- langTp)
    mkAppOptM ``Lang.seq #[none, l1, l2]
  | `(lang| if $cnd:term then $thn:lang else $els:lang) => do
    let thn  <- elabTerm thn (<- langTp)
    let els  <- elabTerm els (<- langTp)
    let stx <- `(Term.byTactic| by intro st; unhygienic cases st; exact ($cnd : Bool))
    let cnd <- elabByTactic stx (<- mkArrow (<- σTp) (mkConst ``Bool))
    mkAppOptM ``Lang.ite #[none, cnd, thn, els]
  | `(lang| do $t:term) => do
      let act <- elabTerm t (<- mkArrow (<- σTp) (<- σTp))
      mkAppOptM ``Lang.act #[none, act]
  | `(lang| $id:structInstLVal := $t:term) => do
    let st := mkIdent "st"
    let act <- `(Term.byTactic| by unhygienic cases $st: ident; exact $t)
    let stx <- `(Term.structInstField| $id: structInstLVal := $act:byTactic)
    let stx <- `(lang| do (fun $st => { $st: ident with $stx: structInstField}))
    elabTerm stx (<- langTp)

macro_rules
  | `(lang| require $t:term) => do
     `(term| @Lang.require _
       ((by intro st;
            unhygienic cases st;
            exact ($t : Prop)) : $(mkIdent "State") .. -> Prop))

-- partial def elabLang (vs : Array Expr) : TSyntax `lang -> TermElabM Expr
--   | `(lang| $l1:lang; $l2:lang) => do
--     let l1  <- elabLang vs l1 --(<- langTp vs)
--     let l2  <- elabLang vs l2 --(<- langTp vs)
--     mkAppOptM ``Lang.seq #[none, l1, l2]
--   | `(lang| if $cnd:term then $thn:lang else $els:lang) => do
--     let thn  <- elabLang vs thn --(<- langTp vs)
--     let els  <- elabLang vs els --(<- langTp vs)
--     let stx <- `(Term.byTactic| by intro st; unhygienic cases st; exact ($cnd : Bool))
--     let cnd <- elabByTactic stx (<- mkArrow (<- σTp vs) (mkConst ``Bool))
--     mkAppOptM ``Lang.ite #[none, cnd, thn, els]
--   | `(lang| require $t:term) => do
--       let stx <- `(Term.byTactic| by intro st; unhygienic cases st; exact $t)
--       let tp <- mkArrow (<- σTp vs) prop
--       dbg_trace ("type:" ++ toString stx)
--       let rq <- elabByTactic stx tp
--       dbg_trace ("type:" ++ toString rq)
--       mkAppOptM ``Lang.require #[none, rq]
--   | `(lang| do $t:term) => do
--       let act <- elabTerm t (<- mkArrow (<- σTp vs) (<- σTp vs))
--       mkAppOptM ``Lang.act #[none, act]
--   | `(lang| $id:structInstLVal := $t:term) => do
--     let st := mkIdent "st"
--     let act <- `(Term.byTactic| by unhygienic cases $st: ident; exact $t)
--     let stx <- `(Term.structInstField| $id: structInstLVal := $act:byTactic)
--     let stx <- `(lang| do (fun $st => { $st: ident with $stx: structInstField}))
--     elabLang vs stx --(<- langTp vs)
--   | _ => throwUnsupportedSyntax

end WP

syntax "action" declId (explicitBinders)? " = " "{{" lang "}}" : command

elab "{|" l:lang "|}" : term => do
  let lTp <- langTp
  elabTerm l lTp

elab_rules : command
  | `(command| action $nm:declId $br:explicitBinders ? = {{ $l:lang }}) => do
    let vd := (<- getScope).varDecls
    elabCommand <| <- Command.runTermElabM fun vs => do
      let stateTp := (<- stsExt.get).typ
      unless stateTp != default do throwError "State has not been declared so far"
      let stateTp := mkAppN stateTp vs
      stsExt.modify fun s => { s with typ_vs := stateTp }
      -- let l <- elabTermAndSynthesize l (<- langTp)
      -- dbg_trace l
      -- let l <- PrettyPrinter.delab l
      let act <- `(term| fun st st' => @wp _ (fun st => st' = st) {| $l:lang |} st)
      match br with
      | some br =>
        let _ <- elabTerm (<-`(term| fun st1 st2 => exists $br, $act st1 st2)) (<- mkArrow stateTp (<- mkArrow stateTp prop))
      | none =>
        let _ <- elabTerm act (<- mkArrow stateTp (<- mkArrow stateTp prop))
      let stateTp <- PrettyPrinter.delab stateTp
      match br with
      | some br =>                                                            -- TODO: add macro a beta reduction here
        `(@[actDef, actSimp] def $nm $[$vd]* : $stateTp -> $stateTp -> Prop := fun st1 st2 => exists $br, $act st1 st2)
      | _ => do
        `(@[actDef, actSimp] def $nm $[$vd]* : $stateTp -> $stateTp -> Prop := $act)


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
