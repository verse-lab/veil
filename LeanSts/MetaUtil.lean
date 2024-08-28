import Lean

open Lean

/- From: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/binderIdent.20vs.20Ident -/
def toBinderIdent (i : Ident) : TSyntax ``binderIdent := Unhygienic.run <|
  withRef i `(binderIdent| $i:ident)

def createExistsBinders (vars : Array (Ident × Name)) : MetaM (Array (TSyntax `Lean.bracketedExplicitBinders)) := do
  let binders ← vars.mapM fun (var, sort) => do
    let bi := toBinderIdent var
    let sn := mkIdent sort
    return ← `(bracketedExplicitBinders|($bi : $sn))
  return binders

def repeatedExists (vars : Array (Ident × Name)) (body : TSyntax `term) : MetaM (TSyntax `term) := do
  let binders ← createExistsBinders vars
  if binders.size == 0 then return body
  else `(term|∃ $binders*, $body)

def createForallBinders (vars : Array (Ident × Name)) : MetaM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let binders ← vars.mapM fun (var, sort) => do
    let sn := mkIdent sort
    return ← `(bracketedBinder|($var : $sn))
  return binders

def repeatedForall (vars : Array (Ident × Name)) (body : TSyntax `term) : MetaM (TSyntax `term) := do
  let binders ← createForallBinders vars
  if binders.size == 0 then return body
  else `(term|∀ $binders*, $body)

def repeatedOp (op : Name) (default : TSyntax `term) (operands : Array (TSyntax `term)) : MetaM (TSyntax `term) := do
  if operands.isEmpty then return default
  else
    let initT := operands[0]!
    let acc := operands[1:]
    acc.foldlM (init := initT) fun operand acc => `(term|$(mkIdent op) $operand $acc)

def repeatedAnd (operands : Array (TSyntax `term)) : MetaM (TSyntax `term) := do
  repeatedOp `And (default := ← `(term|$(mkIdent `True))) operands

def repeatedOr (operands : Array (TSyntax `term)) : MetaM (TSyntax `term) := do
  repeatedOp `Or (default := ← `(term|$(mkIdent `False))) operands
