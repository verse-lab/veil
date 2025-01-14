import Lean

open Lean Elab Command

/- From: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/binderIdent.20vs.20Ident -/
def toBinderIdent (i : Ident) : TSyntax ``binderIdent := Unhygienic.run <|
  withRef i `(binderIdent| $i:ident)

def toIdent (bi : TSyntax ``binderIdent) : Ident :=
  match bi with
  | `(binderIdent|$i:ident) => i
  | _ => unreachable!

/-- Convert existential binders into definition binders. -/
def toBracketedBinderArray (stx : TSyntax `Lean.explicitBinders) : MetaM (TSyntaxArray `Lean.Parser.Term.bracketedBinder) := do
  let mut binders := #[]
  match stx with
  | `(explicitBinders|$bs*) => do
    binders := binders.append (← bs.mapM helper)
  | _ => throwError "unexpected syntax in explicit binder: {stx}"
  return binders.flatten
  where
  helper (stx : TSyntax `Lean.bracketedExplicitBinders) : MetaM (TSyntaxArray `Lean.Parser.Term.bracketedBinder) := do
    let mut binders := #[]
    match stx with
    | `(bracketedExplicitBinders|($bis* : $tp)) => do
      for bi in bis do
        let id := toIdent bi
        let fb ← `(bracketedBinder| ($id : $tp:term))
        binders := binders.push fb
      pure ()
    | _ => throwError "unexpected syntax in explicit binder: {stx}"
    return binders

/-- Convert existential binders into function binders. -/
def toFunBinderArray (stx : TSyntax `Lean.explicitBinders) : MetaM (TSyntaxArray `Lean.Parser.Term.funBinder) := do
  let mut binders := #[]
  match stx with
  | `(explicitBinders|$bs*) => do
    binders := binders.append (← bs.mapM helper)
  | _ => throwError "unexpected syntax in explicit binder: {stx}"
  return binders.flatten
  where
  helper (stx : TSyntax `Lean.bracketedExplicitBinders) : MetaM (TSyntaxArray `Lean.Parser.Term.funBinder) := do
    let mut binders := #[]
    match stx with
    | `(bracketedExplicitBinders|($bis* : $tp)) => do
      for bi in bis do
        let id := toIdent bi
        let fb ← `(Lean.Parser.Term.funBinder| ($id : $tp:term))
        binders := binders.push fb
      pure ()
    | _ => throwError "unexpected syntax in explicit binder: {stx}"
    return binders

/-- Convert existential binders (with explicit types) into terms (including only the identifiers). -/
def existentialIdents (stx : TSyntax `Lean.explicitBinders) : MetaM (TSyntaxArray `term) := do
  let mut vars := #[]
  match stx with
  | `(explicitBinders|$bs*) => do
    for b in bs do
      match b with
      | `(bracketedExplicitBinders|($bis* : $tp)) => do
        for bi in bis do
          let id := toIdent bi
          vars := vars.push id
      | _ => throwError "unexpected syntax in explicit binder: {b}"
  | _ => throwError "unexpected syntax in explicit binder: {stx}"
  return vars

/-- Create the syntax for something like `type1 → type2 → .. → typeN`, ending with `terminator`. -/
def mkArrowStx (tps : List Ident) (terminator : Option $ TSyntax `term := none) : CoreM (TSyntax `term) := do
  match tps with
  | [] => if let some t := terminator then return t else throwError "empty list of types and no terminator"
  | [a] => match terminator with
    | none => `(term| $a)
    | some t => `(term| $a -> $t)
  | a :: as =>
    let cont ← mkArrowStx as terminator
    `(term| $a -> $cont)

def complexBinderToSimpleBinder (nm : TSyntax `ident) (br : TSyntaxArray `Lean.Parser.Term.bracketedBinder) (domT : TSyntax `term) : CoreM (TSyntax `Lean.Parser.Command.structSimpleBinder) := do
  let types ← br.mapM fun m => match m with
    | `(bracketedBinder| ($_arg:ident : $tp:term)) => return (mkIdent tp.raw.getId)
    | _ => throwError "Invalid binder syntax {br}"
  let typeStx ← mkArrowStx types.toList domT
  let simple ← `(Lean.Parser.Command.structSimpleBinder| $nm:ident : $typeStx)
  return simple

/-- Given `nm : _ `, return `nm` -/
def getSimpleBinderName (sig : TSyntax `Lean.Parser.Command.structSimpleBinder) : CoreM Name := do
  match sig with
  | `(Lean.Parser.Command.structSimpleBinder| $nm:ident : $_:term) => pure nm.getId
  | _ => throwError s!"getSimpleBinderName: don't know how to handle {sig}"

/-- Given `nm : type`, return `type` -/
def getSimpleBinderType (sig : TSyntax `Lean.Parser.Command.structSimpleBinder) : CoreM (TSyntax `term) := do
  match sig with
  | `(Lean.Parser.Command.structSimpleBinder| $_:ident : $tp:term) => pure tp
  | _ => throwError s!"getSimpleBinderType: don't know how to handle {sig}"

def createExistsBinders (vars : Array (Ident × Option Name)) : MetaM (Array (TSyntax `Lean.bracketedExplicitBinders)) := do
  let binders ← vars.mapM fun (var, sort) => do
    let bi := toBinderIdent var
    match sort with
    | none => return ← `(bracketedExplicitBinders|($bi : _))
    | some sort => return ← `(bracketedExplicitBinders|($bi : $(mkIdent sort)))
  return binders

def repeatedExists (vars : Array (Ident × Option Name)) (body : TSyntax `term) : MetaM (TSyntax `term) := do
  let binders ← createExistsBinders vars
  if binders.size == 0 then return body
  else `(term|∃ $binders*, $body)

def createForallBinders (vars : Array (Ident × Option Name)) : MetaM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let binders ← vars.mapM fun (var, sort) => do
    match sort with
    | none => return ← `(bracketedBinder|($var))
    | some sort => return ← `(bracketedBinder|($var : $(mkIdent sort)))
  return binders

def repeatedForall (vars : Array (Ident × Option Name)) (body : TSyntax `term) : MetaM (TSyntax `term) := do
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

def mkOrN : List Expr → Expr
  | [] => mkConst ``True
  | [p] => p
  | p :: ps => mkOr p (mkOrN ps)
