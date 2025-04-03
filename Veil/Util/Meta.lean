import Lean

open Lean Elab Command

/-- The directory of the file being currently compiled. -/
syntax (name := currentDirectory) "currentDirectory!" : term

open Lean Elab Elab.Term in
@[term_elab currentDirectory] def elabCurrentFilePath : TermElab
  | `(currentDirectory!), _ => do
    let ctx ← readThe Lean.Core.Context
    let srcPath := System.FilePath.mk ctx.fileName
    let some srcDir := srcPath.parent
      | throwError "cannot compute parent directory of '{srcPath}'"
    return mkStrLit s!"{srcDir}"
  | _, _ => throwUnsupportedSyntax

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
/-- Convert definition binders into existential binders. -/
def toExplicitBinders [Monad m] [MonadError m] [MonadQuotation m] (stx : TSyntax `Lean.Parser.Term.bracketedBinder) : m (TSyntax `Lean.bracketedExplicitBinders) := do
  match stx with
  | `(bracketedBinder| ($id:ident : $tp:term))
  | `(bracketedBinder| [$id:ident : $tp:term])
  | `(bracketedBinder| {$id:ident : $tp:term}) =>
    return ← `(bracketedExplicitBinders|($(toBinderIdent id) : $tp))
  | _ => throwError "unexpected syntax in explicit binder: {stx}"

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
def explicitBindersIdents (stx : TSyntax `Lean.explicitBinders) : MetaM (TSyntaxArray `term) := do
  let mut vars := #[]
  match stx with
  | `(explicitBinders|$bs*) => do
    for b in bs do
      match b with
      | `(bracketedExplicitBinders|($bis* : $_tp)) => do
        for bi in bis do
          let id := toIdent bi
          vars := vars.push id
      | _ => throwError "unexpected syntax in explicit binder: {b}"
  | _ => throwError "unexpected syntax in explicit binder: {stx}"
  return vars

def bracketedBinderIdent [Monad m] [MonadError m] [MonadQuotation m] (stx : TSyntax `Lean.Parser.Term.bracketedBinder) : m (Option Ident) := do
  match stx with
  | `(bracketedBinder| ($id:ident : $_tp)) => return id
  | `(bracketedBinder| [$id:ident : $_tp]) => return id
  | `(bracketedBinder| {$id:ident : $_tp}) => return id
  | _ => return none

/-- Given a set of binders, return the terms that correspond to them.
Typeclasses that are not named are replaced with `_`, to be inferred. -/
def bracketedBindersToTerms [Monad m] [MonadError m] [MonadQuotation m] (stx : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) : m (Array Term) := do
  let idents : Array (Option Ident) ← stx.mapM bracketedBinderIdent
  let terms ← idents.mapM (fun mid => do
    match mid with
    | some id => `(term|$id)
    | none => `(term|_))
  return terms

def toBindersWithInferredTypes (stx : TSyntax `Lean.explicitBinders) [Monad m] [MonadEnv m] [MonadError m] [MonadQuotation m] : m (TSyntax `Lean.explicitBinders) := do
 let mut newBinders := #[]
  match stx with
  | `(explicitBinders|$bs*) => do
    for b in bs do
      match b with
      | `(bracketedExplicitBinders|($bis* : $_tp)) => do
         newBinders := newBinders.push (← `(bracketedExplicitBinders|($bis* : _)))
      | _ => throwError "unexpected syntax in explicit binder: {b}"
  | _ => throwError "unexpected syntax in explicit binder: {stx}"
  return ← `(explicitBinders| $newBinders*)


/-- Convert existential binders (with explicit types) into terms (including only the identifiers). -/
def toBindersWithMappedTypes (stx : TSyntax `Lean.explicitBinders) (mapping : Array (Term × Term)) : CommandElabM (TSyntax `Lean.explicitBinders) := do
  let mut newBinders := #[]
  match stx with
  | `(explicitBinders|$bs*) => do
    for b in bs do
      match b with
      | `(bracketedExplicitBinders|($bis* : $tp)) => do
        let newTp := match mapping.find? (fun (paramType, _argType) => paramType == tp) with
          | some (_, newTp) => newTp
          | none => tp
        newBinders := newBinders.push $ ← `(bracketedExplicitBinders|($bis* : $newTp))
      | _ => throwError "unexpected syntax in explicit binder: {b}"
  | _ => throwError "unexpected syntax in explicit binder: {stx}"
  let newStx ← `(explicitBinders|$newBinders*)
  return newStx

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
def getSimpleBinderName [Monad m] [MonadError m] (sig : TSyntax `Lean.Parser.Command.structSimpleBinder) : m Name := do
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

def simpleAddDefn (n : Name) (e : Expr)
  (red := Lean.ReducibilityHints.regular 0)
  (attr : Array Attribute := #[])
  (type : Option Expr := none) : TermElabM Unit := do
  addDecl <|
    Declaration.defnDecl <|
      mkDefinitionValEx n [] (type.getD <| ← Meta.inferType e) e red
      (DefinitionSafety.safe) []
  Elab.Term.applyAttributes n attr

def mkLambdaFVarsImplicit (vs : Array Expr) (e : Expr) : TermElabM Expr := do
  let e <- Meta.mkLambdaFVars vs e
  return go vs.size e
  where go (cnt : Nat) (e : Expr) : Expr :=
    match cnt, e with
    | 0, _ => e
    | _, Expr.lam n d b .default =>
      let b := go (cnt-1) b
      Expr.lam n d b .implicit
    | _, Expr.lam n d b bi =>
      let b := go (cnt-1) b
      Expr.lam n d b bi
    | _, _ => e

open Meta in
/-- Generates a repeated-`op` of all expressions in `exps`, each applied
to `vs`. For instance, when called with `Or` and the list of actions,
this gives us the `Next` transition.-/
def combineLemmas (op : Name) (exps: List Expr) (vs : Array Expr) (name : String) : MetaM Expr := do
    let exp0 :: exprs := exps
      | throwError ("There are no " ++ name ++ " defined")
    let exp0 <- etaExpand exp0
    let exps <- lambdaTelescope exp0 fun args exp0 => do
      let mut exps := exp0
      for exp in exprs do
        let exp := mkAppN exp args
        exps <- mkAppM op #[exp, exps]
      mkLambdaFVars args exps
    instantiateLambda exps vs

open Meta in
partial def turnExistsIntoForall (e : Expr) : MetaM Expr := do
  match_expr e with
  | Exists _t eBody =>
  lambdaBoundedTelescope eBody (maxFVars := 1) (fun ks lBody => do
    mkForallFVars ks (← turnExistsIntoForall lBody)
  )
  | _ => return e

def getItemsFromDoSeq [Monad m] [MonadError m] [MonadQuotation m] (l : TSyntax `Lean.Parser.Term.doSeq) : m (TSyntaxArray `Lean.Parser.Term.doSeqItem) := do
  match l with
  | `(doSeq|$items*) => pure items
  | `(doSeq|{ $items* }) => pure items
  | _ => throwError "Unexpected doSeq: {l}"
