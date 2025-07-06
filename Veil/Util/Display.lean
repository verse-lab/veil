import Lean
import Veil.Util.DSL
import Veil.SMT.Main

open Lean Elab Meta Tactic TryThis

def displaySuggestion (stx : Syntax) (theorems : Array (TSyntax `command)) (preMsg : Option String := none) := do
    Command.liftTermElabM do
    let cmd ← constructCommands theorems
    let suggestion : Suggestion := {
      suggestion := cmd
      preInfo? := preMsg
      toCodeActionTitle? := .some (fun _ => "Replace with explicit proofs.")
    }
    addSuggestion stx suggestion (header := "")

def emoji (res : SmtResult) : String :=
  match res with
  | .Unsat => "✅"
  | .Sat _ => "❌"
  | .Unknown _ => s!"❓"
  | .Failure reason => s!"💥 {reason}"

def getBaseNameForDisplay (n : Name) : Name := stripFirstComponent n

structure TheoremIdentifier where
  /- If it's `none`, it's the termination check for the action. -/
  invName : Option Name
  /-- If it's `none`, it's the initial action. -/
  actName : Option Name
  theoremName : Name
deriving Inhabited, BEq, ToJson, FromJson, Hashable

def getTimeForDisplay [Monad m] [MonadOptions m] (time : Option TimeInMs) : m String := do
  if !veil.showVerificationTime.get (← getOptions) then
    return ""
  return match time with
  | .some time => s!" ({time} ms)"
  | .none => ""

def getInitCheckResultMessages' [Monad m] [MonadOptions m]  (res: List (Name × SmtResult × Option TimeInMs)) : m (Array String) := do
  let mut msgs := #[]
  if !res.isEmpty then
    msgs := msgs.push "Initialization must establish the invariant:"
    for (invName, (r, time)) in res do
      msgs := msgs.push s!"  {getBaseNameForDisplay invName} ... {emoji r}{← getTimeForDisplay time}"
  pure msgs

def getInitCheckResultMessages [Monad m] [MonadOptions m] (res : List (TheoremIdentifier × SmtResult × Option TimeInMs)) : m (Array String) :=
  getInitCheckResultMessages' (res.map (fun (id, r) => (id.invName.getD `termination, r)))

/-- `(invName, actName, result)` -/
def getActCheckResultMessages' [Monad m] [MonadOptions m] (res: List (Name × Name × SmtResult × Option TimeInMs)) : m (Array String) := do
  let mut msgs := #[]
  if !res.isEmpty then
    msgs := msgs.push "The following set of actions must preserve the invariant and successfully terminate:"
    for (actName, invResults) in group res do
      msgs := msgs.push s!"  {getBaseNameForDisplay actName}"
      for (invName, (r, time)) in invResults do
        msgs := msgs.push s!"    {getBaseNameForDisplay invName} ... {emoji r}{← getTimeForDisplay time}"
  pure msgs
where group {T : Type} (xs : List (Name × T)) : List (Name × List T) :=
  xs.foldl (fun acc (key, val) =>
    match acc.find? (fun (k, _) => k = key) with
    | some (k, vs) =>
          acc.filter (fun (k', _) => k' ≠ key) ++ [(k, vs ++ [val])]
    | none =>
      acc ++ [(key, [val])]) []

def getActCheckResultMessages [Monad m] [MonadOptions m] (res : List (TheoremIdentifier × SmtResult × Option TimeInMs)) : m (Array String) :=
  getActCheckResultMessages' (res.map (fun (id, r) => (id.actName.get!, id.invName.getD `termination, r)))

def getModelStr (msg : String) : String :=
  let resWithErr := match msg.splitOn Veil.SMT.satGoalStr with
    | [_, model] => model
    /- multiple models can be returned, e.g. due to the `split_ifs` in `solve_clause_wp` -/
    | _ :: model :: _rest => model
    | _ => msg
  /- at this point, the message string looks like this:
  ```
  interpreted sort Bool
  sort processor = #[processor0, processor1]

  /Users/dranov/src/veil/Examples/Spec.lean:315:0: error:
  ```
  We get rid of the last part by splitting on the last newline and taking the first part. -/
  match resWithErr.splitOn "\n\n" with
  | [model, _] => model
  | _ => resWithErr


def Lean.MessageLog.getErrorMessages (log : MessageLog) : MessageLog :=
  { unreported := log.unreported.filter fun m => match m.severity with | MessageSeverity.error => true | _ => false }

/-! Deriving `Repr` for functions over finite types. The idea is to first
    curry the function using `finFunctionReprCurry`, and then apply `finFunctionRepr`
    or `essentiallyFinSetRepr`.
-/

instance (priority := high) finFunctionReprCurry (α₁ : Type u) (α₂ : Type v) (β : Type w)
  [Repr α₁] [FinEnum α₁] [Repr α₂] [FinEnum α₂] [Repr β] [inst : Repr (α₁ × α₂ → β)] :
  Repr (α₁ → α₂ → β) where
  reprPrec := fun f n => inst.reprPrec (fun (x, y) => f x y) n

instance (priority := low) finFunctionRepr (α : Type u) (β : Type v) [Repr α] [FinEnum α] [Repr β] :
  Repr (α → β) where
  reprPrec := fun f n =>
    let l := FinEnum.toList α
    let args := l.map (reprPrec · n)
    let res := l.map ((fun x => reprPrec x n) ∘ f)
    args.zip res |>.foldl
      (fun acc (a, b) => acc.append (a ++ " => " ++ b ++ Format.line))
      ("finite_fun : ".toFormat)

instance (priority := high) essentiallyFinSetRepr (α : Type u) [Repr α] [FinEnum α] : Repr (α → Bool) where
  reprPrec := fun f => List.repr (FinEnum.toList α |>.filter f)

open Lean Meta Elab Term Command in
/-- Attempt to derive a `Repr` instance for a `structure` by assuming all
    its parameters are `Repr`s. This can be useful when the structure
    includes functions, which are finite when the type parameters are finite
    but by default Lean cannot derive `Repr` for them.
    Note that this command does not check if any parameter is not a `Type`. -/
elab "simple_deriving_repr_for " t:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  let ConstantInfo.inductInfo info1 ← getConstInfo name | throwError "no such structure {name}"
  let .some info2 := getStructureInfo? (← getEnv) name | throwError "no such structure {name}"
  -- get the names of the parameters from the type
  let numParams := info1.numParams
  let .some (paramNames, _) := Nat.foldM (m := Option) numParams (fun _ _ (res, ty) => do
    let Expr.forallE na _ body _ := ty | failure
    pure (na :: res, body)) ([], info1.type) | throwError "unknown error"
  let paramIdents := paramNames.toArray |>.map mkIdent
  let fields := info2.fieldNames
  let t ← mkIdent <$> mkFreshBinderName
  let n ← mkIdent <$> mkFreshBinderName
  -- create the `instance` definition syntax; for fields, need some tricks?
  let embeddedStringStx x : TSyntax `str :=
    { raw := Lean.Syntax.node Lean.SourceInfo.none `str #[Lean.Syntax.atom Lean.SourceInfo.none ("\"" ++ x ++ " := \"")] }
  let fieldReprs ← fields.mapM (fun fn => do
    -- `State.field t`
    let fieldAccess ← `(term| ($(mkIdent <| name ++ fn) $t))
    `(term| $(mkIdent ``Std.Format.append) $(embeddedStringStx <| toString fn)
      ($(mkIdent ``Repr.reprPrec) $fieldAccess $n)))
  -- for all parameters, assume they are `FinEnum`
  -- NOTE: this might be relaxed later
  let paramInsts : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) ←
    paramIdents.mapM (fun pn => `(bracketedBinder| [$(mkIdent ``Repr) $pn] ))
  let target := Syntax.mkApp (mkIdent name) paramIdents
  -- assemble everything
  let cmd ← `(command|
    instance $[$paramInsts]* : $(mkIdent ``Repr) $target where
      reprPrec $t:ident $n:ident := $(mkIdent ``Std.Format.bracket) "{ "
        ($(mkIdent ``Std.Format.joinSep) [$fieldReprs,*] ", ") " }")
  elabCommand cmd
