import Lean
open Lean Meta Elab Term

namespace Veil.Util

structure AbstractTCArgsConfig where
  allowMVarDependency : Bool := true
  simplifyType : Bool := false
deriving Inhabited

-- TODO This is overlapping with `simplifyMVarType` in `Veil/Util/Meta.lean`
-- except for the delaboration and some further simplification there;
-- consider merging once this is tested to be OK

/-- Simplify the type of the given metavariable `mv`, and abstract it as a new
metavariable with the given `mvname`. Each pair in the returned `Option` contains
the simplified type and the new metavariable expression. -/
def simplifyAndAbstractMVar (mv : Expr)
  (mvname : Name) (keepBodyIf : Expr → TermElabM Bool := fun _ => return true)
  (cfg : AbstractTCArgsConfig := {}) : TermElabM (Option (Expr × Expr)) := do
  let ty ← /- Meta.reduce (skipTypes := false) $ ← -/ Meta.inferType mv
  Meta.forallTelescope ty fun ys body => do
    let body ← whnf body
    if !(← keepBodyIf body) then return none
    let type' ← if cfg.simplifyType then Meta.mkForallFVars ys /- (← Meta.whnf body) -/ body (usedOnly := true) else pure ty
    -- Create a new mvar to replace the old one
    let decl ← mv.mvarId!.getDecl
    let mv' ← Meta.mkFreshExprMVar (.some type') (kind := decl.kind) (userName := mvname)
    -- Assign the old mvar, to get rid of it
    let mv_pf ← do
      -- NOTE: `mkLambdaFVars` can behave unexpectedly when handling mvars
      -- (e.g., automatically applying them to the body); we workaround this
      -- by using a dummy fvar and then doing replacement
      Meta.withLocalDeclD decl.userName type' fun z => do
        let tmp ← if cfg.simplifyType then Meta.mkLambdaFVars ys $ mkAppN z (ys.filter fun y => y.occurs body) else pure z
        pure $ tmp.replaceFVar z mv'
    mv.mvarId!.assign mv_pf
    -- IMPORTANT: the type might have _delayed assignment metavariables_; here
    -- we don't handle this.
    let tyMVars ← Meta.getMVars type'
    unless tyMVars.isEmpty || cfg.allowMVarDependency do
      throwError "(type still has mvars after simplification):\n{type'}"
    return (type', mv')

-- taken from the function introduced in https://github.com/leanprover/lean4/pull/8621
open Meta Grind in
private partial def topsortMVars? (ms : Array Expr) : MetaM (Option (Array Expr)) := do
  let (some _, s) ← go.run.run {} | return none
  return some s.result
where
  go : TopSortM Unit := do
    for m in ms do
      visit m

  visit (m : Expr) : TopSortM Unit := do
    if (← get).permMark.contains m then
      return ()
    if (← get).tempMark.contains m then
      failure
    modify fun s => { s with tempMark := s.tempMark.insert m }
    visitTypeOf m
    modify fun s => { s with
      result := s.result.push m
      permMark := s.permMark.insert m
    }

  visitTypeOf (m : Expr) : TopSortM Unit := do
    let type ← instantiateMVars (← inferType m)
    type.forEach' fun e => do
      if e.hasExprMVar then
        if e.isMVar && ms.contains e then
          visit e
        return true
      else
        return false

-- TODO This is overlapping with `getRequiredDecidableInstances` in `Veil/Util/Meta.lean`
def abstractTCArgsCore (stx : Term)-- (expectedType? : Option Expr)
  (targetTC : Expr → Bool)
  (nameGen : String := "arg")
  (cfg : AbstractTCArgsConfig := {}) : TermElabM (Array (Expr × Expr) × Expr) := do
  /- We want to throw an error if anything fails or is missing during
  elaboration. -/
  Term.withoutErrToSorry $ do
  -- We elaborate the `stx` ignoring typeclass inference failures, but ensuring we
  -- do synthesize all the metavariables that we can (not postponing them). This
  -- is to ensure the resulting expression is 'complete' (i.e. doesn't have holes,
  -- except for the `targetTC` instances, which will be passed explicitly).
  withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) do
  let e ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
  let mvars ← Array.map Expr.mvar <$> Meta.getMVars e
  -- there might be dependencies between the metavariables
  let some mvars ← topsortMVars? mvars | throwError "cyclic dependencies between metavariables detected"
  let mut nameCounter := 0
  let mut nextName := getNextName nameCounter
  let mut res : Array (Expr × Expr) := #[]
  for mv in mvars do
    if let some tmp ← simplifyAndAbstractMVar mv nextName isBodyTarget cfg then
      res := res.push tmp
      nameCounter := nameCounter + 1
      nextName := getNextName nameCounter
  return (res, e)
where
  isBodyTarget (body : Expr) : TermElabM Bool := do
    -- return body.getAppFn'.constName?.elim false targetTC
    return targetTC body.getAppFn'
  getNextName (n : Nat) : Name :=
    .mkSimple <| nameGen ++ toString n

/-- `abstractTCargs% [TC1, TC2, ...] t` collects all missing arguments in `t`
that are instances of any typeclass in `TC1`, `TC2`, ... , and abstracts them
as arguments. The result will be like `fun [arg1 : TC1 ... , argk : TCm] => t`.
If no typeclass list is given, it will abstract all typeclass arguments.

The `TCi` in the list can be either a constant name or a local typeclass
declaration in the local context. -/
syntax (name := abstractTCargsStx) "abstractTCargs% " Parser.Tactic.optConfig ("[" ident,* "]")? term : term

@[term_elab abstractTCargsStx]
def elabAbstractTCargs : TermElab := fun stx _ => do
  match stx with
  | `(abstractTCargs% $[[ $[$tcs:ident],* ]]? $t:term) => do
    let parsedList ← tcs.mapM parseTCList
    let targetTC e := match parsedList with
      | none => true
      | some (constTCNames, targetFVars) =>
        e.constName?.elim (targetFVars.contains e) constTCNames.contains
    let (tmp, e) ← abstractTCArgsCore t targetTC    -- for now just use the default config
    let (_, mvars) := tmp.unzip
    let e ← Meta.mkLambdaFVars mvars e (binderInfoForMVars := BinderInfo.instImplicit) >>= instantiateMVars
    pure e
  | _ => throwUnsupportedSyntax
where
  parseTCList (tcs : Array (TSyntax `ident)) : TermElabM (Array Name × Array Expr) := do
    let mut constTCNames : Array Name := #[]
    let mut targetFVars : Array Expr := #[]
    for i in tcs do
      try
        let n ← resolveGlobalConstNoOverload i
        constTCNames := constTCNames.push n
      catch _ =>
        let ldecl? := (← getLCtx).findFromUserName? i.getId
        match ldecl? with
        | some ldecl =>
          targetFVars := targetFVars.push ldecl.toExpr
        | none =>
          throwError "unknown typeclass or local declaration: {i}"
    return (constTCNames, targetFVars)

end Veil.Util
