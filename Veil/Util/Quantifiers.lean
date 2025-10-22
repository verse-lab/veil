import Lean
import Batteries.Lean.Meta.UnusedNames
import Lean.Util.ForEachExpr

import Veil.Base
import Veil.Util.DSL
import Veil.SMT.Preparation

open Lean Meta Elab Tactic

namespace Veil

private def getDefInfoTemp (info : ConstantInfo) : MetaM (Option ConstantInfo) := do
  match (← getTransparency) with
  | .all => return some info
  | .default => return some info
  | _ =>
    if (← isReducible info.name) then
      return some info
    else
      return none


/-- Remark: we later define `getUnfoldableConst?` at `GetConst.lean` after we define `Instances.lean`.
   This method is only used to implement `isClassQuickConst?`.
   It is very similar to `getUnfoldableConst?`, but it returns none when `TransparencyMode.instances` and
   `constName` is an instance. This difference should be irrelevant for `isClassQuickConst?`. -/
private def getConstTemp? (constName : Name) : MetaM (Option ConstantInfo) := do
  match (← getEnv).find? constName with
  | some (info@(ConstantInfo.thmInfo _))  => getTheoremInfo info
  | some (info@(ConstantInfo.defnInfo _)) => getDefInfoTemp info
  | some info                             => pure (some info)
  | none                                  => throwUnknownConstant constName

private def fvarsSizeLtMaxFVars (fvars : Array Expr) (maxFVars? : Option Nat) : Bool :=
  match maxFVars? with
  | some maxFVars => fvars.size < maxFVars
  | none          => true

private def isClassQuickConst? (constName : Name) : MetaM (LOption Name) := do
  if isClass (← getEnv) constName then
    return .some constName
  else
    match (← getConstTemp? constName) with
    | some (.defnInfo ..) => return .undef -- We may be able to unfold the definition
    | _ => return .none

private partial def isClassQuick? : Expr → MetaM (LOption Name)
  | .bvar ..         => return .none
  | .lit ..          => return .none
  | .fvar ..         => return .none
  | .sort ..         => return .none
  | .lam ..          => return .none
  | .letE ..         => return .undef
  | .proj ..         => return .undef
  | .forallE _ _ b _ => isClassQuick? b
  | .mdata _ e       => isClassQuick? e
  | .const n _       => isClassQuickConst? n
  | .mvar mvarId     => do
    let some val ← getExprMVarAssignment? mvarId | return .none
    isClassQuick? val
  | .app f _         => do
    match f.getAppFn with
    | .const n ..  => isClassQuickConst? n
    | .lam ..      => return .undef
    | .mvar mvarId =>
      let some val ← getExprMVarAssignment? mvarId | return .none
      match val.getAppFn with
      | .const n .. => isClassQuickConst? n
      | _ => return .undef
    | _            => return .none

def isExists (e : Expr) : Bool :=
  match_expr e with
  | Exists _ _ => true
  | _          => false

mutual
  /--
    `withNewLocalInstances isClassExpensive fvars j k` updates the vector or local instances
    using free variables `fvars[j] ... fvars.back`, and execute `k`.

    - `isClassExpensive` is defined later.
    - `isClassExpensive` uses `whnf` which depends (indirectly) on the set of local instances. -/
  private partial def withNewLocalInstancesImp
      (fvars : Array Expr) (i : Nat) (k : MetaM α) : MetaM α := do
    if h : i < fvars.size then
      let fvar := fvars[i]
      let decl ← getFVarLocalDecl fvar
      match (← isClassQuick? decl.type) with
      | .none   => withNewLocalInstancesImp fvars (i+1) k
      | .undef  =>
        match (← isClassExpensive? decl.type) with
        | none   => withNewLocalInstancesImp fvars (i+1) k
        | some c => withNewLocalInstance c fvar <| withNewLocalInstancesImp fvars (i+1) k
      | .some c => withNewLocalInstance c fvar <| withNewLocalInstancesImp fvars (i+1) k
    else
      k

  /--
    `existsTelescopeAuxAux lctx fvars j type`
    Remarks:
    - `lctx` is the `MetaM` local context extended with declarations for `fvars`.
    - `type` is the type we are computing the telescope for. It contains only
      dangling bound variables in the range `[j, fvars.size)`
    - if `reducing? == true` and `type` is not `Exists`, we use `whnf`.
    - when `type` is not a `Exists` nor it can't be reduced to one, we
      execute the continuation `k`.

    Here is an example that demonstrates the `reducing?`.
    Suppose we have
    ```
    abbrev StateM s a := s -> Prod a s
    ```
    Now, assume we are trying to build the telescope for
    ```
    exists (x : Nat), StateM Int Bool
    ```
    if `reducing == true`, the function executes `k #[(x : Nat) (s : Int)] Bool`.
    if `reducing == false`, the function executes `k #[(x : Nat)] (StateM Int Bool)`

    if `maxFVars?` is `some max`, then we interrupt the telescope construction
    when `fvars.size == max`


    If `cleanupAnnotations` is `true`, we apply `Expr.cleanupAnnotations` to each type in the telescope.
  -/
  private partial def existsTelescopeReducingAuxAux
      (reducing          : Bool)
      (type              : Expr)
      (k                 : Array Expr → Expr → MetaM α) (cleanupAnnotations : Bool) : MetaM α := do
    let rec process (lctx : LocalContext) (fvars : Array Expr) (j : Nat) (type : Expr) : MetaM α := do
      match_expr type with
      | Exists _ lamtype =>
        let .lam n d b bi := lamtype | throwError "unexpected exists type {lamtype}"
        let d     := d.instantiateRevRange j fvars.size fvars
        let d     := if cleanupAnnotations then d.cleanupAnnotations else d
        let fvarId ← mkFreshFVarId
        let lctx  := lctx.mkLocalDecl fvarId n d bi
        let fvar  := mkFVar fvarId
        let fvars := fvars.push fvar
        process lctx fvars j b
      | _ =>
        let type := type.instantiateRevRange j fvars.size fvars;
        withLCtx' lctx do
          withNewLocalInstancesImp fvars j do
            if reducing then
              let newType ← whnf type
              if isExists newType then
                process lctx fvars fvars.size newType
              else
                k fvars type
            else
              k fvars type
    process (← getLCtx) #[] 0 type

  private partial def existsTelescopeReducingAux (type : Expr) (k : Array Expr → Expr → MetaM α) (cleanupAnnotations : Bool) : MetaM α := do
      let newType ← whnf type
      if isExists newType then
        existsTelescopeReducingAuxAux true newType k cleanupAnnotations
      else
        k #[] type


  -- Helper method for isClassExpensive?
  private partial def isClassApp? (type : Expr) (instantiated := false) : MetaM (Option Name) := do
    match type.getAppFn with
    | .const c _ =>
      let env ← getEnv
      if isClass env c then
        return some c
      else
        -- Use whnf to make sure abbreviations are unfolded
        match (← whnf type).getAppFn with
        | .const c _ => if isClass env c then return some c else return none
        | _ => return none
    | .mvar .. =>
      if instantiated then return none
      isClassApp? (← instantiateMVars type) true
    | _ => return none

  private partial def isClassExpensive? (type : Expr) : MetaM (Option Name) :=
    withReducible do -- when testing whether a type is a type class, we only unfold reducible constants.
      existsTelescopeReducingAux type (cleanupAnnotations := false) fun _ type => isClassApp? type

  private partial def isClassImp? (type : Expr) : MetaM (Option Name) := do
    match (← isClassQuick? type) with
    | .none   => return none
    | .some c => return (some c)
    | .undef  => isClassExpensive? type

end

variable {n : Type → Type}  [Monad n] [MonadControlT MetaM n] [MonadLiftT MetaM n]

def existsTelescopeReducing (type : Expr) (k : Array Expr → Expr → n α) (cleanupAnnotations := false) : n α :=
  map2MetaM (fun k => existsTelescopeReducingAux type k cleanupAnnotations) k

inductive checkMode where
  | goal
  | hypothesis

def quantMetaTelescopeReducing (e : Expr) (mode : checkMode) (k : Array Expr → Expr → n α) : n α :=
  match mode with
  | .goal => forallTelescopeReducing e k
  | .hypothesis => existsTelescopeReducing e k

inductive QuantType where
  | forall
  | exists

instance : ToString QuantType where
  toString
    | QuantType.forall => "∀"
    | QuantType.exists => "∃"

structure QEState where
  quantifiedTypes : List (QuantType × Name × Expr)
deriving Inhabited

abbrev QuantElimM := StateT QEState n

def isHigherOrder (e : Expr) : MetaM Bool := do
  let t ← inferType e
  let isHO := (!t.isProp) && (e.isArrow || e.isAppOf (← getStateName))
  return isHO

partial def forEachExprSane'
  (input : Expr)
  (fn : Expr → n Bool)
  : n Unit := do
  let _ : STWorld IO.RealWorld n := ⟨⟩
  let _ : MonadLiftT (ST IO.RealWorld) n := { monadLift := fun x => liftM (m := MetaM) (liftM (m := ST IO.RealWorld) x) }
  let rec visit (e : Expr) : MonadCacheT Expr Unit n Unit :=
    checkCache e fun _ => do
      if (← liftM (fn e)) then
        match e with
        | .forallE n d b c  => do visit d; withLocalDecl n c d (fun x => visit $ b.instantiate1 x)
        | .lam n d b c      => do visit d; withLocalDecl n c d (fun x => visit $ b.instantiate1 x)
        | .letE n d v b _   => do visit d; visit v; withLetDecl n d v (fun x => visit $ b.instantiate1 x)
        | .app f a      => visit f; visit a
        | .mdata _ b    => visit b
        | .proj _ _ b   => visit b
        | _             => return ()
  visit input |>.run

/-- Similar to `Expr.forEach`, but creates free variables whenever going inside
of a binder. Unlike `Meta.forEachExpr`, this doesn't use the strange
`visitForall` function which behaves unintuitively. -/
def forEachExprSane (e : Expr) (f : Expr → n Unit) : n Unit :=
  forEachExprSane' e fun e => do
    f e
    return true

end Veil
