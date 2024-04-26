import Lean
import Lean.Elab.Tactic
import Lean.Meta
import Std.Lean.Meta.UnusedNames

open Lean Meta Elab
-- open Lean Elab Command Term Meta Tactic

initialize registerTraceClass `sts.init

def _root_.Lean.EnvExtension.set [Inhabited σ] (ext : EnvExtension σ) (s : σ) : AttrM Unit := do
  Lean.setEnv $ ext.setState (<- getEnv) s

def _root_.Lean.EnvExtension.modify [Inhabited σ] (ext : EnvExtension σ) (s : σ -> σ) : AttrM Unit := do
  Lean.modifyEnv (ext.modifyState · s)

def _root_.Lean.EnvExtension.get [Inhabited σ] (ext : EnvExtension σ) : AttrM σ := do
  return ext.getState (<- getEnv)

def fresh [Monad m] [Lean.MonadLCtx m] (suggestion : Lean.Name) : m Lean.Syntax.Ident := do
  let name ← getUnusedUserName suggestion
  return Lean.mkIdent name

structure StsState where
  typ : Expr
  init : Expr
  actions : Array Expr
  invariants : Array Expr
  deriving Inhabited

open StsState

initialize stsExt : EnvExtension StsState ←
  registerEnvExtension (pure default)

syntax (name:= state) "state" : attr

initialize registerBuiltinAttribute {
  name := `state
  descr := "Marks as an state type"
  add := fun declName _ _ => do
    let stsTp := (<- stsExt.get).typ
    unless stsTp == default do
      throwError "State type has already been declared: {stsTp}"
    let ty := mkConst declName
    stsExt.modify ({ · with typ := ty })
}

syntax (name:= initial) "initial" : attr

initialize registerBuiltinAttribute {
  name := `initial
  descr := "Marks as an initial state"
  add := fun declName _ _ => MetaM.run' do
    liftCommandElabM $ Command.runTermElabM fun vs => do
      -- Type Checking
      -- let initTp := (<- Lean.getConstInfo declName).type
      -- let initTp <- instantiateForall initTp vs
      -- let stateTp <- instantiateForall (<- stsExt.get).typ vs
      -- let wrongType := throwError "Inital state predicate expected of type {stateTp} -> Prop, but got {initTp} instead"
      -- let some (stateTp', prop) := initTp.arrow?
      --   | wrongType
      -- unless stateTp' == stateTp && prop.isProp do wrongType
      -- Check if the initial state has already been declared
      let intTp := (<- stsExt.get).init
      unless intTp == default do
        throwError "Inital state predicate has already been declared: {intTp}"
      let init := (<- Lean.getConstInfo declName).value!
      stsExt.modify ({ · with init := init })
}
