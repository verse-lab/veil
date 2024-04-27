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
  typ        : Expr
  rel_sig    : Array (TSyntax `Lean.Parser.Command.structSimpleBinder)
  init       : Expr
  actions    : List Expr
  invariants : List Expr
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
  add := fun declName _ _ => do
    -- Check if the initial state has already been declared
    let intTp := (<- stsExt.get).init
    unless intTp == default do
      throwError "Inital state predicate has already been declared: {intTp}"
    let init := mkConst declName
    stsExt.modify ({ · with init := init })
}

syntax (name:= action) "action" : attr

initialize registerBuiltinAttribute {
  name := `action
  descr := "Marks as a state stransition"
  add := fun declName _ _ => do
    stsExt.modify (fun s => { s with actions := mkConst declName :: s.actions})
}

syntax (name:= inv) "inv" : attr

initialize registerBuiltinAttribute {
  name := `inv
  descr := "Marks as an invariant clause"
  add := fun declName _ _ => do
    stsExt.modify (fun s => { s with invariants := mkConst declName :: s.invariants})
}
