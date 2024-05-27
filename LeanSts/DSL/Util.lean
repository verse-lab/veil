import Lean
import Lean.Elab.Tactic
import Lean.Meta
import Lean.Parser
import Std.Lean.Meta.UnusedNames

open Lean Meta Elab Lean.Parser
-- open Lean Elab Command Term Meta Tactic

initialize registerTraceClass `sts

def _root_.Lean.EnvExtension.set [Inhabited σ] (ext : EnvExtension σ) (s : σ) : AttrM Unit := do
  Lean.setEnv $ ext.setState (<- getEnv) s

def _root_.Lean.EnvExtension.modify [Inhabited σ] (ext : EnvExtension σ) (s : σ -> σ) : AttrM Unit := do
  Lean.modifyEnv (ext.modifyState · s)

def _root_.Lean.EnvExtension.get [Inhabited σ] (ext : EnvExtension σ) : AttrM σ := do
  return ext.getState (<- getEnv)

def freshIdentifier (suggestion : String) : CoreM Lean.Syntax.Ident := do
  let name ← mkFreshUserName (Name.mkSimple suggestion)
  return Lean.mkIdent name

/-- Auxiliary structure to store the transition system objects -/
structure StsState where
  /-- type of the transition system state -/
  typ        : Expr
  /-- signatures of all relations -/
  rel_sig    : Array (TSyntax `Lean.Parser.Command.structSimpleBinder)
  /-- initial state predicate -/
  init       : Expr
  /-- list of transitions -/
  actions    : List Expr
  /-- safety properties -/
  safeties     : List Expr
  /-- list of invariants -/
  invariants : List Expr
  /-- number of declared traces -/
  numTraces : Nat := 0
  deriving Inhabited

open StsState

initialize stsExt : EnvExtension StsState ←
  registerEnvExtension (pure default)

syntax (name:= state) "stateDef" : attr

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

syntax (name:= initial) "initDef" : attr

initialize registerBuiltinAttribute {
  name := `initial
  descr := "Marks as an initial state"
  add := fun declName _ _ => do
    -- Check if the initial state has already been declared
    let intTp := (<- stsExt.get).init
    unless intTp == default do
      throwError "Inital state predicate has already been declared"
    let init := mkConst declName
    stsExt.modify ({ · with init := init })
}

syntax (name:= action) "actDef" : attr

initialize registerBuiltinAttribute {
  name := `action
  descr := "Marks as a state stransition"
  add := fun declName _ _ => do
    stsExt.modify (fun s => { s with actions := mkConst declName :: s.actions})
}

syntax (name:= safe) "safeDef" : attr

initialize registerBuiltinAttribute {
  name := `safe
  descr := "Marks as a safety property"
  add := fun declName _ _ => do
    stsExt.modify (fun s => { s with safeties := mkConst declName :: s.safeties})
}


syntax (name:= inv) "invDef" : attr

initialize registerBuiltinAttribute {
  name := `inv
  descr := "Marks as an invariant clause"
  add := fun declName _ _ => do
    stsExt.modify (fun s => { s with invariants := mkConst declName :: s.invariants})
}

register_simp_attr invSimp
register_simp_attr actSimp
register_simp_attr initSimp
register_simp_attr safeSimp

/-- This is used in `require` were we define a predicate over a state.
    Instead of writing `fun st => Pred` this command will pattern match over
    `st` making all its fileds accessible for `Pred` -/
macro "funcases" t:term : term => `(term| by intros st; unhygienic cases st; exact $t)

/-- This is used wherener we want to define a predicate over a state
    which should not depend on the state (for instance in `after_init`). -/
macro "funclear" t:term : term => `(term| by intros st; clear st; exact $t)

/-- Retrieves the current `State` structure and applies it to
    section variables `vs` -/
def stateTp (vs : Array Expr) : MetaM Expr := do
  let stateTp := (<- stsExt.get).typ
  unless stateTp != default do throwError "State has not been declared so far"
  return mkAppN stateTp vs
