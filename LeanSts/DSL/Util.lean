import Lean
import Lean.Elab.Tactic
import Lean.Meta
import Lean.Parser
import LeanSts.State
import Batteries.Lean.Meta.UnusedNames

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
  /-- name of the system; set when `#gen_spec` runs -/
  name: Name
  /-- type of the transition system state -/
  typ        : Expr
  /-- signatures of all constants, relations, and functions -/
  sig    : Array (TSyntax `Lean.Parser.Command.structSimpleBinder)
  /-- initial state predicate -/
  init       : Expr
  /-- list of transitions -/
  actions    : List Expr
  /-- safety properties -/
  safeties     : List Expr
  /-- list of invariants -/
  invariants : List Expr
  /-- established invariant clauses; set on `@[invProof]` label -/
  establishedClauses : List Name := []
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
    stsExt.modify (fun s => { s with actions := s.actions ++ [mkConst declName]})
}

syntax (name:= safe) "safeDef" : attr

initialize registerBuiltinAttribute {
  name := `safe
  descr := "Marks as a safety property"
  add := fun declName _ _ => do
    stsExt.modify (fun s => { s with safeties := s.safeties ++ [mkConst declName]})
}


syntax (name:= inv) "invDef" : attr

initialize registerBuiltinAttribute {
  name := `inv
  descr := "Marks as an invariant clause"
  add := fun declName _ _ => do
    stsExt.modify (fun s => { s with invariants := s.invariants ++ [mkConst declName]})
}

register_simp_attr invSimp
register_simp_attr actSimp
register_simp_attr initSimp
register_simp_attr safeSimp

/-- For `solve_by_elim` -/
-- register_label_attr invProof
syntax (name := invProof) "invProof" : attr

initialize registerBuiltinAttribute {
  name := `invProof
  descr := "Marks this theorem as the proof of an invariant clause"
  add := fun declName _ _ => do
    stsExt.modify (fun s => { s with establishedClauses := s.establishedClauses ++ [declName]})
}

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


open Lean Elab Command Term Meta Lean.Parser

def prop := (Lean.Expr.sort (Lean.Level.zero))

def Term.explicitBinderF := Term.explicitBinder (requireType := false)
def Term.implicitBinderF := Term.implicitBinder (requireType := false)

/-- Transforms explicit binder into implicit one -/
def mkImplicitBinders : TSyntax `Lean.Parser.Term.bracketedBinder ->
  CommandElabM (TSyntax `Lean.Parser.Term.bracketedBinder)
  | `(Term.explicitBinderF| ($id:ident : $tp:term)) => do
    `(Term.bracketedBinderF| {$id:ident : $tp:term})
  | stx => return stx

partial def withAutoBoundExplicit (k : TermElabM α) : TermElabM α := do
  let flag := autoImplicit.get (← getOptions)
  if flag then
    withReader (fun ctx => { ctx with autoBoundImplicit := flag, autoBoundImplicits := {} }) do
      let rec loop (s : Term.SavedState) : TermElabM α := do
        try
          k
        catch
          | ex => match isAutoBoundImplicitLocalException? ex with
            | some n =>
              if isCapital (Lean.mkIdent n) then
              -- Restore state, declare `n`, and try again
                s.restore
                withLocalDecl n .default (← mkFreshTypeMVar) fun x =>
                  withReader (fun ctx => { ctx with autoBoundImplicits := ctx.autoBoundImplicits.push x } ) do
                    loop (← saveState)
              else throwErrorAt ex.getRef "Unbound uncapitalized variable: {n}"
            | none   => throw ex
      loop (← saveState)
  else
    k

/-- This is used wherener we want to define a predicate over a state
    (for intstance, in `safety`, `invatiant` and `relation`). Instead
    of writing `fun st => Pred` this command will pattern match over
    `st` making all its fileds accessible for `Pred` -/
def funcasesM (t : Term) (vs : Array Expr) : TermElabM Term := do
  let stateTp <- stateTp vs
  let .some sn := stateTp.getAppFn.constName?
    | throwError "{stateTp} is not a constant"
  let .some _sinfo := getStructureInfo? (<- getEnv) sn
    | throwError "{stateTp} is not a structure"
  let fns := _sinfo.fieldNames.map Lean.mkIdent
  let casesOn <- mkConst $ "State.casesOn".toName
  let casesOn <- PrettyPrinter.delab casesOn
  let stateTp <- PrettyPrinter.delab stateTp
  `(term| (fun $(mkIdent `st) : $stateTp =>
      $(casesOn) (motive := fun _ => Prop) $(mkIdent `st) <| (fun $[$fns]* => ($t : Prop))))


def elabBindersAndCapitals
  (br : Array Syntax)
  (vs : Array Expr)
  (e : Syntax)
  (k : Array Expr -> Expr -> TermElabM α)
   : TermElabM α := do
  withAutoBoundExplicit $ Term.elabBinders br fun brs => do
    let vars := (← getLCtx).getFVars.filter (fun x => not $ vs.elem x || brs.elem x)
    trace[sts] e
    let e <- elabTermAndSynthesize e none
    lambdaTelescope e fun _ e => do
        let e <- mkForallFVars vars e
        k vars e

def my_delab :=  (withOptions (·.insert `pp.motives.all true) $ PrettyPrinter.delab ·)

/-- Create the syntax for something like `type1 → type2 → .. → typeN`, ending with `terminator`. -/
def mkArrowStx (tps : List Ident) (terminator : Option $ TSyntax `term := none) : CommandElabM (TSyntax `term) := do
  match tps with
  | [] => if let some t := terminator then return t else throwError "empty list of types and no terminator"
  | [a] => match terminator with
    | none => `(term| $a)
    | some t => `(term| $a -> $t)
  | a :: as =>
    let cont ← mkArrowStx as terminator
    `(term| $a -> $cont)

/-- Hack for generating lists of commands. Used by `checkInvariants` -/
declare_syntax_cat commands
syntax (command ppLine ppLine)* : commands
elab_rules : command
  | `(commands| $cmds:command*) => do
    for cmd in cmds do
      elabCommand cmd
def constructCommands (thms : Array (TSyntax `command)) : CoreM (TSyntax `commands) := `(commands| $[$thms]*)
