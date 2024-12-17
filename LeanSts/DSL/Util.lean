import Lean
import LeanSts.DSL.StateExtensions

open Lean Elab Command Term Meta Lean.Parser

/-- Retrieves the current State structure and applies it to
    section variables `vs` -/
def stateTp (vs : Array Expr) : AttrM Expr := do
  let stateTp := (<- localSpecCtx.get).spec.stateType
  unless stateTp != default do throwError "State has not been declared so far"
  return mkAppN stateTp vs

/-- Retrieves the name passed to `#gen_state` -/
def getPrefixedName (name : Name): AttrM Name := do
  let stateName := (← localSpecCtx.get).stateBaseName
  return stateName ++ name

def getStateName : AttrM Name := getPrefixedName `State

def getSectionArgumentsStx (vs : Array Expr) : TermElabM (Array (TSyntax `term)) := do
  let args ← vs.mapM (fun v => do
    let t ← PrettyPrinter.delab v
    let isHygienicName := (extractMacroScopes t.raw.getId).scopes.length > 0
    if isHygienicName then return ← `(term|_) else return t
  )
  return args

/-- A `Lean.Expr` denoting the `Prop` type. -/
def mkProp := (Lean.Expr.sort (Lean.Level.zero))

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
  let stateName ← getStateName
  let casesOn <- mkConst $ (stateName ++ `casesOn)
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
    trace[dsl] e
    let e <- elabTermAndSynthesize e none
    lambdaTelescope e fun _ e => do
        let e <- mkForallFVars vars e
        k vars e

/-- Elaborator with motives. -/
def elabWithMotives :=  (withOptions (·.insert `pp.motives.all true) $ PrettyPrinter.delab ·)

/-- Hack for generating lists of commands. Used by `checkInvariants` -/
declare_syntax_cat commands
syntax (command ppLine ppLine)* : commands
elab_rules : command
  | `(commands| $cmds:command*) => do
    for cmd in cmds do
      elabCommand cmd
def constructCommands (thms : Array (TSyntax `command)) : CoreM (TSyntax `commands) := `(commands| $[$thms]*)

/--
We have three versions of actions: `act.tr`, `act.fn`, and `act.trfn`.
- `act.tr` has existentially quantified arguments (and is thus a
  transition)
- `act.fn` has universally quantified arguments (and is thus a function
  that returns a transition WITH a return value for specific argument
  instances)
- `act.tr.fn` returns `act.tr` instantiated for specific argument
  instances (with NO return value)
 -/
def toTrName (n : Name) : Name := n ++ `tr
/-- See docstring on `toTrName`. -/
def toTrIdent (id : Ident) : Ident := mkIdent $ toTrName id.getId

/-- See docstring on `toTrName`. -/
def toFnName (n : Name) : Name := n ++ `fn
/-- See docstring on `toTrName`. -/
def toFnIdent (id : Ident) : Ident := mkIdent $ toFnName id.getId

def toIOActionDeclName (n : Name) : Name := n ++ `iodecl
def toIOActionDeclIdent (id : Ident) : Ident := mkIdent $ toIOActionDeclName id.getId
