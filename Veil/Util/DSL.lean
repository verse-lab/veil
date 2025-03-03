import Lean
import Veil.Model.State
import Veil.DSL.Internals.StateExtensions
import Veil.DSL.Action.Theory

open Lean Elab Command Term Meta Lean.Parser

def isTypeClassBinder : TSyntax `Lean.Parser.Term.bracketedBinder → Bool
  | `(bracketedBinder| $_:instBinder) => true
  | _ => false

def Term.explicitBinderF := Term.explicitBinder (requireType := false)
def Term.implicitBinderF := Term.implicitBinder (requireType := false)

/-- Transforms explicit binder into implicit one -/
def mkImplicitBinders : TSyntax `Lean.Parser.Term.bracketedBinder ->
  CommandElabM (TSyntax `Lean.Parser.Term.bracketedBinder)
  | `(Term.explicitBinderF| ($id:ident : $tp:term)) => do
    `(Term.bracketedBinderF| {$id:ident : $tp:term})
  | stx => return stx

/-- Returns syntax for the given section arguments. -/
def getSectionArgumentsStx (vs : Array Expr) : TermElabM (Array (TSyntax `term)) := do
  let args ← vs.mapM (fun v => do
    let t ← PrettyPrinter.delab v
    let isHygienicName := (extractMacroScopes t.raw.getId).scopes.length > 0
    if isHygienicName then return ← `(term|_) else return t
  )
  return args

/- We don't pass typeclass arguments (e.g. `[DecidableEq node]`) to the
`State` type, since we want to use `deriving Nonempty` on the
`structure` we create, and it seems it gets confused by them -/
def getStateParametersBinders (vd : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) : Array (TSyntax `Lean.Parser.Term.bracketedBinder) :=
  vd.filter (fun b => !isTypeClassBinder b)

/-- Get the arguments which we have to pass to the `State` type to instantiate it. -/
def getStateArguments [ToMessageData α] (vd : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (vs : Array α) [Monad m] [MonadError m]: m (Array α) := do
  if vd.size != vs.size then throwError "Mismatch in number of arguments between {vd} and {vs}"
  let vs' := (vd.zip vs).filter (fun (b, _) => !isTypeClassBinder b) |> .map Prod.snd
  return vs'

def getStateArgumentsStx (vd : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (vs : Array Expr) : TermElabM (Array (TSyntax `term)) := do
  let vs' ← getStateArguments vd vs
  getSectionArgumentsStx vs'

def getActionParameters : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := return (← getScope).varDecls
def getAssertionParameters : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := getActionParameters
def getImplicitActionParameters : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do (← getActionParameters).mapM mkImplicitBinders

/-- Makes a full application of the `State` type, with the appropriate
section variables/arguments. We don't pass typeclass arguments (e.g.
`[DecidableEq node]`), since we want to use `deriving Nonempty` on the
`structure` we create, and it seems it gets confused by them. -/
def mkStateTpStx (vd : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (vs : Array Expr) : TermElabM Term := do
  let stateTpExpr := (<- localSpecCtx.get).spec.stateType
  unless stateTpExpr != default do throwError "State has not been declared so far"
  let stateTp ← PrettyPrinter.delab stateTpExpr
  let stx ← `(term|@$stateTp $(← getStateArgumentsStx vd vs)*)
  return stx

/-- Retrieve `stateTp` from the local state.-/
def getStateTpStx : AttrM Term := do
  let stateTp := (← localSpecCtx.get).spec.stateStx
  trace[debug] "[getStateTpStx] {stateTp}"
  return stateTp

def getSystemTpStx (vs : Array Expr) : TermElabM Term := do
  let sectionArgs ← getSectionArgumentsStx vs
  `(@$(mkIdent `System) $sectionArgs:term*)

/-- Retrieves the name passed to `#gen_state` -/
def getPrefixedName (name : Name): AttrM Name := do
  let stateName := (← localSpecCtx.get).stateBaseName
  return (stateName.getD Name.anonymous) ++ name

def getStateName : AttrM Name := getPrefixedName `State


/-- A `Lean.Expr` denoting the `Prop` type. -/
def mkProp := (Lean.Expr.sort (Lean.Level.zero))

/-- Modelled after `Lean.Elab.Term.withAutoBoundImplicit`, but customisable. -/
partial def withAutoBoundCont
  (k : TermElabM α)
  (conditionToBind : Name → TermElabM Bool)
  (unboundCont : Exception → Name → TermElabM α)
  : TermElabM α := do
  let flag := autoImplicit.get (← getOptions)
  if flag then
    withReader (fun ctx => { ctx with autoBoundImplicit := flag, autoBoundImplicits := {} }) do
      let rec loop (s : Term.SavedState) : TermElabM α := do
        try
          k
        catch
          | ex => match isAutoBoundImplicitLocalException? ex with
            | some n =>
              if ← conditionToBind n then
              -- Restore state, declare `n`, and try again
                s.restore
                withLocalDecl n .default (← mkFreshTypeMVar) fun x =>
                  withReader (fun ctx => { ctx with autoBoundImplicits := ctx.autoBoundImplicits.push x } ) do
                    loop (← saveState)
              else unboundCont ex n
            | none   => throw ex
      loop (← saveState)
  else
    k

/-- Automatically bound all variables whose names contain only capitals
(and/or digits). -/
partial def withAutoBoundCapitals (k : TermElabM α) : TermElabM α := do
  withAutoBoundCont k (fun n => return isCapital (mkIdent n)) (fun ex n => do throwErrorAt ex.getRef "Unbound uncapitalized variable: {n}")

/-- Throw an exception if `t` refers to any `mutable` state components.
We use this to warn if `assumption`s (axioms) refer to mutable state.-/
def throwIfRefersToMutable (t : Term) : TermElabM Unit :=
  withAutoBoundCont
    (do let _ ← elabTerm t .none)
    -- It's good if it's `immutable` or an all-caps identifier (which is
    -- implicitly `forall` quantified)
    (fun n => do
      let immutable := (← localSpecCtx.get).spec.immutableComponents.map (fun sc => sc.name)
      return immutable.contains n || isCapital (mkIdent n))
    (fun ex n => do
      let mutable := (← localSpecCtx.get).spec.mutableComponents.map (fun sc => sc.name)
      if mutable.contains n then
        throwErrorAt ex.getRef "The assumption refers to mutable state component `{n}`!"
      else
        throwErrorAt ex.getRef "The assumption refers to unbound variable `{n}`!")

/-- This is used wherever we want to define a predicate over a state
    (for instance, in `safety`, `invariant` and `relation`). Instead
    of writing `fun st => Pred` this command will pattern match over
    `st` making all its fields accessible for `Pred`.
    IMPORTANT: You should NOT pass all of `vs`, but only those returned
    by `(← getStateArguments vd vs)`!
    -/
def funcasesM (t : Term) (vs : Array Expr) : TermElabM Term := do
  let stateTpExpr := (<- localSpecCtx.get).spec.stateType
  let .some sn := stateTpExpr.getAppFn.constName?
    | throwError "{stateTpExpr} is not a constant"
  let .some _sinfo := getStructureInfo? (<- getEnv) sn
    | throwError "{stateTpExpr} is not a structure"
  let fns := _sinfo.fieldNames.map Lean.mkIdent
  let moduleName <- getCurrNamespace
  let stateName := `State
  let casesOn <- mkConst $ (moduleName ++ stateName ++ `casesOn)
  let casesOn <- PrettyPrinter.delab casesOn
  let stateTp <- getStateTpStx
  let term ← `(term| (fun $(mkIdent `st) : $stateTp =>
      $(casesOn) $(← getSectionArgumentsStx vs)* (motive := fun _ => Prop) $(mkIdent `st) <| (fun $[$fns]* => ($t : Prop))))
  trace[veil.debug] "funcasesM: {term}"
  return term

def elabBindersAndCapitals
  (br : Array Syntax)
  (vs : Array Expr)
  (e : Syntax)
  (k : Array Expr -> Expr -> TermElabM α)
   : TermElabM α := do
  withAutoBoundCapitals $ Term.elabBinders br fun brs => do
    let vars := (← getLCtx).getFVars.filter (fun x => not $ vs.elem x || brs.elem x)
    trace[veil.debug] "[elabBindersAndCapitals] {e}"
    let e <- elabTermAndSynthesize e none
    lambdaTelescope e fun _ e => do
        let e <- mkForallFVars vars e
        k vars e

/-- Elaborator with motives. -/
def delabWithMotives :=  (withOptions (fun s => (s.insert `pp.motives.all true).insert `pp.funBinderTypes true) $ PrettyPrinter.delab ·)

/-- Hack for generating lists of commands. Used by `checkInvariants` -/
declare_syntax_cat commands
syntax (command ppLine ppLine)* : commands
elab_rules : command
  | `(commands| $cmds:command*) => do
    for cmd in cmds do
      elabCommand cmd
def constructCommands (thms : Array (TSyntax `command)) : CoreM (TSyntax `commands) := `(commands| $[$thms]*)

/--
We have various versions of actions: `act.tr`, `act.fn`, and `act.tr.fn`.
- `act.tr` has existentially quantified arguments (and is thus a
  transition)
- `act.fn` has universally quantified arguments (and is thus a function
  that returns a transition WITH a return value for specific argument
  instances)
- `act.tr.fn` returns `act.tr` instantiated for specific argument
  instances (with NO return value)
- `act.raw` is `act.tr.fn` with only `wlp` unfolded but with no other
  simplifications applied. We use this for debugging purposes.
 -/
def toTrName (n : Name) : Name := n ++ `tr
/-- See docstring on `toTrName`. -/
def toTrIdent (id : Ident) : Ident := mkIdent $ toTrName id.getId

/-- See docstring on `toTrName`. -/
def toFnName (n : Name) : Name := n ++ `fn
/-- See docstring on `toTrName`. -/
def toFnIdent (id : Ident) : Ident := mkIdent $ toFnName id.getId

/-- See docstring on `toTrName`. -/
def toUnsimplifiedName (n : Name) : Name := n ++ `unsimplified
def toUnsimplifiedIdent (id : Ident) : Ident := mkIdent $ toUnsimplifiedName id.getId

def toSpecName (n : Name) : Name := n ++ `spec
def toSpecIdent (id : Ident) : Ident := mkIdent $ toSpecName id.getId

def toGenName (n : Name) (mode : Mode) : Name :=
  n ++ (match mode with
  | Mode.internal => `genI
  | Mode.external => `genE)
def toGenIdent (id : Ident) (mode : Mode): Ident := mkIdent $ toGenName id.getId mode

def toGenInstName (n : Name) (mode : Mode) : Name :=
  n ++ (match mode with
  | Mode.internal => `genIInst
  | Mode.external => `genEInst)
def toGenInstIdent (id : Ident) (mode : Mode) : Ident := mkIdent $ toGenInstName id.getId mode

def toActTrEqName (n : Name) : Name := n ++ `act_tr_eq
def toActTrEqIdent (id : Ident) : Ident := mkIdent $ toActTrEqName id.getId

def toInstName (n : Name) (mode : Mode) : Name :=
  n ++ (match mode with
  | Mode.internal => `inst
  | Mode.external => `instExt)
def toInstIdent (id : Ident) (mode : Mode) : Ident := mkIdent $ toInstName id.getId mode

def toExtName (n : Name) : Name := n ++ `ext
def toExtIdent (id : Ident) : Ident := mkIdent $ toExtName id.getId

def toIOActionDeclName (n : Name) : Name := n ++ `iodecl
def toIOActionDeclIdent (id : Ident) : Ident := mkIdent $ toIOActionDeclName id.getId

/-- The DSL sometimes generates names including `.tr`, and we can't
print these to SMT. -/
def mkPrintableName (n : Name) : Name :=
  Name.mkSimple $ "_".intercalate (n.components.map toString)

def List.removeDuplicates [BEq α] (xs : List α) : List α :=
  xs.foldl (init := []) fun acc x =>
    if acc.contains x then acc else x :: acc

def Lean.TSyntax.isApp? (stx : Term) : Option (Ident × Array Term) := do
  let #[f, args] := stx.raw.getArgs | failure
  let `(term| $f:ident) := f | failure
  return (⟨f⟩, args.getArgs.map (⟨·⟩))

def simpleAddThm (n : Name) (tp : Expr) (tac : TermElabM (TSyntax `Lean.Parser.Tactic.tacticSeq))
  (attr : Array Attribute := #[]) : TermElabM Unit := do
  addDecl <|
    Declaration.thmDecl <|
      mkTheoremValEx n [] tp (<- elabTermAndSynthesize (<- `(by $(<- tac))) tp) []
  applyAttributes n attr

macro "exists?" br:explicitBinders ? "," t:term : term =>
  match br with
  | some br => `(exists $br, $t)
  | none => `($t)

macro "forall?" br:bracketedBinder* "," t:term : term =>
  if br.size > 0 then
    `(∀ $br*, $t)
  else
    `($t)
