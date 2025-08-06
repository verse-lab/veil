import Lean
import Veil.DSL.Internals.StateExtensions
import Veil.Theory.WP

open Lean Elab Command Term Meta Lean.Parser

-- Tuple syntax and function update syntax (moved from Model/State.lean)
declare_syntax_cat tupl
syntax term "[" (term),* " ↦ " term "]" : term
syntax (term:max)* : tupl
syntax (name := tupl) "[tupl|" tupl "]" : term

@[term_elab tupl]
def tuplElab : TermElab := fun stx type? => do
  match stx with
  | `(term| [tupl| $arg: term $args: term *]) =>
    let newStx ← if args.size == 0 then `($arg) else `(($arg, [tupl| $args: term *]))
    elabTerm newStx type?
  | _ => throwUnsupportedSyntax

def isCapital (i : Lean.Syntax) : Bool :=
  i.getId.isStr && i.getId.toString.all (fun c => c.isUpper || c.isDigit)

macro_rules
  | `(term| $f[$is:term,* ↦ $b ]) => do
    let mut x : Array $ Lean.TSyntax `ident := #[]
    for i in is.getElems do
      if isCapital i && x.all (· != ⟨i.raw⟩) then
        x := x.push ⟨i.raw⟩
      else
        x := x.push (<- Lean.Elab.Term.mkFreshIdent i)
    let tuple1 <- `(term| [tupl| $is: term *])
    let tuple2 <- `(term| [tupl| $[$x: ident] * ] )
    let stx <- `(fun $[$x:ident]* => if $tuple2 = $tuple1 then $b else $f:term $x *)
    -- dbg_trace toString stx
    return stx

def isTypeClassBinder : TSyntax `Lean.Parser.Term.bracketedBinder → Bool
  | `(bracketedBinder| $_:instBinder) => true
  | _ => false

def Term.explicitBinderF := Term.explicitBinder (requireType := false)
def Term.implicitBinderF := Term.implicitBinder (requireType := false)

/-- Transforms explicit binder into implicit one -/
def mkImplicitBinders [Monad m] [MonadQuotation m] : TSyntax `Lean.Parser.Term.bracketedBinder ->
  m (TSyntax `Lean.Parser.Term.bracketedBinder)
  | `(Term.explicitBinderF| ($id:ident : $tp:term)) => do
    `(Term.bracketedBinderF| {$id:ident : $tp:term})
  | stx => return stx

/-- Construct the fully-applied `stateTp` from the local state. -/
def getStateTpStx [Monad m] [MonadEnv m] [MonadQuotation m] : m Term := do
  let spec := (← localSpecCtx.get).spec
  let stateTpStx ← spec.generic.stateTpStx
  return stateTpStx

/-- Construct the fully-applied `stateTp` from the local state. -/
def getReaderTpStx [Monad m] [MonadEnv m] [MonadQuotation m] : m Term := do
  let spec := (← localSpecCtx.get).spec
  let readerTpStx ← spec.generic.readerTpStx
  return readerTpStx

def getStateTpArgsStx [Monad m] [MonadEnv m] [MonadQuotation m] : m (Array Term) := do
  let spec := (← localSpecCtx.get).spec
  let args := spec.generic.stateArguments
  return args

def getReaderTpArgsStx [Monad m] [MonadEnv m] [MonadQuotation m] : m (Array Term) := do
  let spec := (← localSpecCtx.get).spec
  let args := spec.generic.readerArguments
  return args

def getActionParameters : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := return (← getScope).varDecls
def getImplicitProcedureParameters : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do (← getActionParameters).mapM mkImplicitBinders

/-- Returns syntax for the given section arguments (`Expr`s). -/
def getSectionArgumentsStx (vs : Array Expr) : TermElabM (Array (TSyntax `term)) := do
  let args ← vs.mapM (fun v => do
    let t ← PrettyPrinter.delab v
    let isHygienicName := (extractMacroScopes t.raw.getId).scopes.length > 0
    if isHygienicName then return ← `(term|_) else return t
  )
  return args

def getSectionArgumentsStxWithConcreteState (vs : Array Expr) : TermElabM (Array (TSyntax `term)) := do
  let args ← getSectionArgumentsStx vs
  let spec := (← localSpecCtx.get).spec
  let stateTp ← getStateTpStx
  let readerTp ← getReaderTpStx
  let substateInst ← `(term|_) -- infer the instance from the context
  let subreaderInst ← `(term|_) -- infer the instance from the context
  let concreteArgs ← spec.generic.applyWithConcreteState args stateTp readerTp substateInst subreaderInst
  trace[veil.debug] "args: {args} => concreteArgs: {concreteArgs}"
  return concreteArgs

/-- Used to get the existentials in `trace` queries. -/
def getNonGenericStateParameters : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let vd := (← getScope).varDecls
  let spec := (← localSpecCtx.get).spec
  spec.generic.applyGetNonGenericStateAndReaderArguments vd

def getNonGenericStateAndReaderArguments (vs : Array α) : TermElabM (Array α) := do
  let spec := (← localSpecCtx.get).spec
  spec.generic.applyGetNonGenericStateAndReaderArguments vs

def getSystemParameters : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := getActionParameters
def getAssertionParameters : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := getActionParameters
/-- Assumptions don't depend on the state. -/
def getAssumptionParameters : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let vd := (← getScope).varDecls
  let spec := (← localSpecCtx.get).spec
  spec.generic.applyGetNonGenericStateArguments vd

def getAssumptionArguments (vs : Array Expr) : TermElabM (Array Expr) := do
  let spec := (← localSpecCtx.get).spec
  spec.generic.applyGetNonGenericStateArguments vs

def getSystemTpStx (vs : Array Expr) : TermElabM Term := do
  let systemArgs ← getSectionArgumentsStx vs
  `(@$(mkIdent `System) $systemArgs:term*)

def getConcreteSystemTpStx (vs : Array Expr) : TermElabM Term := do
  let systemArgs ← getSectionArgumentsStxWithConcreteState vs
  `(@$(mkIdent `System) $systemArgs:term*)

/-- Retrieves the name passed to `#gen_state` -/
def getPrefixedName (name : Name): AttrM Name := do
  let stateName := (← localSpecCtx.get).stateBaseName
  return (stateName.getD Name.anonymous) ++ name

def getStateName : AttrM Name := getPrefixedName `State
def getReaderName : AttrM Name := getPrefixedName `Reader

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
    `st` making all its fields accessible for `Pred`. -/
def funcasesM (t : Term) : TermElabM Term := do
  let stateTpExpr := (<- localSpecCtx.get).spec.generic.stateType
  let .some sn := stateTpExpr.getAppFn.constName?
    | throwError "{stateTpExpr} is not a constant"
  let .some _sinfo := getStructureInfo? (<- getEnv) sn
    | throwError "{stateTpExpr} is not a structure"
  let stateFns := _sinfo.fieldNames.map Lean.mkIdent

  let readerTpExpr := (<- localSpecCtx.get).spec.generic.readerType
  let .some sn := readerTpExpr.getAppFn.constName?
    | throwError "{readerTpExpr} is not a constant"
  let .some _rinfo := getStructureInfo? (<- getEnv) sn
    | throwError "{readerTpExpr} is not a structure"
  let readerFns := _rinfo.fieldNames.map Lean.mkIdent

  let moduleName <- getCurrNamespace
  let stateName := `State
  let readerName := `Reader
  let casesOn <- mkConst $ (moduleName ++ stateName ++ `casesOn)
  let casesOnReader <- mkConst $ (moduleName ++ readerName ++ `casesOn)
  let casesOn <- PrettyPrinter.delab casesOn
  let casesOnReader <- PrettyPrinter.delab casesOnReader
  let stateTpStx ← getStateTpStx
  let readerTpStx ← getReaderTpStx
  let stateTpArgs ← getStateTpArgsStx
  let readerTpArgs ← getReaderTpArgsStx
  let st := mkIdent `st
  let rd := mkIdent `rd
  let term ← `(term| (fun ($rd : $readerTpStx) ($st : $stateTpStx) =>
      $(casesOnReader)
      $(readerTpArgs)*
      (motive := fun _ => Prop) (readFrom $rd) <|
        fun $[$readerFns]* =>
          $(casesOn)
          $(stateTpArgs)*
          (motive := fun _ => Prop) (getFrom $st) <|
          fun $[$stateFns]* => ($t : Prop)))
  trace[veil.debug] "funcasesM: {term}"
  return term

/-- Like `funcasesM`, but only destruct the reader (immutable) state. -/
def funcasesReader (t : Term) : TermElabM Term := do
  let readerTpExpr := (<- localSpecCtx.get).spec.generic.readerType
  let .some sn := readerTpExpr.getAppFn.constName?
    | throwError "{readerTpExpr} is not a constant"
  let .some _rinfo := getStructureInfo? (<- getEnv) sn
    | throwError "{readerTpExpr} is not a structure"
  let readerFns := _rinfo.fieldNames.map Lean.mkIdent

  let moduleName <- getCurrNamespace
  let readerName := `Reader
  let casesOnReader <- mkConst $ (moduleName ++ readerName ++ `casesOn)
  let casesOnReader <- PrettyPrinter.delab casesOnReader
  let readerTpStx ← getReaderTpStx
  let readerTpArgs ← getReaderTpArgsStx
  let rd := mkIdent `rd
  let term ← `(term| (fun ($rd : $readerTpStx) =>
      $(casesOnReader)
      $(readerTpArgs)*
      (motive := fun _ => Prop) (readFrom $rd) <|
        fun $[$readerFns]* => ($t : Prop)))
  trace[veil.debug] "funcasesReader: {term}"
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
def delabWithMotives := (withOptions (fun s => ((s.insert `pp.motives.all true).insert `pp.funBinderTypes true).insert `pp.structureInstanceTypes true) $ PrettyPrinter.delab ·)
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
- `act.raw` is `act.tr.fn` with only `wp` unfolded but with no other
  simplifications applied. We use this for debugging purposes.
 -/
def toTrName (n : Name) : Name := n ++ `tr
/-- See docstring on `toTrName`. -/
def toTrIdent (id : Ident) : Ident := mkIdent $ toTrName id.getId
def toTrLemmaName (n : Name) : Name := n ++ `tr_eq


def toOriginalName (n : Name) : Name := n ++ `original
def toOriginalIdent (id : Ident) : Ident := mkIdent $ toOriginalName id.getId

def toSpecName (n : Name) : Name := n ++ `spec
def toSpecIdent (id : Ident) : Ident := mkIdent $ toSpecName id.getId

def toExtName (n : Name) : Name := n ++ `ext
def toExtIdent (id : Ident) : Ident := mkIdent $ toExtName id.getId

def toActName (n : Name) (mode : Mode) : Name :=
  match mode with
  | Mode.internal => n
  | Mode.external => toExtName n

def toActIdent (id : Ident) (mode : Mode) : Ident := mkIdent $ toActName id.getId mode

def toWpName (n : Name) : Name := n ++ `wpGen
def toWpLemmaName (n : Name) : Name := n ++ `wp_eq
def toWpSuccName (n : Name) : Name := n ++ `wpSucc
def toWpSuccLemmaName (n : Name) : Name := n ++ `wpSucc_eq
def toWpExName (n : Name) : Name := n ++ `wpEx
def toWpExLemmaName (n : Name) : Name := n ++ `wpEx_eq
def toTwoStateName (n : Name) : Name := n ++ `twoState
def toTwoStateLemmaName (n : Name) : Name := n ++ `twoState_eq_wpSucc
def toEndToEndLemmaName (n : Name) : Name := n ++ `twoState_eq


def toIOActionDeclName (n : Name) : Name := n ++ `iodecl
def toIOActionDeclIdent (id : Ident) : Ident := mkIdent $ toIOActionDeclName id.getId

def initialStateName : Name := `initialState?
def initializerName : Name := `initializer

def stateSimpHypName : Name := `hStateSimp
/-- Name of the generic state variable. -/
def genericStateName : Name := `σ
/-- The generic state variable. -/
def genericState : Ident := mkIdent genericStateName

def assumptionsName : Name := `Assumptions
def assumptionsIdent : Ident := mkIdent assumptionsName

def invInductiveName : Name := `inv_inductive
def invInductiveIdent : Ident := mkIdent invInductiveName

def propInvariantName (p : Name) : Name := Name.mkSimple s!"{p}_invariant"

/-- Name of the generic reader variable. -/
def genericReaderName : Name := `ρ
/-- The generic reader variable. -/
def genericReader : Ident := mkIdent genericReaderName

def subStateInstIdent (id : Ident): Ident := mkIdent $ Name.mkSimple s!"{id.getId}_substate"
def subStateInstIdent' (base : Ident) (other : Ident): Ident := mkIdent $ Name.mkSimple s!"{base.getId}_substate_{other.getId}"
def genericSubStateIdent : Ident := subStateInstIdent genericState

def subReaderInstIdent (id : Ident): Ident := mkIdent $ Name.mkSimple s!"{id.getId}_reader"
def subReaderInstIdent' (base : Ident) (other : Ident): Ident := mkIdent $ Name.mkSimple s!"{base.getId}_reader_{other.getId}"
def genericSubReaderIdent : Ident := subReaderInstIdent genericReader

def labelName : Name := `Label
def labelIdent : Ident := mkIdent labelName

def labelCasesName : Name := `Label_cases
def labelCasesIdent : Ident := mkIdent labelCasesName

/-- The DSL sometimes generates names including `.tr`, and we can't
print these to SMT. -/
def mkPrintableName (n : Name) : Name :=
  Name.mkSimple $ "_".intercalate (n.components.map toString)

def mkNameFromComponents (comp : List Name) : Name :=
  s!"{mkString comp}".toName
where
  mkString (xs : List Name) : String :=
    xs.map toString |> String.intercalate "."

private def veilSuffixes : Std.HashSet Name := Std.HashSet.ofList [`tr, `tr_eq, `original, `spec, `ext, `wpGen, `wp_eq, `wpSucc, `wpSucc_eq, `wpEx, `wpEx_eq, `twoState, `twoState_eq_wpSucc, `twoState_eq, `iodecl]
private partial def dropSuffixes' (components : List Name) : List Name :=
    if components.length > 1 && veilSuffixes.contains components.getLast! then
      dropSuffixes' components.dropLast
    else
      components
/-- Drops all the Veil-specific suffixes from the name. -/
def dropSuffixes (n : Name) : Name :=
  mkNameFromComponents (dropSuffixes' n.components)

/-- Returns the name stripped of all the Veil-specific suffixes and of
the module/specification name, if any. -/
def normalizeName [Monad m] [MonadError m] (n : Name) (inSpec : Name) : m Name := do
  let n' := dropSuffixes n
  match n'.components with
  | [nm] => pure nm
  | [mod, nm] =>
     if mod != inSpec then
       throwError "normalized name {n'} with two components should have the first component be the specification name: {mod}"
     pure nm
  | _ => throwError "normalized name should only have one component: {n'}"

def retrieveProcedureSpecification [Monad m] [MonadEnv m] [MonadError m] (n : Name) : m (Option ProcedureSpecification) := do
  let n' := dropSuffixes n
  match n'.components with
  | [nm] =>
    let ctx := (← localSpecCtx.get)
    return ctx.spec.procedures.find? (·.name == nm)
  | [mod, nm] =>
     let .some ctx := (← globalSpecCtx.get).get? mod
       | throwError "specification {mod} not found in the global environment when trying to retrieve procedure {n}"
     return ctx.spec.procedures.find? (·.name == nm)
  | _ => throwError "normalized name should only have one component: {n'}"

/-- Primes the first component of the name. -/
def mkPrimed (f : Name) : Name :=
  let comp := f.components
  let primeComp (n : Name) : Name := Name.mkSimple (n.toString ++ "'")
  match comp with
  | [nm] => primeComp nm
  | fst :: rest => mkNameFromComponents (primeComp fst :: rest)
  | [] => unreachable!

/-- Like `mkPrintableName`, but strips the first component of the name. -/
def mkStrippedName (n : Name) (separator : String := "_") : Name :=
  s!"{mkString n.components}".toName
where
  stripFirst {α : Type} (xs : List α) : List α :=
    match xs with
    | [] => []
    | [x] => [x]
    | _ :: xs => xs
  mkString (xs : List Name) : String :=
    xs.map toString |> stripFirst |> String.intercalate separator

def mkTheoremName (actName : Name) (invName : Name) : Name := s!"{mkStrippedName actName}_{mkStrippedName invName}".toName
def mkTrTheoremName (actName : Name) (invName : Name) : Name :=
  if actName == initializerName then
    s!"{actName}_tr_{mkStrippedName invName}".toName
  else mkTheoremName (toTrName actName) invName

def mkConcreteStateNameFromAbstract (n : Name) : Name := match n with
  | `r₀ => `r₀
  | `s₀ => `st
  | `s₁ => `st'
  | _ => n

def stripFirstComponent (n : Name) : Name := mkStrippedName n "."

def List.removeDuplicates [BEq α] (xs : List α) : List α :=
  xs.foldl (init := []) fun acc x =>
    if acc.contains x then acc else x :: acc

def Lean.TSyntax.isApp? (stx : Term) : Option (Ident × Array Term) := do
  let #[f, args] := stx.raw.getArgs | failure
  let `(term| $f:ident) := f | failure
  return (⟨f⟩, args.getArgs.map (⟨·⟩))

/-- Add a single theorem to the environment by providing its name, type and proof. -/
def simpleAddTheorem (name : Name) (lvlParams : List Name) (type value : Expr) (nonComputable? : Bool) : CoreM Unit := do
  let thm := Declaration.thmDecl <| mkTheoremValEx name lvlParams type value []
  if nonComputable? then
    addDecl <| thm
    setEnv <| addNoncomputable (← getEnv) name
  else
    addAndCompile thm

macro "exists?" br:explicitBinders ? "," t:term : term =>
  match br with
  | some br => `(exists $br, $t)
  | none => `($t)

macro "forall?" br:bracketedBinder* "," t:term : term =>
  if br.size > 0 then
    `(∀ $br*, $t)
  else
    `($t)

def Lean.Expr.isBool (e : Expr) : Bool := e.isConstOf `Bool
