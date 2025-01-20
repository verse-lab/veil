import Lean
import Auto
import Smt

/- Not actually used here, but re-exported. -/
import Veil.SMT.Preparation
import Veil.SMT.UniversalQuantifiers
import Veil.SMT.ExistentialQuantifiers
import Veil.SMT.Model

open Lean hiding Command Declaration

initialize
  registerTraceClass `sauto
  registerTraceClass `sauto.query
  registerTraceClass `sauto.result
  registerTraceClass `sauto.model
  registerTraceClass `sauto.debug
  -- the following are primarily for performance profiling
  registerTraceClass `sauto.perf.translate
  registerTraceClass `sauto.perf.query
  registerTraceClass `sauto.perf.checkSat
  registerTraceClass `sauto.perf.getModel
  registerTraceClass `sauto.perf.minimizeModel

open Auto.Solver.SMT in
register_option sauto.smt.solver : SolverName := {
  defValue := SolverName.z3
  descr := "SMT solver to use"
}

register_option sauto.model.minimize : Bool := {
  defValue := false
  descr := "Should models be minimized before being displayed?"
}

inductive Translator
  | leanSmt
  | leanAuto
  deriving BEq, Hashable, Inhabited

instance : ToString Translator where
  toString : Translator → String
  | .leanSmt  => "lean-smt"
  | .leanAuto => "lean-auto"

instance : Lean.KVMap.Value Translator where
  toDataValue n := toString n
  ofDataValue?
  | "lean-smt"  => some .leanSmt
  | "lean-auto" => some .leanAuto
  | _           => none

register_option sauto.smt.translator : Translator := {
  defValue := Translator.leanAuto
  descr := "Which package to use for translating Lean to SMT (`lean-auto` or `lean-smt`)"
}

register_option sauto.smt.macrofinder : Bool := {
  defValue := False
  descr := "Whether to use Z3's macro-finder tactic"
}

inductive CheckSatResult
  | Sat
  | Unsat
  | Unknown (reason : String)
deriving BEq, Inhabited

instance : ToString CheckSatResult where
  toString
    | CheckSatResult.Sat => "sat"
    | CheckSatResult.Unsat => "unsat"
    | CheckSatResult.Unknown r => s!"unknown ({r})"

inductive SmtResult
  | Sat (model : Option FirstOrderStructure)
  | Unsat
  | Unknown (reason : String)
deriving Inhabited

instance : ToString SmtResult where
  toString
    | SmtResult.Sat none => "sat"
    | SmtResult.Sat (some m) => s!"sat\n{m}"
    | SmtResult.Unsat => s!"unsat"
    | SmtResult.Unknown r => s!"unknown ({r})"


namespace Smt
open Elab Tactic Qq

open Smt Smt.Tactic Translate Lean.Meta in
def prepareQuery (mv' : MVarId) (hs : List Expr) : MetaM String := do
  -- HACK: We operate on a cloned goal, and then reset it to the original.
  let mv := (← mkFreshExprMVar (← mv'.getType)).mvarId!
  mv.withContext do
    withTraceNode `sauto.perf.translate (fun _ => return "prepareQuery") do
    withProcessedHints mv hs fun mv hs => mv.withContext do
    let (hs, mv) ← Preprocess.elimIff mv hs
    mv.withContext do
    let goalType : Q(Prop) ← mv.getType
    -- 2. Generate the SMT query.
    let (fvNames₁, _fvNames₂) ← genUniqueFVarNames
    let cmds ← prepareSmtQuery hs goalType fvNames₁
    let cmds := .setLogic "ALL" :: cmds
    let cmdString := s!"{Command.cmdsAsQuery cmds}"
    trace[sauto.debug] "goal:\n{goalType}"
    trace[sauto] "query:\n{cmdString}"
    return cmdString

open Auto Auto.Solver.SMT
def emitCommandStr (p : SolverProc) (c : String) : MetaM Unit := do
  trace[sauto.query] "{c}"
  p.stdin.putStr c
  p.stdin.flush

def emitCommand (p : SolverProc) (c : IR.SMT.Command) : MetaM Unit := do
  emitCommandStr p s!"{c}\n"

def createSolver (name : SolverName) (withTimeout : Nat) : MetaM SolverProc := do
  let tlim_sec := withTimeout
  match name with
  | .none => throwError "createSolver :: Unexpected error"
  -- | .z3   => createAux "z3" #["-in", "-smt2", s!"-T:{tlim}"]
  -- We wrap Z3 with a Python script that prints models in a more usable format.
  | .z3   =>
    let solverPath := (System.mkFilePath [s!"{← IO.currentDir}", "z3model.py"]).toString
    let args := #[s!"--tlimit={tlim_sec * 1000}"]
    createAux solverPath args
  | .cvc4 => throwError "cvc4 is not supported"
  | .cvc5 =>
      let args := #["--lang", "smt", s!"--tlimit={tlim_sec * 1000}",
        "--finite-model-find", "--enum-inst-interleave", "--nl-ext-tplanes", "--produce-models"]
      createAux "cvc5" args
where
  createAux (path : String) (args : Array String) : MetaM SolverProc := do
    trace[sauto.debug] "invoking {path} {args}"
    IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped,
                      cmd := path, args := args}

partial def Handle.readLineSkip (h : IO.FS.Handle) (skipLine : String := "\n") : IO String := do
  let rec loop := do
    let line ← h.getLine
    if line.isEmpty || line == skipLine then
      loop
    else
      return line
  loop

partial def Handle.readUntil (h : IO.FS.Handle) (endString : String) : IO String := do
  let rec loop (s : String) := do
    let line ← h.getLine
    if line.isEmpty then
      return s
    else if line == endString then
      return (s ++ line)
    else
      loop (s ++ line)
  loop ""

def addConstraint (solver : SolverProc) (expr : Expr) : MetaM Unit := do
  -- prepareSmtQuery negates the expression, so we negate it here.
  let (fvNames₁, _fvNames₂) ← genUniqueFVarNames
  let cmds ← prepareSmtQuery [] (mkNot expr) fvNames₁
  -- Do not declare sorts again, etc. Only add constraints (i.e. assertions).
  let cmds := cmds.filter fun
    | .assert _ => true
    | _ => false
  let cmd := Smt.Translate.Command.cmdsAsQuery cmds
  emitCommandStr solver cmd

def checkSat (solver : SolverProc) (solverName : SolverName) : MetaM CheckSatResult := do
  withTraceNode `sauto.perf.checkSat (fun _ => return "checkSat") do
  try
  if sauto.smt.macrofinder.get (← getOptions) && solverName == SolverName.z3 then
    -- only Z3 supports the macro-finder tactic
    emitCommandStr solver "(check-sat-using (then macro-finder smt))\n"
  else
    emitCommand solver .checkSat
  let stdout ←
    -- Our Z3 wrapper works differently from the other solvers
    if solverName == SolverName.z3 then
      Handle.readLineSkip solver.stdout
    else
      solver.stdout.getLine
  let (checkSatResponse, _) ← getSexp stdout
  match checkSatResponse with
  | .atom (.symb "sat") =>
    trace[sauto.debug] "{solverName} says Sat"
    return CheckSatResult.Sat
  | .atom (.symb "unsat") =>
    trace[sauto.debug] "{solverName} says Unsat"
    return CheckSatResult.Unsat
  | e => return CheckSatResult.Unknown s!"{e}"
  catch e =>
    let _exMsg ← e.toMessageData.toString
    throwError s!"check-sat failed (z3model.py likely timed out)"

def getModel (solver : SolverProc) : MetaM Parser.SMTSexp.Sexp := do
  withTraceNode `sauto.perf.getModel (fun _ => return "getModel") do
  try
  emitCommand solver .getModel
  let stdout ← Handle.readUntil solver.stdout ")\n"
  let (model, _) ← getSexp stdout
  return model
  catch e =>
    let _exMsg ← e.toMessageData.toString
    throwError s!"get-model failed (z3model.py likely timed out)"

/-- Check if the constraint is satisfiable in the current frame. -/
def constraintIsSatisfiable (solver : SolverProc) (solverName : SolverName) (constr : Option Expr) : MetaM Bool := do
  match constr with
  | none => return true
  | some expr =>
  addConstraint solver expr
  let res ← checkSat solver solverName
  match res with
  | .Sat => return true
  | .Unsat => return false
  | .Unknown e => throwError s!"Unexpected response from solver: {e}"

private def minimizeModelImpl (solver : SolverProc) (solverName : SolverName) (fostruct : FirstOrderStructure) (kill: Bool := true) : MetaM FirstOrderStructure := do
  -- Implementation follows the `solver.py:_minimal_model()` function in `mypyvy`
  try
  -- Minimize sorts
  let mut sortConstraints : Array (FirstOrderSort × Nat × Expr) := #[]
  for sort in fostruct.domains do
    for sortSize in [1 : sort.size] do
      let .some constraint ← sort.cardinalityConstraint sortSize
        | trace[sauto.debug] "no constraint for sort {sort} at size {sortSize}"; continue
      -- we check each constraint in a separate frame
      emitCommandStr solver s!"(push)"
      let isSat ← constraintIsSatisfiable solver solverName constraint
      match isSat with
      | true =>
          sortConstraints := sortConstraints.push (sort, sortSize, constraint)
          trace[sauto.debug] "minimized sort {sort} to size {sortSize}"
          break -- break out of the `sortSize in [1 : sort.size]` loop
      | false =>
        -- we end the frame here; since this constraint is unsatisfiable,
        -- we don't want to build on top of it
        emitCommandStr solver "(pop)"
        continue
  -- Minimize number of positive elements in each relation interpreted as a finite enumeration
  let mut relConstraints : Array (Declaration × Nat × Expr) := #[]
  for decl in fostruct.signature.declarations do
    -- We try to minimize symbolic interpretations of relations to zero size
    let currentSize ← if fostruct.isInterpretedByFiniteEnumeration decl then fostruct.numTrueInstances decl else pure 1
    trace[sauto.debug] "trying to minimize relation {decl.name} at sizes [0 : {currentSize})"
    for relSize in [0 : currentSize] do
      let .some constraint ← decl.cardinalityConstraint relSize
        | trace[sauto.debug] "no constraint for relation {decl.name} at size {relSize}"; continue
      -- we check each constraint in a separate frame
      emitCommandStr solver "(push)"
      let isSat ← constraintIsSatisfiable solver solverName constraint
      match isSat with
      | true =>
          relConstraints := relConstraints.push (decl, relSize, constraint)
          trace[sauto.debug] "minimized relation {decl.name} to size {relSize}"
          break -- break out of the `relSize in [0 : ← fostruct.numTrueInstances decl]` loop
      | false =>
        -- we end the frame here; since this constraint is unsatisfiable,
        -- we don't want to build on top of it
        emitCommandStr solver "(pop)"
        trace[sauto.debug] "relation {decl.name} is unsatisfiable at size {relSize}"
        continue
  let checkSatResponse ← checkSat solver solverName
  if checkSatResponse != .Sat then
    throwError s!"Minimization failed! (check-sat) returned {checkSatResponse}."
  emitCommand solver .getModel
  -- FIXME: it's probably not OK to kill the solver here
  let (_, solver) ← solver.takeStdin
  let stdout ← solver.stdout.readToEnd
  let stderr ← solver.stderr.readToEnd
  if kill then
    solver.kill
  trace[sauto.debug] "(get-model) {stdout.length}: {stdout}"
  trace[sauto.debug] "(stderr) {stderr}"
  let (model, _) ← getSexp stdout
  trace[sauto.debug] "Model:\n{model}"
  let fostruct ← extractStructure model
  return fostruct
  catch e =>
    let exMsg ← e.toMessageData.toString
    throwError s!"Minimization failed: {exMsg}"

/- FIXME: for whatever reason, if I add `withTraceNode` directly inside `minimizeModelImpl`, it hangs. -/
def minimizeModel (solver : SolverProc) (solverName : SolverName) (fostruct : FirstOrderStructure) (kill : Bool := true): MetaM FirstOrderStructure := do
  withTraceNode `sauto.perf.minimizeModel (fun _ => return "minimizeModel") do
  minimizeModelImpl solver solverName fostruct kill

/-- If the solver returns `Unknown`, we try the other solver. -/
def solverToTryOnUnknown (tried : SolverName) : Option SolverName :=
  match tried with
  | SolverName.z3 => SolverName.cvc5
  | SolverName.cvc5 => SolverName.z3
  | _ => none

partial def getSolverResult (solver: SolverProc) (solverName: SolverName) (kill: Bool := true) (retryOnFailure : Bool := false) (getModel? : Bool := true) (minimize : Bool := false) : MetaM SmtResult := do
  let checkSatResponse ← checkSat solver solverName
  match checkSatResponse with
  | .Sat =>
      trace[sauto.result] "{solverName} says Sat"
      if getModel? then
        let model ← getModel solver
        trace[sauto.debug] "Model:\n{model}"
        -- For Z3, we have model pretty-printing and minimization.
        if solverName == SolverName.z3 then
          let mut fostruct ← extractStructure model
          if minimize then
            fostruct ← minimizeModel solver solverName fostruct (kill := kill)
          trace[sauto.model] "{fostruct}"
          return .Sat fostruct
        -- Non-Z3 solver
        else
          trace[sauto.model] "Currently, we print readable interpretations only for Z3. For other solvers, we only return the raw model."
          trace[sauto.model] "Model:\n{model}"
          if kill then
            solver.kill
          return .Sat .none
      else
        if kill then
            solver.kill
        return .Sat .none
  | .Unsat =>
      trace[sauto.result] "{solverName} says Unsat"
      return .Unsat
  | .Unknown reason =>
      trace[sauto.result] "{solverName} says Unknown ({reason})"
      if retryOnFailure then
        match solverToTryOnUnknown solverName with
        | some s => do
          if kill then
            solver.kill
          trace[sauto.result] "Retrying the query with {s}"
          getSolverResult solver s kill retryOnFailure getModel? minimize
        | none =>
          if kill then
            solver.kill
          return .Unknown reason
      else
        if kill then
          solver.kill
        return .Unknown reason

open Smt Smt.Tactic Translate in
partial def querySolver (goalQuery : String) (withTimeout : Nat) (forceSolver : Option SolverName := none) (retryOnFailure : Bool := false) (getModel? : Bool := true) (minimize : Option Bool := none) : MetaM SmtResult := do
  withTraceNode `sauto.perf.query (fun _ => return "querySolver") do
  try
  let opts ← getOptions
  let minimize := minimize.getD (sauto.model.minimize.get opts)
  let solverName :=
    match forceSolver with
    | some s => s
    | none => sauto.smt.solver.get opts
  trace[sauto.debug] "solver: {solverName}"
  let solver ← createSolver solverName withTimeout
  if solverName == SolverName.cvc5 then
    emitCommand solver (.setLogic "ALL")
    emitCommand solver (.setOption (.produceProofs true))
  emitCommandStr solver goalQuery
  let res ← getSolverResult solver solverName (kill := true) retryOnFailure getModel? minimize
  return res
  catch e =>
    let exMsg ← e.toMessageData.toString
    return .Unknown s!"{exMsg}"

-- /-- Our own version of the `smt` & `auto` tactics. -/
syntax (name := sauto) "sauto" smtHints smtTimeout : tactic

/-- Converts `smtHints` into those understood by `lean-auto`. -/
def parseAutoHints : TSyntax `smtHints → TacticM (TSyntax `Auto.hints)
  | `(smtHints| [ $[$hs],* ]) => `(hints| [$[$hs:term],*])
  | `(smtHints| ) => `(hints| [])
  | _ => throwUnsupportedSyntax

/- We use our own `parseTimeout` because the one in `lean-smt` has a
  hard-coded `5` as default if no timeout is specified. -/
def parseTimeout : TSyntax `smtTimeout → CoreM Nat
  | `(smtTimeout| (timeout := $n)) => return n.getNat
  | `(smtTimeout| ) => return (auto.smt.timeout.get (← getOptions))
  | _ => throwUnsupportedSyntax

open Embedding.Lam Lean.Meta in
/-- Alternative to `prepareQuery`, this invokes `lean-auto` to generate the
  SMT query rather than `lean-smt`. The advantage is this is much faster
  (see
  [ufmg-smite#126](https://github.com/ufmg-smite/lean-smt/issues/126)),
  but produces unreadable queries. -/
def prepareAutoQuery (mv : MVarId) (hints : TSyntax `Auto.hints) : TacticM String := do
  withTraceNode `sauto.perf.translate (fun _ => return "prepareAutoQuery") do
  -- HACK: We operate on a cloned goal, and then reset it to the original.
  let goal := (← mkFreshExprMVar (← mv.getType)).mvarId!
  let (goalBinders, newGoal) ← goal.intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "prepareAutoQuery :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let (lemmas, inhFacts) ← collectAllLemmas hints #[] (goalBinders.push ngoal)
    let query ← getQueryFromAuto lemmas inhFacts
    -- IMPORTANT: Reset the goal to the original
    replaceMainGoal [mv]
    return query
  where
  -- based on `runAuto`
  getQueryFromAuto
    (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM String := do
    -- Simplify `ite`
    let ite_simp_lem ← Lemma.ofConst ``Auto.Bool.ite_simp (.leaf "hw Auto.Bool.ite_simp")
    let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem ite_simp_lem)
    -- Simplify `decide`
    let decide_simp_lem ← Lemma.ofConst ``Auto.Bool.decide_simp (.leaf "hw Auto.Bool.decide_simp")
    let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem decide_simp_lem)
    let afterReify (uvalids : Array UMonoFact) (uinhs : Array UMonoFact) (minds : Array (Array SimpleIndVal)) : LamReif.ReifM String := (do
      let exportFacts ← LamReif.reifFacts uvalids
      let mut exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
      let _ ← LamReif.reifInhabitations uinhs
      let exportInds ← LamReif.reifMutInds minds
      LamReif.printValuation
      -- **Preprocessing in Verified Checker**
      let (exportFacts', exportInds) ← LamReif.preprocess exportFacts exportInds
      exportFacts := exportFacts'
      getAutoQueryString exportFacts exportInds)
    let (cmdString, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM String) do
      let s ← get
      let u ← computeMaxLevel s.facts
      (afterReify s.facts s.inhTys s.inds).run' {u := u})
    return cmdString
  getAutoQueryString (exportFacts : Array REntry) (exportInds : Array MutualIndInfo) : LamReif.ReifM String := do
    let lamVarTy := (← LamReif.getVarVal).map Prod.snd
    let lamEVarTy ← LamReif.getLamEVarTy
    let exportLamTerms ← exportFacts.mapM (fun re => do
      match re with
      | .valid [] t => return t
      | _ => throwError "runAuto :: Unexpected error")
    let sni : SMT.SMTNamingInfo :=
      {tyVal := (← LamReif.getTyVal), varVal := (← LamReif.getVarVal), lamEVarTy := (← LamReif.getLamEVarTy)}
    let ((commands, _validFacts), _state) ← (lamFOL2SMT sni lamVarTy lamEVarTy exportLamTerms exportInds).run
    let queryStr := String.intercalate "\n" (commands.toList.map toString)
    return queryStr

@[tactic sauto] def evalSauto : Tactic := fun stx => withMainContext do
  let mv ← Tactic.getMainGoal
  let withTimeout ← parseTimeout ⟨stx[2]⟩
  -- Due to [ufmg-smite#126](https://github.com/ufmg-smite/lean-smt/issues/126),
  -- we first use `lean-auto` to generate the query, and call `lean-smt` only
  -- if the query is satisfiable and we want to print a model,
  -- UNLESS the `sauto.smt.translator` option overrides this behaviour.
  let translatorToUse := sauto.smt.translator.get (← getOptions)
  let cmdString ←
    match translatorToUse with
    | Translator.leanAuto => prepareAutoQuery mv (← parseAutoHints ⟨stx[1]⟩)
    | Translator.leanSmt => prepareQuery mv (← Tactic.parseHints ⟨stx[1]⟩)
  let getModel? := translatorToUse == Translator.leanSmt
  let res ← querySolver cmdString withTimeout (getModel? := getModel?) (retryOnFailure := true)
  match res with
  -- if we have a model, we can print it
  | .Sat (.some fostruct) => throwError "the goal is false: {fostruct}"
  | .Sat none =>
    -- If we don't, we probably called `lean-auto`, so we need to call
    -- `lean-smt` to get the model.
    if translatorToUse == Translator.leanAuto then
      let hs ← Tactic.parseHints ⟨stx[1]⟩
      let cmdString ← prepareQuery mv hs
      let res ← querySolver cmdString withTimeout
      if let .Sat (.some fostruct) := res then
        throwError "the goal is false: {fostruct}"
      else
        throwError s!"the goal is false, but second SMT query asking for a model returned {res}"
    else
      throwError "the goal is false"
  | .Unknown reason => throwError "the solver returned unknown: {reason}"
  | .Unsat => mv.admit (synthetic := false)

open Lean.Meta in
/-- UNSAFE: Switches the goal with its negation!
    This is unsound unless we use `admit_if_satisfiable` on the resulting goal! -/
elab "negate_goal" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← getMainTarget
  let negatedGoalType ← mkAppM `Not #[goalType]
  let negatedGoal ← mkFreshExprMVar $ negatedGoalType
  goal.admit (synthetic := false)
  setGoals [negatedGoal.mvarId!]

syntax (name := admit_if_satisfiable) "admit_if_satisfiable" smtHints smtTimeout : tactic

open Lean.Meta in
/-- UNSAFE: admits the goal if it is satisfiable.
    This is unsound unless we use `negate_goal` on the goal first!
    MOREOVER, we need to pass in all the hypotheses in the context.
-/
@[tactic admit_if_satisfiable] def evalAdmitIfSat : Tactic := fun stx => withMainContext do
  let mv ← Tactic.getMainGoal
  let hs ← Tactic.parseHints ⟨stx[1]⟩
  let withTimeout ← parseTimeout ⟨stx[2]⟩
  let cmdString ← prepareQuery mv hs
  let res ← querySolver cmdString withTimeout (retryOnFailure := true)
  match res with
  | .Sat _ =>
    trace[sauto.result] "The negation of the goal is satisfiable, hence the goal is valid."
    mv.admit (synthetic := false)
  | .Unsat => throwError "the goal is false"
  | .Unknown reason => throwError "the solver returned unknown: {reason}"


end Smt
