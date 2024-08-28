import Lean
import Auto
import Smt

/- Not actually used here, but re-exported. -/
import LeanSts.SMT.Preparation
import LeanSts.SMT.Model

open Lean hiding Command Declaration

initialize
  registerTraceClass `sauto
  registerTraceClass `sauto.query
  registerTraceClass `sauto.result
  registerTraceClass `sauto.debug

open Auto.Solver.SMT in
register_option sauto.smt.solver : SolverName := {
  defValue := SolverName.z3
  descr := "SMT solver to use"
}

register_option sauto.smt.macrofinder : Bool := {
  defValue := False
  descr := "Whether to use Z3's macro-finder tactic"
}

inductive SmtResult
  | Sat (model : Option FirstOrderStructure)
  | Unsat (unsatCore : Auto.Parser.SMTSexp.Sexp)
  | Unknown

namespace Smt
open Elab Tactic Qq

open Smt Smt.Tactic Translate in
def prepareQuery (mv : MVarId) (hs : List Expr) : MetaM String := mv.withContext do
  let mv ← Util.rewriteIffMeta mv
  let goalType : Q(Prop) ← mv.getType
  -- 1. Process the hints passed to the tactic.
  withProcessedHints mv hs fun mv hs => mv.withContext do
  -- 2. Generate the SMT query.
  let cmds ← prepareSmtQuery hs (← mv.getType)
  let cmdString := s!"{Command.cmdsAsQuery cmds}"
  trace[sauto.debug] "goal:\n{goalType}"
  -- trace[sauto] "query:\n{cmdString}"
  return cmdString

open Auto Auto.Solver.SMT
def emitCommandStr (p : SolverProc) (c : String) : MetaM Unit := do
  trace[sauto.query] "{c}"
  p.stdin.putStr c
  p.stdin.flush

def emitCommand (p : SolverProc) (c : IR.SMT.Command) : MetaM Unit := do
  emitCommandStr p s!"{c}\n"

def createSolver (name : SolverName) (timeout : Option Nat) : MetaM SolverProc := do
  let tlim ← match timeout with
  | none => pure (auto.smt.timeout.get (← getOptions))
  | some t => pure t
  match name with
  | .none => throwError "createSolver :: Unexpected error"
  -- | .z3   => createAux "z3" #["-in", "-smt2", s!"-T:{tlim}"]
  -- We wrap Z3 with a Python script that prints models in a more usable format.
  | .z3   =>
    let solverPath := (System.mkFilePath [s!"{← IO.currentDir}", "z3model.py"]).toString
    trace[sauto.debug] "Z3 wrapper at {solverPath}"
    createAux solverPath #[s!"--tlimit={tlim}"]
  | .cvc4 => throwError "cvc4 is not supported"
  | .cvc5 => createAux "cvc5" #[s!"--tlimit={tlim * 1000}", "--produce-models"]
where
  createAux (path : String) (args : Array String) : MetaM SolverProc :=
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
  let cmds ← prepareSmtQuery [] (mkNot expr)
  -- Do not declare sorts again, etc. Only add constraints (i.e. assertions).
  let cmds := cmds.filter fun
    | .assert _ => true
    | _ => false
  let cmd := Smt.Translate.Command.cmdsAsQuery cmds
  emitCommandStr solver cmd

/-- Try the constraint in a new frame. -/
def constraintIsSatisfiable (solver : SolverProc) (solverName : SolverName) (constr : Option Expr) : MetaM (Option Bool) := do
  match constr with
  | none => return none
  | some expr =>
  -- we check each constraint in a separate frame
  emitCommandStr solver "(push)"
  addConstraint solver expr
  emitCommand solver .checkSat
  let stdout ← Handle.readLineSkip solver.stdout
  let (checkSatResponse, _) ← getSexp stdout
  -- we end the frame here, such that the next iteration of the loop
  -- starts with a clean slate
  emitCommandStr solver "(pop)"
  match checkSatResponse with
  | .atom (.symb "sat") =>
    trace[sauto.debug] "{solverName} says Sat"
    return true
  | .atom (.symb "unsat") =>
    trace[sauto.debug] "{solverName} says Unsat"
    return false
  | e => throwError s!"Unexpected response from solver: {e}"

def minimizeModel (solver : SolverProc) (solverName : SolverName) (fostruct : FirstOrderStructure) : MetaM FirstOrderStructure := do
  -- Implementation follows the `solver.py:_minimal_model()` function in `mypyvy`
  -- Minimize sorts
  let mut sortConstraints : Array (FirstOrderSort × Nat × Expr) := #[]
  for sort in fostruct.domains do
    for sortSize in [1 : sort.size] do
      let constraint ← sort.cardinalityConstraint sortSize
      let isSat ← constraintIsSatisfiable solver solverName constraint
      match isSat with
      | .some true =>
          sortConstraints := sortConstraints.push (sort, sortSize, constraint.get!)
          break -- break out of the `sortSize in [1 : sort.size]` loop
      | .some false => continue
      | .none => throwError "Sort minimization: unexpected response from solver"
  -- Minimize number of positive elements in each relation
  let mut relConstraints : Array (Declaration × Nat × Expr) := #[]
  for decl in fostruct.signature.declarations do
    for relSize in [1 : ← fostruct.numTrueInstances decl] do
      let constraint ← decl.cardinalityConstraint relSize
      let isSat ← constraintIsSatisfiable solver solverName constraint
      match isSat with
      | .some true =>
          relConstraints := relConstraints.push (decl, relSize, constraint.get!)
          break -- break out of the `relSize in [0 : ← fostruct.numTrueInstances decl]` loop
      | .some false => continue
      | .none => throwError "Relation minimization: unexpected response from solver"
  -- At this point, we are operating on a clean frame. We re-assert all the
  -- satisfied constraints and  `(check-sat)` again to get the minimized model.
  for (s, size, constraint) in sortConstraints do
    trace[sauto.debug] "minimized sort {s} to size {size}"
    addConstraint solver constraint
  for (r, size, constraint) in relConstraints do
    trace[sauto.debug] "minimized relation {r} to size {size}"
    addConstraint solver constraint
  emitCommand solver .checkSat
  let stdout ← Handle.readLineSkip solver.stdout
  trace[sauto.debug] "(check-sat) {stdout.length}: {stdout}"
  let (checkSatResponse, _) ← getSexp stdout
  if checkSatResponse != .atom (.symb "sat") then
    throwError s!"Minimization failed! (check-sat) returned {checkSatResponse}."
  emitCommand solver .getModel
  -- FIXME: it's probably not OK to kill the solver here
  let (_, solver) ← solver.takeStdin
  let stdout ← solver.stdout.readToEnd
  let stderr ← solver.stderr.readToEnd
  solver.kill
  trace[sauto.debug] "(get-model) {stdout.length}: {stdout}"
  trace[sauto.debug] "(stderr) {stderr}"
  let (model, _) ← getSexp stdout
  trace[sauto.debug] "Model:\n{model}"
  let fostruct ← extractStructure model
  return fostruct

open Smt Smt.Tactic Translate in
def querySolver (goalQuery : String) (timeout : Option Nat) (minimize : Bool := true) : MetaM SmtResult := do
  let opts ← getOptions
  let solverName := sauto.smt.solver.get opts
  trace[sauto.debug] "solver: {solverName}"
  let solver ← createSolver solverName timeout
  if solverName == SolverName.cvc5 then
    emitCommand solver (.setLogic "ALL")
    emitCommand solver (.setOption (.produceProofs true))
    emitCommand solver (.setOption (.produceUnsatCores true))
  emitCommandStr solver goalQuery
  if sauto.smt.macrofinder.get opts then
    emitCommandStr solver "(check-sat-using (then macro-finder smt))\n"
  else
    emitCommand solver .checkSat
  let stdout ← Handle.readLineSkip solver.stdout
  trace[sauto.debug] "(check-sat) {stdout.length} {stdout}"
  let (checkSatResponse, _) ← getSexp stdout
  match checkSatResponse with
  | .atom (.symb "sat") =>
      emitCommand solver .getModel
      trace[sauto.result] "{solverName} says Sat"
      let stdout ← Handle.readUntil solver.stdout ")\n"
      let (model, _) ← getSexp stdout
      trace[sauto.debug] "Model:\n{model}"
      -- For Z3, we have model pretty-printing and minimization.
      if solverName == SolverName.z3 then
        let mut fostruct ← extractStructure model
        if minimize then
          fostruct ← minimizeModel solver solverName fostruct
        trace[sauto.result] "{fostruct}"
        return .Sat fostruct
      -- Non-Z3 solver
      else
        trace[sauto.result] "Currently, we print readable interpretations only for Z3. For other solvers, we only return the raw model."
        trace[sauto.result] "Model:\n{model}"
        solver.kill
        return .Sat .none
  | .atom (.symb "unsat") =>
      emitCommand solver .getUnsatCore
      let (_, solver) ← solver.takeStdin
      let stdout ← solver.stdout.readToEnd
      -- let stderr ← solver.stderr.readToEnd
      trace[sauto.result] "{solverName} says Unsat"
      trace[sauto.debug] "{stdout}"
      let (unsatCore, _stdout) ← getSexp stdout
      solver.kill
      trace[sauto.result] "Unsat core: {unsatCore}"
      -- trace[sauto] "Proof:\n{_stdout}"
      -- trace[sauto] "stderr:\n{stderr}"
      return .Unsat unsatCore
  | _ => return .Unknown

-- /-- Our own version of the `smt` & `auto` tactics. -/
syntax (name := sauto) "sauto" smtHints smtTimeout : tactic

@[tactic sauto] def evalSauto : Tactic := fun stx => withMainContext do
  let mv ← Tactic.getMainGoal
  let hs ← Tactic.parseHints ⟨stx[1]⟩
  let timeout ← Tactic.parseTimeout ⟨stx[2]⟩
  let cmdString ← prepareQuery mv hs
  let res ← querySolver cmdString timeout
  match res with
  | .Sat _ => throwError "the goal is false"
  | .Unknown => throwError "the solver returned unknown"
  | .Unsat _ => mv.admit (synthetic := false)

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
  let timeout ← Tactic.parseTimeout ⟨stx[2]⟩
  let cmdString ← prepareQuery mv hs
  let res ← querySolver cmdString timeout
  match res with
  | .Sat _ =>
    trace[sauto.result] "The negation of the goal is satisfiable, hence the goal is valid."
    mv.admit (synthetic := false)
  | .Unsat _ => throwError "the goal is false"
  | .Unknown => throwError "the solver returned unknown"


end Smt
