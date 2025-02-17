import Veil.Base
import Veil.SMT.Translation

partial def Handle.readLineSkip (h : IO.FS.Handle) (skipLine : String := "\n") : IO String := do
  let rec loop := do
    let line ← h.getLine
    if line.isEmpty then
      return line
    if line == skipLine then
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

namespace Veil.SMT

open Lean hiding Command Declaration

def emitCommandStr (p : SolverProc) (c : String) : MetaM Unit := do
  trace[veil.smt.query] "{c}"
  p.stdin.putStr c
  p.stdin.flush

def emitCommand (p : SolverProc) (c : Auto.IR.SMT.Command) : MetaM Unit := do
  emitCommandStr p s!"{c}\n"

def createSolver (name : SmtSolver) (withTimeout : Nat) : MetaM SolverProc := do
  let tlim_sec := withTimeout
  let seed := veil.smt.seed.get $ ← getOptions
  match name with
  | .z3   => createAux "z3" #["-in", "-smt2", s!"-t:{tlim_sec * 1000}", s!"sat.random_seed={seed}", s!"smt.random_seed={seed}"]
  | .cvc5 =>
      let args := #["--lang", "smt", s!"--tlimit-per={tlim_sec * 1000}", "--seed", s!"{seed}",
        "--finite-model-find", "--enum-inst-interleave", "--nl-ext-tplanes", "--incremental"]
      let proc ← createAux "cvc5" args
      emitCommand proc (.setLogic "ALL")
      pure proc
where
  createAux (path : String) (args : Array String) : MetaM SolverProc := do
    trace[veil.smt.debug] "invoking {path} {args}"
    IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped,
                      cmd := path, args := args}

private def throwSmtError (solver : SolverProc) (e : Exception) (msg: String): MetaM α := do
  let exMsg ← e.toMessageData.toString
  let stderr ← solver.stderr.readToEnd
  let stderr := if stderr.isEmpty then "" else s!": \n{stderr}"
  trace[veil.smt.debug] s!"{msg} ({exMsg}) {stderr}"
  throwError s!"{msg} ({exMsg}) {stderr}"

def checkSat (solver : SolverProc) (solverName : SmtSolver) : MetaM SmtResult := do
  withTraceNode `veil.smt.perf.checkSat (fun _ => return "checkSat") do
  try
    emitCommand solver .checkSat
    let stdout ← solver.stdout.getLine
    trace[veil.smt.debug] "[checkSat] stdout: {stdout}"
    let (checkSatResponse, _) ← Auto.Solver.SMT.getSexp stdout
    match checkSatResponse with
    | .atom (.symb "sat") =>
      trace[veil.smt.debug] "{solverName} says Sat"
      return SmtResult.Sat .none .none
    | .atom (.symb "unsat") =>
      trace[veil.smt.debug] "{solverName} says Unsat"
      return SmtResult.Unsat
    | .atom (.symb "unknown") =>
      trace[veil.smt.debug] "{solverName} says Unknown"
      return SmtResult.Unknown .none
    | _ => throwError s!"Unexpected response from solver: {checkSatResponse}"
  catch e => throwSmtError solver e "check-sat failed"

def getModel (solver : SolverProc) : MetaM SExpression := do
  withTraceNode `veil.smt.perf.getModel (fun _ => return "getModel") do
  try
  emitCommand solver .getModel
  let stdout ← Handle.readUntil solver.stdout ")\n"
  let (model, _) ← Auto.Solver.SMT.getSexp stdout
  return model
  catch e => throwSmtError solver e "get-model failed"

/-- Check if the constraint is satisfiable in the current frame. -/
def constraintIsSatisfiable (solver : SolverProc) (solverName : SmtSolver) (constr : Option Expr) : MetaM Bool := do
  match constr with
  | none => return true
  | some expr =>
  addConstraint solver expr
  let res ← checkSat solver solverName
  match res with
  | .Sat _ _ => return true
  | .Unsat => return false
  | .Unknown e => throwError s!"Unexpected unknown from solver: {e}"
  | .Failure e => throwError s!"failure from solver: {e}"
/- FIXME: This only supports goals translated using `lean-smt`. -/
where addConstraint (solver : SolverProc) (expr : Expr) : MetaM Unit := do
  -- prepareSmtQuery negates the expression, so we negate it here.
  let (fvNames₁, _fvNames₂) ← Smt.genUniqueFVarNames
  let cmds ← Smt.prepareSmtQuery [] (mkNot expr) fvNames₁
  -- Do not declare sorts again, etc. Only add constraints (i.e. assertions).
  let cmds := cmds.filter fun
    | .assert _ => true
    | _ => false
  let cmd := Smt.Translate.Command.cmdsAsQuery cmds
  emitCommandStr solver cmd

private def minimizeModelImpl (solver : SolverProc) (solverName : SmtSolver) (fostruct : FirstOrderStructure) (kill: Bool := true) : MetaM FirstOrderStructure := do
  -- Implementation follows the `solver.py:_minimal_model()` function in `mypyvy`
  try
  -- Minimize sorts
  let mut sortConstraints : Array (FirstOrderSort × Nat × Expr) := #[]
  for sort in fostruct.domains do
    for sortSize in [1 : sort.size] do
      let .some constraint ← sort.cardinalityConstraint sortSize
        | trace[veil.smt.debug] "no constraint for sort {sort} at size {sortSize}"; continue
      -- we check each constraint in a separate frame
      emitCommandStr solver s!"(push)"
      let isSat ← constraintIsSatisfiable solver solverName constraint
      match isSat with
      | true =>
          sortConstraints := sortConstraints.push (sort, sortSize, constraint)
          trace[veil.smt.debug] "minimized sort {sort} to size {sortSize}"
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
    trace[veil.smt.debug] "trying to minimize relation {decl.name} at sizes [0 : {currentSize})"
    for relSize in [0 : currentSize] do
      let .some constraint ← decl.cardinalityConstraint relSize
        | trace[veil.smt.debug] "no constraint for relation {decl.name} at size {relSize}"; continue
      -- we check each constraint in a separate frame
      emitCommandStr solver "(push)"
      let isSat ← constraintIsSatisfiable solver solverName constraint
      match isSat with
      | true =>
          relConstraints := relConstraints.push (decl, relSize, constraint)
          trace[veil.smt.debug] "minimized relation {decl.name} to size {relSize}"
          break -- break out of the `relSize in [0 : ← fostruct.numTrueInstances decl]` loop
      | false =>
        -- we end the frame here; since this constraint is unsatisfiable,
        -- we don't want to build on top of it
        emitCommandStr solver "(pop)"
        trace[veil.smt.debug] "relation {decl.name} is unsatisfiable at size {relSize}"
        continue
  let checkSatResponse ← checkSat solver solverName
  let .Sat _ _ := checkSatResponse
    | throwError s!"Minimization failed! (check-sat) returned {checkSatResponse}."
  emitCommand solver .getModel
  -- FIXME: it's probably not OK to kill the solver here
  let (_, solver) ← solver.takeStdin
  let stdout ← solver.stdout.readToEnd
  let stderr ← solver.stderr.readToEnd
  if kill then
    solver.kill
  trace[veil.smt.debug] "(get-model) {stdout.length}: {stdout}"
  trace[veil.smt.debug] "(stderr) {stderr}"
  let (model, _) ← Auto.Solver.SMT.getSexp stdout
  trace[veil.smt.debug] "Model:\n{model}"
  let fostruct ← extractStructure model
  return fostruct
  catch e =>
    let exMsg ← e.toMessageData.toString
    throwError s!"Minimization failed: {exMsg}"

/- FIXME: for whatever reason, if I add `withTraceNode` directly inside `minimizeModelImpl`, it hangs. -/
def minimizeModel (solver : SolverProc) (solverName : SmtSolver) (fostruct : FirstOrderStructure) (kill : Bool := true): MetaM FirstOrderStructure := do
  withTraceNode `veil.smt.perf.minimizeModel (fun _ => return "minimizeModel") do
  minimizeModelImpl solver solverName fostruct kill

partial def getSolverResult (solver: SolverProc) (solverName: SmtSolver) (kill: Bool := true) (getModel? : Bool := true) (minimize : Bool := false) : MetaM SmtResult := do
  let checkSatResponse ← checkSat solver solverName
  match checkSatResponse with
  | .Sat _ _ =>
      trace[veil.smt.result] "{solverName} says Sat"
      match getModel? with
      | false =>
        if kill then
            solver.kill
        return .Sat .none .none
      | true =>
        let model ← getModel solver
        trace[veil.smt.debug] "Model:\n{model}"
        trace[veil.smt.model] "Model:\n{model}"
        if kill then
          solver.kill
        return .Sat s!"{model}" .none
  | .Unsat =>
      trace[veil.smt.result] "{solverName} says Unsat"
      return .Unsat
  | .Unknown reason =>
      trace[veil.smt.result] "{solverName} says Unknown ({reason})"
      if kill then
        solver.kill
      return .Unknown reason
  | .Failure reason => return .Failure reason

open Smt Smt.Tactic Translate in
partial def querySolver (goalQuery : String) (withTimeout : Nat) (forceSolver : Option SmtSolver := none) (retryOnUnknown : Bool := false) (getModel? : Bool := true) (minimize : Option Bool := none) : MetaM SmtResult := do
  withTraceNode `veil.smt.perf.query (fun _ => return "querySolver") do
  try
  let opts ← getOptions
  let minimize := minimize.getD (veil.smt.model.minimize.get opts)
  let solverName :=
    match forceSolver with
    | some s => s
    | none => veil.smt.solver.get opts
  trace[veil.smt.debug] "solver: {solverName}"
  let solver ← createSolver solverName withTimeout
  emitCommandStr solver goalQuery
  let res ← getSolverResult solver solverName (kill := true) getModel? minimize
  let res : SmtResult ← match res with
  | .Unknown _=> do
    if retryOnUnknown then
      let newSolver := solverToTryOnUnknown solverName
      trace[veil.smt.debug] "Retrying with {newSolver}"
      querySolver goalQuery withTimeout (forceSolver := .some newSolver) (retryOnUnknown := false) getModel? minimize
    else
      return res
  | _ => return res
  catch e =>
    let exMsg ← e.toMessageData.toString
    return .Failure s!"{exMsg}"

end Veil.SMT
