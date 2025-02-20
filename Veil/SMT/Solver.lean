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

namespace Veil.SMT

open Lean hiding Command Declaration

def emitCommandStr (p : SolverProc) (c : String) : MetaM Unit := do
  trace[veil.smt.query] "{c}"
  p.stdin.putStr c
  p.stdin.flush

def commandStr (c : Auto.IR.SMT.Command) : String := s!"{c}\n"

def emitCommand (p : SolverProc) (c : Auto.IR.SMT.Command) : MetaM Unit := do
  emitCommandStr p (commandStr c)

private def createAux (path : String) (args : Array String) : MetaM SolverProc := do
    trace[veil.smt.debug] "invoking {path} {args}"
    IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped,
                      cmd := path, args := args}

/-- FIXME: this is a hack to get the build directory; how to do this properly? -/
private def buildDir := System.mkFilePath [currentDirectory!] / ".." / ".." / ".lake" / "build"
def z3Path := buildDir / "z3"
def cvc5Path := buildDir / "cvc5"
def uvPath := buildDir / "uv"
def z3ModelPath := System.mkFilePath [currentDirectory!, "z3model.py"]

def createSolver (name : SmtSolver) (withTimeout : Nat) : MetaM SolverProc := do
  let tlim_sec := withTimeout
  let seed := veil.smt.seed.get $ ← getOptions
  match name with
  | .z3   => createAux s!"{z3Path}" #["-in", "-smt2", s!"-t:{tlim_sec * 1000}", s!"sat.random_seed={seed}", s!"smt.random_seed={seed}"]
  | .cvc5 =>
      let args := #["--lang", "smt", s!"--tlimit-per={tlim_sec * 1000}", "--seed", s!"{seed}",
        "--finite-model-find", "--enum-inst-interleave", "--nl-ext-tplanes", "--incremental"]
      let proc ← createAux s!"{cvc5Path}" args
      emitCommand proc (.setLogic "ALL")
      pure proc

inductive ModelGenerator where
  | z3Model

def createModelGenerator (name : ModelGenerator) (withTimeout : Nat) (minimize : Bool) : MetaM SolverProc := do
  let tlim_sec := withTimeout
  let seed := veil.smt.seed.get $ ← getOptions
  match name with
  | .z3Model   =>
    let wrapperDir := currentDirectory!
    let wrapperPath := (System.mkFilePath [wrapperDir, "z3model.py"]).toString
    let mut wrapperArgs := #[s!"--tlimit={tlim_sec * 1000}", s!"--seed", s!"{seed}"]
    if minimize then
      wrapperArgs := wrapperArgs.push "--minimize"
    let uvArgs := #["run", wrapperPath] ++ wrapperArgs
    createAux s!"{uvPath}" uvArgs

def getFOStructure (queryStr : String) (withTimeout : Nat) (minimize : Bool) : MetaM (Option FirstOrderStructure) := do
  try
    let mg ← createModelGenerator .z3Model withTimeout minimize
    emitCommandStr mg queryStr
    let (_, mg) ← mg.takeStdin
    let stdout ← mg.stdout.readToEnd
    let stderr ← mg.stderr.readToEnd
    trace[veil.smt.debug] "stdout: {stdout}"
    trace[veil.smt.debug] "stderr: {stderr}"
    mg.kill
    let (model, _) ← Auto.Solver.SMT.getSexp stdout
    extractStructure model
  catch _ex => pure none

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
  emitCommand solver .checkSat
  let stdout ← solver.stdout.getLine
  trace[veil.smt.debug] "[checkSat] stdout: {stdout}"
  let (checkSatResponse, _) ← Auto.Solver.SMT.getSexp stdout
  match checkSatResponse with
  | .atom (.symb "sat") =>
    trace[veil.smt.result] "{solverName} says Sat"
    emitCommand solver .getModel
    let (_, solver) ← solver.takeStdin
    let stdout ← solver.stdout.readToEnd
    let stderr ← solver.stderr.readToEnd
    trace[veil.smt.debug] "stdout: {stdout}"
    trace[veil.smt.debug] "stderr: {stderr}"
    let (model, _) ← Auto.Solver.SMT.getSexp stdout
    solver.kill
    let queryStr := goalQuery ++ ("\n".intercalate $ [.checkSat, .getModel].map commandStr)
    let fostruct ← getFOStructure queryStr withTimeout minimize
    return SmtResult.Sat s!"{model}" fostruct

  | .atom (.symb "unsat") =>
    trace[veil.smt.result] "{solverName} says Unsat"
    let (_, solver) ← solver.takeStdin
    let stdout ← solver.stdout.readToEnd
    let stderr ← solver.stderr.readToEnd
    trace[veil.smt.debug] "stdout: {stdout}"
    trace[veil.smt.debug] "stderr: {stderr}"
    solver.kill
    return SmtResult.Unsat

  | .atom (.symb "unknown") =>
    trace[veil.smt.result] "{solverName} says Unknown"
      if retryOnUnknown then
        let newSolver := solverToTryOnUnknown solverName
        trace[veil.smt.debug] "Retrying with {newSolver}"
        querySolver goalQuery withTimeout (forceSolver := .some newSolver) (retryOnUnknown := false) getModel? minimize
      else
        let (_, solver) ← solver.takeStdin
        let stdout ← solver.stdout.readToEnd
        let stderr ← solver.stderr.readToEnd
        trace[veil.smt.debug] "stdout: {stdout}"
        trace[veil.smt.debug] "stderr: {stderr}"
        solver.kill
        return SmtResult.Unknown .none

  | _ => throwError s!"Unexpected response from solver: {checkSatResponse}"
  catch e =>
    let exMsg ← e.toMessageData.toString
    return .Failure s!"{exMsg}"

end Veil.SMT
